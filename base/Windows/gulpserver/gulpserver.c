#include "winlean.h"
#include "winsock2.h"
#include <stdlib.h>
#include <stdio.h>

#define DEF_PACKET_SIZE 32
#define MAX_PACKET 1024

#define xmalloc(s) HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, (s))
#define xfree(p)   HeapFree (GetProcessHeap(), 0, (p))
//
// This event is set when a control socket is closed before the end of a test.
// If the user kills the manager script then its end of the control socket will
// be closed.  We catch that and use this event to notify any worker threads
// associated with that control socket to stop what they're doing.
// 
_declspec (thread) void * MC_MyCS_StopEvent;

// print an error message and exit the program   
void die (char *format,...) {
    va_list args;
    char buffer[2048], *ptr=buffer;

    va_start(args,format);
    ptr += vsprintf (ptr, format, args);
    va_end (args);
    *(ptr++) = '\n';
    *(ptr++) = '\0';

    printf( buffer);

    exit(1);
}
int InitChildLayer(void) {
    WORD wVersionRequested;
    WSADATA wsaData;
    int err;
    int major, minor;

    wVersionRequested = MAKEWORD( 2, 0 );

    err = WSAStartup( wVersionRequested, &wsaData );
    if ( err != 0 ) {
    // Tell the user that we couldn't find a useable   
    // WinSock DLL.                                    
    die ("Couldn't find a WinSock DLL!\n");
    }

    // Confirm that the WinSock DLL supports 2.0.          
    // Note that if the DLL supports versions greater      
    // than 2.0 in addition to 2.0, it will still return   
    // 2.0 in wVersion since that is the version we        
    // requested.                                          

    major = LOBYTE( wsaData.wVersion );
    minor = LOBYTE( wsaData.wVersion );

    if ( major < 1 || ( major == 1 && minor < 1 ) ) {
    // Tell the user that we couldn't find a useable   
    // WinSock DLL.                                    
    WSACleanup( );
    die ("Require at least WinSock 1.1, your version is %d.%d!\n",
         major, minor);
    }
    return 0;
}
static USHORT
checksum(USHORT *buffer, int size)
{
    unsigned long cksum=0;

    while(size > 1)
    {
        cksum += *buffer++;
        size -= sizeof(USHORT);
    }

    if (size)
        cksum += *(UCHAR*)buffer; // if there's an odd number of bytes   

    cksum = (cksum >> 16) + (cksum & 0xffff);
    cksum += (cksum >> 16);
    return (USHORT)(~cksum);
}


//
// MC_GetLastErrorText
//
//  PURPOSE: copies error message text to string
//
//  PARAMETERS:
//    lpszBuf - destination buffer
//    dwSize - size of buffer
//
//  RETURN VALUE:
//    destination buffer
// 
LPSTR
MC_GetLastErrorText(LPSTR lpszBuf, DWORD dwSize, DWORD errnum)
{
    DWORD dwRet;
    LPTSTR lpszTemp = NULL;

    dwRet = FormatMessage( FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM |FORMAT_MESSAGE_ARGUMENT_ARRAY,
                           NULL,
                           errnum,
                           LANG_NEUTRAL,
                           (LPTSTR)&lpszTemp,
                           0,
                           NULL );

    if ( !dwRet)
        sprintf(lpszBuf, "error number %d", errnum); // no message so use errnum   
    else
    {
        lpszTemp[lstrlen(lpszTemp)-2] = '\0';  // remove cr and newline characters   
        sprintf(lpszBuf, "%s (0x%x)", lpszTemp, errnum);
    }

    if (lpszTemp)
        LocalFree((HLOCAL) lpszTemp );

    return lpszBuf;
}


static void
MC_ErrMsg(LPSTR buf, DWORD bufsize, LPCSTR msg)
{
     DWORD tmp;

     tmp = strlen(strcpy(buf, msg));
     MC_GetLastErrorText(buf + tmp, bufsize - tmp, WSAGetLastError());
}

//
//  FUNCTION: MC_Recv
//
//  PURPOSE: A replacement for the Winsock recv() routine.  This version uses
//           overlapped I/O to look for data on a socket and also watch
//           for the Stop event.
//
//  PARAMETERS:
//    sock - read from this socket.
//    buffer - place incoming data into this buffer.
//    nbytes - the amount of storage in the buffer.
//
//  RETURN VALUE:
//    -1 - error.
//    0  - the socket connection has been closed.
//    >0 - the number of bytes read.
// 
int
MC_Recv(SOCKET sock, char *buffer, int nbytes)
{
    DWORD          bytesreceived;
    DWORD          flags = 0;
    WSAOVERLAPPED  ov;
    WSABUF         wsabuffer[1];
    HANDLE         ourevents[2];

    ov.hEvent = NULL;
    ov.Offset = ov.OffsetHigh = 0;
    wsabuffer[0].buf = buffer;
    wsabuffer[0].len = nbytes;

    while(1)
    {
        if (WSARecv(sock, wsabuffer, 1, &bytesreceived, &flags, &ov, NULL) == SOCKET_ERROR)
        {
            switch (WSAGetLastError())
            {
            case WSAEWOULDBLOCK: continue;  // try again   
            case WSAENETRESET:
            case WSAECONNRESET:
            case WSAEDISCON:     return 0;  // connection closed   
            //case WSA_IO_PENDING: break;     /* okay */
            default:             return -1; // unexpected error   
            }
            ourevents[0] = (HANDLE) sock;
            ourevents[1] = MC_MyCS_StopEvent;
            if (WaitForMultipleObjects(2, ourevents, FALSE, INFINITE) != WAIT_OBJECT_0)
            {
                printf("MC_Recv(): Stop event or WaitForMultipleObjects() error\n");
                return -1; // Stop event or error   
            }
            else if (!WSAGetOverlappedResult(sock, &ov, &bytesreceived, FALSE, &flags))
                return -1; // error   
        }
        return bytesreceived; // if we got here its due to a successful read   
    }
}

static DWORD  WINAPI Gulp(LPVOID lpParam )
{
    int         totalBytes;
    int         numPackets;
    int         bytesRead;
    char        buffer[4096];
    SOCKET      sockfd;

    INT64 startCounter, endCounter, frequency;

    totalBytes = 0;
    numPackets = 0;
    sockfd = *(SOCKET *) lpParam;

    QueryPerformanceCounter((PLARGE_INTEGER)&startCounter);
    do {
        bytesRead = MC_Recv(sockfd, buffer,  4096);
        if (bytesRead > 0 ) {
            numPackets++;
            totalBytes += bytesRead;
        }
    } while (bytesRead > 0) ;
    QueryPerformanceCounter((PLARGE_INTEGER)&endCounter);
    QueryPerformanceFrequency((PLARGE_INTEGER)&frequency);

    printf(" Read %d bytes / %d KB / %d MB in %d receives\n",
           totalBytes, totalBytes / 1024, totalBytes / 1048576, numPackets);

    if (endCounter != startCounter) {
        double tau = (double)(endCounter - startCounter) / (double)frequency;
        double bps = totalBytes * 8.0 / tau;

        printf("Transferred in %.3e seconds => %.3e bps\n",
               tau, bps);
    }
    else {
        printf("Transfer too quick to measure with this clock\n");
    }

    return 1;
}

static DWORD listener (int port, LPSTR retmsg, DWORD size_retmsg)
{
    struct sockaddr_in  sock_addr;
    DWORD       tmp;
    int         server_status = 0;
    int         ret_count = 0;
    SOCKET      listenSockfd;
    SOCKET      sockfd;
    HANDLE      hThread;
    DWORD       dwThreadId;


    memset((void *) &sock_addr, '\0', sizeof(sock_addr));
    sock_addr.sin_family = AF_INET;
    sock_addr.sin_addr.S_un.S_addr = INADDR_ANY;
    sock_addr.sin_port = htons((short) (port > 0 ? port : 80));

    if ((listenSockfd = WSASocket(AF_INET, SOCK_STREAM, IPPROTO_TCP, NULL, 0, 0)) == INVALID_SOCKET)
    {
        MC_ErrMsg(retmsg, size_retmsg, "500 Unable to create socket: ");
        printf(retmsg);
        return -1;
    }
    if ((listenSockfd = WSASocket(AF_INET, SOCK_STREAM, IPPROTO_TCP, NULL, 0, 0)) == INVALID_SOCKET)
    {
        MC_ErrMsg(retmsg, size_retmsg, "500 Unable to create socket: ");
        printf(retmsg);
        return -1;
    }

    tmp = bind(listenSockfd, (struct sockaddr *) &sock_addr, sizeof(sock_addr));
    if (tmp == SOCKET_ERROR)
    {
        MC_ErrMsg(retmsg, size_retmsg, "500 Unable to bind to socket: ");
        printf(retmsg);
        return -1;
    }

    tmp = listen( listenSockfd,10);
    if (tmp == SOCKET_ERROR)
    {
        MC_ErrMsg(retmsg, size_retmsg, "500 Unable to listen on socket: ");
        printf(retmsg);
        return -1;
    }
    do {
        printf("\n listening\n");
        sockfd  = accept(listenSockfd,0,0);
        if (sockfd == SOCKET_ERROR)
        {
            MC_ErrMsg(retmsg, size_retmsg, "500 Unable to accept on socket: ");
            printf(retmsg);
            return -1;
        }
        printf(" ...Accepted connection\n");

        hThread = CreateThread(
            NULL,                        // default security attributes
            0,                           // use default stack size
            Gulp,                        // thread function
            &sockfd,                // argument to thread function
            0,                           // use default creation flags
            &dwThreadId);                // returns the thread identifier

    // Check the return value for success.

    if (hThread == NULL)
    {
        printf("CreateThread failed." );
    }
    else
    {
        CloseHandle( hThread );
    }

    } while (TRUE);
}




int main(int argc, char *argv[]) {

    char retmsg[1024];
    int foo;

    if (argc < 2 ) {
        printf("gulpserver port\n");
        printf("    listens on port for TCP blast client \n");
        return -1;
    }
    foo = atoi(argv[1]);
    InitChildLayer();
    printf (" Listening on port %d ...",foo);
    listener(foo, retmsg, 1024);
    WSACleanup( );

}


