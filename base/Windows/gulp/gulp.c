#include "winlean.h"
#include "winsock2.h"
#include <stdlib.h>
#include <stdio.h>

#define DEF_PACKET_SIZE 32 
#define MAX_PACKET 1024 

#define xmalloc(s) HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, (s)) 
#define xfree(p)   HeapFree (GetProcessHeap(), 0, (p)) 

_declspec (thread) void * MC_MyCS_StopEvent;

typedef struct args {
	LPTSTR  host;
	int	port;
} thread_args_t, *pthread_args_t; 

static HANDLE  endThreadEvent; 
static HANDLE  threadCountMutex; 
static int doneThreads; 
static int   numThreads; 
static int  iterationCount; 
static int  g_totalBytesRead; 
//
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
LPSTR MC_GetLastErrorText(LPSTR lpszBuf, DWORD dwSize, DWORD errnum)
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
        //sprintf(lpszBuf, "%s (%d)", lpszTemp, errnum);
        sprintf(lpszBuf, " error %d\n", errnum);
    }

    if (lpszTemp)
        LocalFree((HLOCAL) lpszTemp );

    return lpszBuf;
}


static void MC_ErrMsg(LPSTR buf, DWORD bufsize, LPCSTR msg)
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
            if (WaitForMultipleObjects(2, ourevents, FALSE, 10000) != WAIT_OBJECT_0)
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

static DWORD  Gulp(SOCKET sockfd )
{
    int				totalBytes; 
    int				numPackets; 
    int				bytesRead; 
    char			buffer[4096];

	totalBytes = 0; 
    numPackets = 0; 
	
	do { 
		bytesRead = MC_Recv(sockfd, buffer,  4096);
		if (bytesRead > 0 ) { 
			numPackets++;
			totalBytes += bytesRead; 
		}
	} while (bytesRead > 0) ;
 
	//printf(" Read %d bytes in %d receives\n", totalBytes, numPackets); 
    return totalBytes;
}


static DWORD WINAPI 
MC_DoFetchUrl(LPVOID lpParam)
{
    struct hostent      *hostelement;
    struct sockaddr_in  sock_addr;
    DWORD				tmp;
    int					server_status = 0;
    int					ret_count = 0;
    SOCKET				sockfd; 
	pthread_args_t		args;
	char				retmsg[1024];
	int					size_retmsg; 
	int					i;
	struct linger		lo; 
	int					bytesRead; 

	args = (pthread_args_t) lpParam; 
	size_retmsg = 1024; 

    bytesRead = 0; 
	for (i=0; i < iterationCount; i++)  {

		memset((void *) &sock_addr, '\0', sizeof(sock_addr));
		sock_addr.sin_family = AF_INET;
		sock_addr.sin_port = htons((short) (args->port > 0 ? args->port : 80));

		if ((sockfd = WSASocket(AF_INET, SOCK_STREAM, IPPROTO_TCP, NULL, 0, 0)) == INVALID_SOCKET) {
			MC_ErrMsg(retmsg, size_retmsg, "500 Unable to create socket: ");
			printf(retmsg); 
			//break;
		}

		if ((hostelement = gethostbyname(args->host)) == NULL) {
			tmp = sprintf(retmsg, "Unable to resolve host name '%s':", args->host);
			MC_GetLastErrorText(retmsg + tmp, size_retmsg - tmp, WSAGetLastError());
			printf(retmsg); 
			break;
		}

		memcpy(&sock_addr.sin_addr, hostelement->h_addr, hostelement->h_length);
		tmp = connect(sockfd, (struct sockaddr *) &sock_addr, sizeof(sock_addr));
		if (tmp == SOCKET_ERROR) {
			MC_ErrMsg(retmsg, size_retmsg, "500 Unable to connect to web server: ");
			printf(retmsg); 
			//break;
		}

        lo.l_onoff  = 1;
        lo.l_linger = 0;
		if (setsockopt(sockfd, SOL_SOCKET, SO_LINGER,
			(char *) &lo, sizeof(lo)) < 0) {
			printf("HTDoConnect: Can't set sockopt SO_LINGER (%d)\n", errno);
			break;
		}

		bytesRead += Gulp(sockfd); 
		shutdown(sockfd, SD_BOTH);
		closesocket(sockfd);
	}

	WaitForSingleObject(threadCountMutex,INFINITE);
		g_totalBytesRead += bytesRead; 
		doneThreads++; 
		printf("Thread ending..count=%d\n",doneThreads); 
		SetEvent(endThreadEvent); 
	ReleaseMutex(threadCountMutex); 

    return 1;
}

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

void Usage()
{
    printf(
            "Usage:\n"
            "    gulp [options] \n"
            "Options:\n"
			"    /p:N             -- Port to connect to (default=5000)\n"
			"    /a:nnn.nnn.nnn   -- address to connect to\n"
			"    /i:N             -- number of iterations\n"
            );
}
int main(int argc, char *argv[]) {

	int					arg; 
	pthread_args_t		blee; 
    BOOL				fNeedHelp       = FALSE;
	char				*argn;
	char				*argp;
	char				*address;
	DWORD				dwPort;
	BOOL				bHaveAddress; 
    LARGE_INTEGER		before;
    LARGE_INTEGER		after;
    LARGE_INTEGER		frequency;
	double				elapsed; 
	double				rate; 
	double				MBS; 
	double				mbs; 
	int					i; 
	DWORD				dwThreadId;
	HANDLE				hThread; 

	InitChildLayer(); 

	endThreadEvent = CreateEvent(NULL,FALSE,FALSE,NULL); 
	threadCountMutex = CreateMutex(NULL,FALSE,NULL); 
	doneThreads = 0; 

	if (endThreadEvent == NULL) {
		printf("Unable to allocate event!\n");
		exit(1);
	}

   numThreads = 1; 
   dwPort = 5000; 
   iterationCount = 10; 
   fNeedHelp = FALSE; 
   bHaveAddress = FALSE; 

   for (arg = 1; arg < argc && !fNeedHelp; arg++) {
        if (argv[arg][0] == '-' || argv[arg][0] == '/') {
            argn = argv[arg]+1;                   // Argument name
            argp = argn;                          // Argument parameter

            while (*argp && *argp != ':') {
                argp++;
            }
            if (*argp == ':')
                *argp++ = '\0';

            switch (argn[0]) {

              case '?':                                 // Help
                fNeedHelp = TRUE;
                break;

              case 'a':                                 // address to connect to 
              case 'A':
                address = argp;
				printf("Address = '%s'\n", argp); 
				bHaveAddress = TRUE; 
                break;

              case 'i':                                 // iterations within thread
              case 'I':
                iterationCount = atoi(argp);
                break;

              case 'p':                                 // port to attach to 
              case 'P':
                dwPort = (DWORD)atoi(argp);
                break;

			  case 't':                                 // Number of  threads to start 
              case 'T':
                numThreads = atoi(argp);
                break;

              default:
                printf("Unknown argument: %s\n", argv[arg]);
                fNeedHelp = TRUE;
                break;
            }
        }
        else {
        }
    }

   if (fNeedHelp | !bHaveAddress) {
		Usage();
		exit(1);
   }

    printf ("Connecting to %s on port %d. threads=%d iterations=%d..", address, dwPort, numThreads, iterationCount); 
	blee  = malloc(sizeof(pthread_args_t));  
	blee->host = address;
	blee->port = dwPort; 

#if 1
	for (i=0; i < numThreads; i++) {
		hThread = CreateThread( 
			NULL,                       // default security attributes 
			0,                          // use default stack size  
			MC_DoFetchUrl,				// thread function 
			blee,						// argument to thread function 
			0,                          // use default creation flags 
			&dwThreadId);               // returns the thread identifier 
	}
	//for (i=0; i < numThreads; i++) {
    QueryPerformanceFrequency(&frequency);
    QueryPerformanceCounter(&before);
	while(doneThreads !=  numThreads ) {
		WaitForSingleObject(endThreadEvent,INFINITE); 
		printf ("received %d of %d events, done=%d\n", i+1, numThreads, doneThreads);
	}
    QueryPerformanceCounter(&after);
    after.QuadPart -= before.QuadPart;
    elapsed = (double)after.QuadPart / (double)frequency.QuadPart;
	rate = (double) g_totalBytesRead / elapsed; 
	printf("bytes read =%d, time elapsed = %10.3f seconds rate = %10.3f \n", g_totalBytesRead, elapsed, rate); 
	MBS =  rate / (double) (1024 *1024); 
	mbs =  MBS * 8; 
	printf("MB/s = %10.3f, mb/s = %10.3f\n", MBS, mbs); 
#else
	MC_DoFetchUrl(blee); 
#endif 
	WSACleanup( );

}


