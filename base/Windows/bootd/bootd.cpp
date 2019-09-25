////////////////////////////////////////////////////////////////////////////
//
// Boot Service
//
// Copyright Microsoft Corporation
//
#include <winlean.h>
#include <winsock.h>
#include <stdio.h>
#include <assert.h>
#include <iphlpapi.h>

#include "socksr.h"
#include "hashtab.h"
#include "dhcpd.h"
#include "tftpd.h"

#define ARRAYOF(x)      (sizeof(x)/sizeof(x[0]))
#define ASSERT(a)       assert(a)

#define WM_SOCKET_EVENT  (WM_USER+101)

void SocketErrorBox(DWORD dwWSALastError, PCSTR pszFile, INT nLine)
{
    CHAR *szError = NULL;

    switch (dwWSALastError) {
      case WSAEACCES:
        szError = "WSAEACCES (%d) Permission denied.";
        break;
      case WSAEADDRINUSE:
        szError = "WSAEADDRINUSE (%d) Address already in use.";
        break;
      case WSAEADDRNOTAVAIL:
        szError = "WSAEADDRNOTAVAIL (%d) Cannot assign requested address.";
        break;
      case WSAEAFNOSUPPORT:
        szError = "WSAEAFNOSUPPORT (%d) Address family not supported by protocol family.";
        break;
      case WSAEALREADY:
        szError = "WSAEALREADY (%d) Operation already in progress.";
        break;
      case WSAECONNABORTED:
        szError = "WSAECONNABORTED (%d) Software caused connection abort.";
        break;
      case WSAECONNREFUSED:
        szError = "WSAECONNREFUSED (%d) Connection refused.";
        break;
      case WSAECONNRESET:
        szError = "WSAECONNRESET (%d) Connection reset by peer.";
        break;
      case WSAEDESTADDRREQ:
        szError = "WSAEDESTADDRREQ (%d) Destination address required.";
        break;
      case WSAEFAULT:
        szError = "WSAEFAULT (%d) Bad address.";
        break;
      case WSAEHOSTDOWN:
        szError = "WSAEHOSTDOWN (%d) Host is down.";
        break;
      case WSAEHOSTUNREACH:
        szError = "WSAEHOSTUNREACH (%d) No route to host.";
        break;
      case WSAEINPROGRESS:
        szError = "WSAEINPROGRESS (%d) Operation now in progress.";
        break;
      case WSAEINTR:
        szError = "WSAEINTR (%d) Interrupted function call.";
        break;
      case WSAEINVAL:
        szError = "WSAEINVAL (%d) Invalid argument.";
        break;
      case WSAEISCONN:
        szError = "WSAEISCONN (%d) Socket is already connected.";
        break;
      case WSAEMFILE:
        szError = "WSAEMFILE (%d) Too many open files.";
        break;
      case WSAEMSGSIZE:
        szError = "WSAEMSGSIZE (%d) Message too long.";
        break;
      case WSAENETDOWN:
        szError = "WSAENETDOWN (%d) Network is down.";
        break;
      case WSAENETRESET:
        szError = "WSAENETRESET (%d) Network dropped connection on reset.";
        break;
      case WSAENETUNREACH:
        szError = "WSAENETUNREACH (%d) Network is unreachable.";
        break;
      case WSAENOBUFS:
        szError = "WSAENOBUFS (%d) No buffer space available.";
        break;
      case WSAENOPROTOOPT:
        szError = "WSAENOPROTOOPT (%d) Bad protocol option.";
        break;
      case WSAENOTCONN:
        szError = "WSAENOTCONN (%d) Socket is not connected.";
        break;
      case WSAENOTSOCK:
        szError = "WSAENOTSOCK (%d) Socket operation on nonsocket.";
        break;
      case WSAEOPNOTSUPP:
        szError = "WSAEOPNOTSUPP (%d) Operation not supported.";
        break;
      case WSAEPFNOSUPPORT:
        szError = "WSAEPFNOSUPPORT (%d) Protocol family not supported.";
        break;
      case WSAEPROCLIM:
        szError = "WSAEPROCLIM (%d) Too many processes.";
        break;
      case WSAEPROTONOSUPPORT:
        szError = "WSAEPROTONOSUPPORT (%d) Protocol not supported.";
        break;
      case WSAEPROTOTYPE:
        szError = "WSAEPROTOTYPE (%d) Protocol wrong type for socket.";
        break;
      case WSAESHUTDOWN:
        szError = "WSAESHUTDOWN (%d) Cannot send after socket shutdown.";
        break;
      case WSAESOCKTNOSUPPORT:
        szError = "WSAESOCKTNOSUPPORT (%d) Socket type not supported.";
        break;
      case WSAETIMEDOUT:
        szError = "WSAETIMEDOUT (%d) Connection timed out.";
        break;
      case WSATYPE_NOT_FOUND:
        szError = "WSATYPE_NOT_FOUND (%d) Class type not found.";
        break;
      case WSAEWOULDBLOCK:
        szError = "WSAEWOULDBLOCK (%d) Resource temporarily unavailable.";
        break;
      case WSAHOST_NOT_FOUND:
        szError = "WSAHOST_NOT_FOUND (%d) Host not found.";
        break;
      case WSANOTINITIALISED:
        szError = "WSANOTINITIALISED (%d) Successful WSAStartup not yet performed.";
        break;
      case WSANO_DATA:
        szError = "WSANO_DATA (%d) Valid name, no data record of requested type.";
        break;
      case WSANO_RECOVERY:
        szError = "WSANO_RECOVERY (%d) This is a nonrecoverable error.";
        break;
      case WSASYSCALLFAILURE:
        szError = "WSASYSCALLFAILURE (%d) System call failure.";
        break;
      case WSASYSNOTREADY:
        szError = "WSASYSNOTREADY (%d) Network subsystem is unavailable.";
        break;
      case WSATRY_AGAIN:
        szError = "WSATRY_AGAIN (%d) Nonauthoritative host not found.";
        break;
      case WSAVERNOTSUPPORTED:
        szError = "WSAVERNOTSUPPORTED (%d) Winsock.";
        break;
      case WSAEDISCON:
        szError = "WSAEDISCON (%d) Graceful shutdown in progress.\nReturned by WS";
        break;
      default:
        szError = "UNKNOWN WSA Socket ERROR! (%d)";
        break;
    }

    printf("%s, Line %d.\n", pszFile, nLine);
    printf(szError, dwWSALastError);
    printf("\n");
}

//////////////////////////////////////////////////////////////////////////////
//
static inline INT Max(INT a, INT b)
{
    return a >= b ? a : b;
}

static inline INT Min(INT a, INT b)
{
    return a <= b ? a : b;
}

CHAR * StringDuplicate(PCSTR psz)
{
    int n = strlen(psz);
    CHAR *pszNew = new CHAR [n + 1];
    if (pszNew)
    {
        memcpy(pszNew, psz, n + 1);
    }
    assert(pszNew);
    return pszNew;
}

UINT32 GetIpAddr(PCSTR pszAddr)
{
    if (pszAddr[0] >= '0' && pszAddr[0] <= '9')
    {
        return ntohl(inet_addr(pszAddr));
    }
    else
    {
        HOSTENT *pHost = gethostbyname(pszAddr);
        if (pHost)
        {
            return *(UINT32*)pHost->h_addr_list[0];
        }
    }
    return 0;
}

PCSTR FileTimeToString(UINT64 ftTime)
{
    static CHAR rszTimes[16][48];
    static int nTimes = 0;

    static BOOL bGotTzi = FALSE;
    static DWORD dwTzi = TIME_ZONE_ID_UNKNOWN;
    static TIME_ZONE_INFORMATION tzi;
    if (!bGotTzi)
    {
        dwTzi = GetTimeZoneInformation(&tzi);
        if (dwTzi == TIME_ZONE_ID_UNKNOWN)
        {
            ZeroMemory(&tzi, sizeof(tzi));
        }
        bGotTzi = TRUE;
    }
    SYSTEMTIME stUtc;
    SYSTEMTIME stLocal;

    CHAR *pszTime = rszTimes[nTimes];
    nTimes = (nTimes + 1) % ARRAYOF(rszTimes);

    if (!FileTimeToSystemTime((LPFILETIME)&ftTime, &stUtc))
    {
        strcpy(pszTime, "00:00:00");
        return pszTime;
    }
    else if (!SystemTimeToTzSpecificLocalTime(&tzi, &stUtc, &stLocal))
    {
        CopyMemory(&stLocal, &stUtc, sizeof(stLocal));
    }
    sprintf(pszTime, "%2d:%02d:%02d",
            // stLocal.wYear,
            // stLocal.wMonth,
            // stLocal.wDay,
            stLocal.wHour,
            stLocal.wMinute,
            stLocal.wSecond
            // stLocal.wMilliseconds / 10
           );
    return pszTime;
}

VOID OnNodeMessage(UINT32 nAddr, PCSTR pszProt, PCSTR pszMessage, va_list args)
{
    UINT64 ft;
    GetSystemTimeAsFileTime((LPFILETIME)&ft);

    CHAR szBuffer[2048];
    PCHAR pszBuffer = szBuffer;

    pszBuffer += sprintf(pszBuffer, "%s: ", pszProt);
    pszBuffer += vsprintf(pszBuffer, pszMessage, args);

    if (nAddr == 0) {
        printf("%-8.8s %15.15s %s\n", FileTimeToString(ft), "", szBuffer);
    }
    else {
        printf("%-8.8s %15.15s %s\n", FileTimeToString(ft), SocketToString(nAddr), szBuffer);
    }
    fflush(stdout);
}

VOID OnNodeMessagef(UINT32 nAddr, PCSTR pszProt, PCSTR pszMessage, ...)
{
    va_list args;

    va_start(args, pszMessage);
    OnNodeMessage(nAddr, pszProt, pszMessage, args);
    va_end(args);
}

/////////////////////////////////////////////////////////////////// IDhcpSink.
//
class CDhcpSink : public IDhcpSink
{
  public:
    VOID OnDhcpMessage(UINT32 nAddr, PCSTR pszMessage, ...)
    {
        va_list args;

        va_start(args, pszMessage);
        OnNodeMessage(nAddr, "DHCP", pszMessage, args);
        va_end(args);
    }

    VOID OnDhcpSocketError(INT nErr)
    {
        OnNodeMessagef(0, "DHCP", "Socket Error: %d", nErr);
    }

    VOID OnDhcpOffer(UINT32 nAddr, UINT64 idMac)
    {
        OnNodeMessagef(nAddr, "DHCP", "Offer %s to %02x-%02x-%02x-%02x-%02x-%02x",
                       SocketToString(nAddr),
                       ((PBYTE)&idMac)[5],
                       ((PBYTE)&idMac)[4],
                       ((PBYTE)&idMac)[3],
                       ((PBYTE)&idMac)[2],
                       ((PBYTE)&idMac)[1],
                       ((PBYTE)&idMac)[0]);
    }

    VOID OnDhcpAck(UINT32 nAddr, UINT64 idMac)
    {
        OnNodeMessagef(nAddr, "DHCP", "Assigned %s to %02x-%02x-%02x-%02x-%02x-%02x",
                       SocketToString(nAddr),
                       ((PBYTE)&idMac)[5],
                       ((PBYTE)&idMac)[4],
                       ((PBYTE)&idMac)[3],
                       ((PBYTE)&idMac)[2],
                       ((PBYTE)&idMac)[1],
                       ((PBYTE)&idMac)[0]);
    }
};

class CPxepSink : public IDhcpSink
{
  public:
    VOID OnDhcpMessage(UINT32 nAddr, PCSTR pszMessage, ...)
    {
        va_list args;

        va_start(args, pszMessage);
        OnNodeMessage(nAddr, "PXE ", pszMessage, args);
        va_end(args);
    }

    VOID OnDhcpSocketError(INT nErr)
    {
        OnNodeMessagef(0, "PXE ", "Socket Error: %d", nErr);
    }

    VOID OnDhcpOffer(UINT32 nAddr, UINT64 idMac)
    {
        OnNodeMessagef(nAddr, "PXE ", "Offer boot to %02x-%02x-%02x-%02x-%02x-%02x",
                       ((PBYTE)&idMac)[5],
                       ((PBYTE)&idMac)[4],
                       ((PBYTE)&idMac)[3],
                       ((PBYTE)&idMac)[2],
                       ((PBYTE)&idMac)[1],
                       ((PBYTE)&idMac)[0]);
    }

    VOID OnDhcpAck(UINT32 nAddr, UINT64 idMac)
    {
        OnNodeMessagef(nAddr, "PXE ", "Assigned boot to %02x-%02x-%02x-%02x-%02x-%02x",
                       ((PBYTE)&idMac)[5],
                       ((PBYTE)&idMac)[4],
                       ((PBYTE)&idMac)[3],
                       ((PBYTE)&idMac)[2],
                       ((PBYTE)&idMac)[1],
                       ((PBYTE)&idMac)[0]);
    }
};

/////////////////////////////////////////////////////////////////// ITftpSink.
//
class CTftpSink : public ITftpSink
{
    VOID OnTftpMessage(UINT32 nAddr, PCSTR pszMessage, ...)
    {
        va_list args;

        va_start(args, pszMessage);
        OnNodeMessage(nAddr, "TFTP", pszMessage, args);
        va_end(args);
    }

    VOID OnTftpSocketError(INT nErr)
    {
        OnNodeMessagef(0, "TFTP", "Socket Error: %d", nErr);
    }

    VOID OnTftpAccessBegin(UINT32 nAddr, UINT16 nPort, BOOL fWrite, PCSTR pszFile)
    {
        (void)nPort;

        if (fWrite) {
            OnNodeMessagef(nAddr, "TFTP", "Put %s", pszFile);
        }
        else {
            OnNodeMessagef(nAddr, "TFTP", "Get %s", pszFile);
        }
    }

    VOID OnTftpAccessEnd(UINT32 nAddr, UINT16 nPort, BOOL bSuccess)
    {
        (void)nPort;

        if (bSuccess)
        {
            OnNodeMessagef(nAddr, "TFTP", "Operation finished.");
        }
        else
        {
            OnNodeMessagef(nAddr, "TFTP", "Operation terminated.");
        }
    }
};

VOID Usage(VOID)
{
    printf("Usage:\n"
           "    bootd.exe [options]\n"
           "Options:\n"
           "    /? or /h  - Print this help text.\n"
           "    /u        - Unbuffered output (default line buffered).\n"
           "    /dhcp ... - Set DHCP Daemon Options.\n"
           "        /b:bootimg - Default boot image.\n"
           "        /c:command - Set command line in PXE packet.\n"
           "        /i:inifile - Path name of dhcpd.ini\n"
           "        /m:xx-xx-xx-xx-xx-xx - PXE boot MAC.\n"
           "        /m:xx-xx-xx-xx-xx-xx,i.i.i.i - DCHP & PXE boot MAC.\n"
           "    /tftp ... - Set TFTP Daemon Options\n"
           "        /e - Exit on first attempt to read an invalid file.\n"
           "        /r - Disable rename of *.x86 files to pxe.com.N.\n"
           "        /v - Verbose output.\n"
           "        /w:directory - Allow writes to the specified directory.\n"
           "        {directories} - Directories to serve read only.\n"
          );
}

//////////////////////////////////////////////////////////////////////////////
//
static HWND s_hWndMain;

BOOL TimerSet(ITimerSink *pTimerSink, UINT nMilliseconds)
{
    if (!::SetTimer(s_hWndMain, (UINT_PTR)pTimerSink, nMilliseconds, NULL)) {
        return FALSE;
    }
    return TRUE;
}

BOOL TimerClr(ITimerSink *pTimerSink)
{
    return ::KillTimer(s_hWndMain, (UINT_PTR)pTimerSink);
}

int main(int argc, char **argv)
{
    INT nResult = 0;
    CDhcpSink dhcpSink;
    CPxepSink pxepSink;
    CTftpSink tftpSink;

    CDhcpState *m_pDhcpState = NULL;
    CDhcp * m_pDhcpRaw = NULL;
    CDhcp * m_pDhcpPxe = NULL;
    CTftp * m_pTftp = NULL;

    PCHAR rpszAppsArgs[128];
    PCHAR rpszDhcpArgs[128];
    PCHAR rpszTftpArgs[128];
    INT nAppsArgs = 0;
    INT nDhcpArgs = 0;
    INT nTftpArgs = 0;

    // Initialize Winsock, AFTER the window is created above.
    WSADATA WSAData;
    int iRes = WSAStartup(MAKEWORD(1,1), &WSAData);
    if (0 != iRes) {
        printf("WSAStartup failed.\n");
        return 1;
    }

    enum {
        APPS = 0,
        DHCP = 1,
        TFTP = 2,
    } whose = APPS;

    if (argc == 1) {
        Usage();
        return 0;
    }

    for (int arg = 1; arg < argc; arg++) {

        if (_stricmp(argv[arg], "/apps") == 0 || _stricmp(argv[arg], "-apps") == 0)
        {
            whose = APPS;
        }
        else if (_stricmp(argv[arg], "/dhcp") == 0 || _stricmp(argv[arg], "-dhcp") == 0)
        {
            whose = DHCP;
        }
        else if (_stricmp(argv[arg], "/tftp") == 0 || _stricmp(argv[arg], "-tftp") == 0)
        {
            whose = TFTP;
        }
        else
        {
            switch (whose)
            {
              case APPS:
                rpszAppsArgs[nAppsArgs++] = argv[arg];
                break;
              case DHCP:
                rpszDhcpArgs[nDhcpArgs++] = argv[arg];
                break;
              case TFTP:
                rpszTftpArgs[nTftpArgs++] = argv[arg];
                break;
            }
        }
    }

    rpszAppsArgs[nAppsArgs] = NULL;
    rpszDhcpArgs[nDhcpArgs] = NULL;
    rpszTftpArgs[nTftpArgs] = NULL;

    BOOL fNeedHelp = FALSE;
    BOOL fUnbufferedOutput = FALSE;

    for (INT arg = 0; arg < nAppsArgs; arg++)
    {
        if (rpszAppsArgs[arg][0] == '-' || rpszAppsArgs[arg][0] == '/')
        {
            char *argn = rpszAppsArgs[arg]+1;                   // Argument name
            char *argp = argn;                          // Argument parameter

            while (*argp && *argp != ':')
            {
                argp++;
            }
            if (*argp == ':')
            {
                *argp++ = '\0';
            }

            switch (argn[0])
            {
              case 'h':                                 // Help
              case 'H':
              case '?':
                fNeedHelp = TRUE;
                break;

              case 'u':
              case 'U':
                fUnbufferedOutput = TRUE;
                break;

              default:
                printf("Unknown argument: %s\n", rpszAppsArgs[arg]);
                fNeedHelp = TRUE;
                break;
            }
        }
        else
        {
            printf("Unknown argument: %s\n", rpszAppsArgs[arg]);
            fNeedHelp = TRUE;
        }
    }

    if (fNeedHelp) {
        Usage();
        return 1;
    }

    if (fUnbufferedOutput && setvbuf(stdout, NULL, _IONBF, 0) != 0) {
        printf("Failed to set non-buffered output.");
    }

    // Create a message window.
    //
    WNDCLASS wc;
    ZeroMemory(&wc, sizeof(wc));

    wc.lpfnWndProc   = DefWindowProc;   // Function to retrieve messages for    
    wc.lpszClassName = "bootd";  // Name used in call to CreateWindow.   

    ATOM atomClass = RegisterClass(&wc);
    assert(atomClass);

    s_hWndMain = CreateWindow("bootd", NULL, 0, 0, 0, 0, 0, NULL, NULL, NULL, NULL);
    assert(s_hWndMain);

    SocketInit(s_hWndMain, WM_SOCKET_EVENT);

    UINT nError;

    CTftp::ConfigureFiles(&tftpSink, nTftpArgs, rpszTftpArgs);

    m_pDhcpState = new CDhcpState();
    assert(m_pDhcpState);
    m_pDhcpState->Configure(&dhcpSink, nDhcpArgs, rpszDhcpArgs);
    printf("\n");

    TimerSet(NULL, 10000);

    ////////////////////////////////////////////////////////// Process Events.
    //
    MSG msg;
    BOOL fScanNetwork = TRUE;

    for (;;) {
        if (fScanNetwork) {
            fScanNetwork = FALSE;

            CNetwork *pNetworks = NULL;
            SocketLoadNetworks(&pNetworks);

            for (; pNetworks != NULL; pNetworks = pNetworks->pNext) {
                if (pNetworks->fChanged) {
                    OnNodeMessagef(pNetworks->nAddr, "::::", "Changed");
                    if (m_pDhcpRaw) {
                        m_pDhcpRaw->OnNetworkChange(pNetworks->nAddr,
                                                    pNetworks->nMask,
                                                    pNetworks->nGate);
                    }
                    if (m_pTftp) {
                        m_pTftp->OnNetworkChange(pNetworks->nAddr,
                                                 pNetworks->nMask,
                                                 pNetworks->nGate);
                    }
                    if (m_pDhcpPxe) {
                        m_pDhcpPxe->OnNetworkChange(pNetworks->nAddr,
                                                    pNetworks->nMask,
                                                    pNetworks->nGate);
                    }
                    printf("\n");
                    continue;
                }
                else if (pNetworks->fDeleted) {
                    OnNodeMessagef(pNetworks->nAddr, "::::", "Deleted");
                    if (m_pDhcpRaw) {
                        m_pDhcpRaw->OnNetworkDelete(pNetworks->nAddr, &m_pDhcpRaw);
                    }
                    if (m_pTftp) {
                        m_pTftp->OnNetworkDelete(pNetworks->nAddr, &m_pTftp);
                    }
                    if (m_pDhcpPxe) {
                        m_pDhcpPxe->OnNetworkDelete(pNetworks->nAddr, &m_pDhcpPxe);
                    }
                    printf("\n");
                    continue;
                }
                else if (!pNetworks->fCreated) {
                    continue;
                }

                OnNodeMessagef(pNetworks->nAddr, "::::", "Mask: %s, Gate: %s",
                               SocketToString(pNetworks->nMask),
                               SocketToString(pNetworks->nGate));

                m_pDhcpRaw = new CDhcp(m_pDhcpRaw);
                assert(m_pDhcpRaw);
                m_pDhcpRaw->Configure(pNetworks->nAddr,
                                      pNetworks->nMask,
                                      pNetworks->nGate,
                                      m_pDhcpState, &dhcpSink, DHCP_SERVER_PORT);
                nError = SocketCreate(pNetworks->nAddr, DHCP_SERVER_PORT, m_pDhcpRaw);
                if (nError != 0)
                {
                    SocketErrorBox(nError, __FILE__, __LINE__);
                    nResult = 1;
                    goto abort;
                }

                m_pTftp = new CTftp(m_pTftp);
                assert(m_pTftp);
                m_pTftp->Configure(pNetworks->nAddr, TFTP_PORT,
                                   &tftpSink, nTftpArgs, rpszTftpArgs);
                nError = SessionFactoryCreate(pNetworks->nAddr, TFTP_PORT, m_pTftp);
                if (nError != 0)
                {
                    SocketErrorBox(nError, __FILE__, __LINE__);
                    nResult = 3;
                    goto abort;
                }

                m_pDhcpPxe = new CDhcp(m_pDhcpPxe);
                assert(m_pDhcpPxe);
                m_pDhcpPxe->Configure(pNetworks->nAddr,
                                      pNetworks->nMask,
                                      pNetworks->nGate,
                                      m_pDhcpState, &pxepSink, PXE_SERVER_PORT);
                nError = SocketCreate(pNetworks->nAddr, PXE_SERVER_PORT, m_pDhcpPxe);
                if (nError != 0)
                {
                    SocketErrorBox(nError, __FILE__, __LINE__);
                    nResult = 4;
                    goto abort;
                }

                printf("\n");
            }
        }

        DWORD what = MsgWaitForMultipleObjectsEx(0, NULL, INFINITE, QS_ALLEVENTS,
                                                 MWMO_ALERTABLE | MWMO_INPUTAVAILABLE);

        if (what == WAIT_OBJECT_0) {
            if (!GetMessage(&msg, NULL, 0, 0)) {
                break;
            }

            if (msg.hwnd == s_hWndMain) {
                switch (msg.message) {
                  case WM_SOCKET_EVENT:
                    SocketEvent(msg.wParam, msg.lParam);
                    break;
                  case WM_TIMER:
                    if (msg.wParam == 0) {
                        fScanNetwork = TRUE;
                    }
                    else {
                        ITimerSink *pTimerSink = (ITimerSink *)msg.wParam;
                        pTimerSink->OnTimerFired();
                    }
                    break;
                }
            }
            TranslateMessage(&msg);
            DispatchMessage(&msg);
        }
    }

  abort:
    if (m_pDhcpPxe)
    {
        delete m_pDhcpPxe;
        m_pDhcpPxe = NULL;
    }
    if (m_pTftp)
    {
        delete m_pTftp;
        m_pTftp = NULL;
    }
    if (m_pDhcpRaw)
    {
        delete m_pDhcpRaw;
        m_pDhcpRaw = NULL;
    }
    if (m_pDhcpState)
    {
        delete m_pDhcpState;
        m_pDhcpState = NULL;
    }

    // close down winsock
    WSACleanup();

    fflush(stdout);

    return 0;
}
//
///////////////////////////////////////////////////////////////// End of File.
