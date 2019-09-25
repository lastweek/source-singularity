// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//////////////////////////////////////////////////////////////////////////////
//
//
//
#include <winlean.h>
#include <winsock.h>
#include <iphlpapi.h>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "socksr.h"
#include "hashtab.h"

#define ARRAYOF(x)      (sizeof(x)/sizeof(x[0]))
#define ASSERT(a)       assert(a)

//////////////////////////////////////////////////////////////////////////////
//

// Linked list of networks.  Sorted from low to high by address.
static CNetwork *s_pNetworks = NULL;

// Get all of the available networks.  Returns true if the list of networks
// has changed.
// ISSUE: Currently only adds, doesn't remove.
static int __cdecl cmpIpAddrRow(const void *fvp, const void *svp)
{
    const PMIB_IPADDRROW fp = (const PMIB_IPADDRROW)fvp;
    const PMIB_IPADDRROW sp = (const PMIB_IPADDRROW)svp;

    if (fp->dwAddr < sp->dwAddr) {
        return -1;
    }
    else if (fp->dwAddr > sp->dwAddr) {
        return 1;
    }
    return 0;
}

static int __cdecl cmpIpForwardRow(const void *fvp, const void *svp)
{
    const PMIB_IPFORWARDROW fp = (const PMIB_IPFORWARDROW)fvp;
    const PMIB_IPFORWARDROW sp = (const PMIB_IPFORWARDROW)svp;

    if (fp->dwForwardIfIndex < sp->dwForwardIfIndex) {
        return -1;
    }
    else if (fp->dwForwardIfIndex > sp->dwForwardIfIndex) {
        return 1;
    }
    if (fp->dwForwardNextHop < sp->dwForwardNextHop) {
        return -1;
    }
    else if (fp->dwForwardNextHop > sp->dwForwardNextHop) {
        return 1;
    }
    return 0;
}

PCSTR SocketToString(UINT32 dwAddr)
{
    static CHAR rszAddrs[16][32];
    static int nAddrs = 0;

    CHAR *pszAddr = rszAddrs[nAddrs];
    nAddrs = (nAddrs + 1) % ARRAYOF(rszAddrs);

    sprintf(pszAddr, "%d.%d.%d.%d",
            (dwAddr >> 24) & 0xff,
            (dwAddr >> 16) & 0xff,
            (dwAddr >>  8) & 0xff,
            (dwAddr >>  0) & 0xff);
    return pszAddr;
}


BOOL SocketLoadNetworks(CNetwork ** ppNetworks)
{
#if 0
    PMIB_IFTABLE pIfTable = NULL;
#endif
    PMIB_IPADDRTABLE pIpAddrTable = NULL;
    PMIB_IPFORWARDTABLE pIpForwardTable = NULL;
#if 0
    ULONG cbIfTable = 0;
#endif
    ULONG cbIpAddrTable = 0;
    ULONG cbIpForwardTable = 0;
#if 0
    ULONG nIfTable = 0;
#endif
    ULONG nIpAddrTable = 0;
    ULONG nIpForwardTable = 0;
    DWORD err = 0;
    BOOL fChanged = FALSE;

    // Retrieve the address and forwarding tables.
    //
    for (;;) {
        err = GetIpAddrTable(pIpAddrTable, &cbIpAddrTable, FALSE);
        if (err == NO_ERROR) {
            break;
        }
        if (pIpAddrTable != NULL) {
            delete[] (PUINT8)pIpAddrTable;
            pIpAddrTable = NULL;
        }
        if (err != ERROR_INSUFFICIENT_BUFFER) {
            break;
        }

        pIpAddrTable = (PMIB_IPADDRTABLE)new UINT8 [cbIpAddrTable];
    }

    for (;;) {
        err = GetIpForwardTable(pIpForwardTable, &cbIpForwardTable, FALSE);
        if (err == NO_ERROR) {
            break;
        }
        if (pIpForwardTable != NULL) {
            delete[] (PUINT8)pIpForwardTable;
            pIpForwardTable = NULL;
        }
        if (err != ERROR_INSUFFICIENT_BUFFER) {
            break;
        }

        pIpForwardTable = (PMIB_IPFORWARDTABLE)new UINT8 [cbIpForwardTable];
    }

#if 0
    for (;;) {
        err = GetIfTable(pIfTable, &cbIfTable, TRUE);
        if (err == NO_ERROR) {
            break;
        }
        if (pIfTable != NULL) {
            delete[] (PUINT8)pIfTable;
            pIfTable = NULL;
        }
        if (err != ERROR_INSUFFICIENT_BUFFER) {
            break;
        }

        pIfTable = (PMIB_IFTABLE)new UINT8 [cbIfTable];
        nIfTable = pIfTable->dwNumEntries;
    }
#endif

    // Sort the tables.
    //
    if (pIpAddrTable) {
        for (DWORD n = 0; n < pIpAddrTable->dwNumEntries; n++) {
            pIpAddrTable->table[n].dwAddr
                = ntohl(pIpAddrTable->table[n].dwAddr);
            pIpAddrTable->table[n].dwMask
                = ntohl(pIpAddrTable->table[n].dwMask);
            pIpAddrTable->table[n].dwBCastAddr
                = ntohl(pIpAddrTable->table[n].dwBCastAddr);
        }
        qsort(pIpAddrTable->table,
              pIpAddrTable->dwNumEntries,
              sizeof(pIpAddrTable->table[0]),
              cmpIpAddrRow);
        nIpAddrTable = pIpAddrTable->dwNumEntries;
    }

    if (pIpForwardTable) {
        for (DWORD n = 0; n < pIpForwardTable->dwNumEntries; n++) {
            pIpForwardTable->table[n].dwForwardDest
                = ntohl(pIpForwardTable->table[n].dwForwardDest);
            pIpForwardTable->table[n].dwForwardMask
                = ntohl(pIpForwardTable->table[n].dwForwardMask);
            pIpForwardTable->table[n].dwForwardNextHop
                = ntohl(pIpForwardTable->table[n].dwForwardNextHop);
        }
        qsort(pIpForwardTable->table,
              pIpForwardTable->dwNumEntries,
              sizeof(pIpForwardTable->table[0]),
              cmpIpForwardRow);
        nIpForwardTable = pIpForwardTable->dwNumEntries;
    }

#if 0
    if (pIfTable) {
        for (DWORD n = 0; n < nIfTable; n++) {
            printf("%7d. %ls\n",
                   pIfTable->table[n].dwIndex,
                   pIfTable->table[n].wszName);
        }
    }
#endif

    // Normalize the list, delete any fDeleted entries.
    //
    CNetwork **pNetworkLast = &s_pNetworks;
    CNetwork *pNetwork = s_pNetworks;

    while (pNetwork != NULL) {
        if (pNetwork->fDeleted) {
            *pNetworkLast = pNetwork->pNext;

            delete pNetwork;
            pNetwork = *pNetworkLast;
        }
        else {
            pNetwork->fCreated = FALSE;
            pNetwork->fDeleted = FALSE;
            pNetwork->fChanged = FALSE;

            pNetworkLast = &pNetwork->pNext;
            pNetwork = pNetwork->pNext;
        }
    }

    // Walk through the tables, updating the persistent linked list.
    //
    pNetworkLast = &s_pNetworks;
    pNetwork = s_pNetworks;

#if 0
    printf("---------------------------------------------------------------------------\n");
    for (DWORD n = 0; n < nIpAddrTable; n++) {
        printf("                 %5d: %-15.15s -%15.15s\n",
               pIpAddrTable->table[n].dwIndex,
               SocketToString(pIpAddrTable->table[n].dwAddr),
               SocketToString(pIpAddrTable->table[n].dwMask));
    }
#endif

    for (DWORD n = 0; n < nIpAddrTable;) {
        UINT32 nAddr = 0;
        UINT32 nMask = 0;
        UINT32 nCast = 0;
        UINT32 nGate = 0;

        if (pIpAddrTable->table[n].dwAddr == 0 ||
            (pIpAddrTable->table[n].dwAddr & 0xff000000) == 0x7f000000) {

            // Drop 0 networks and 127.*.*.*, the local loopback.
            n++;
            continue;
        }

        nAddr = pIpAddrTable->table[n].dwAddr;
        nMask = pIpAddrTable->table[n].dwMask;
        nCast = (nMask & nAddr) | ~nMask;

        for (DWORD f = 0; f < nIpForwardTable; f++) {
            if (pIpForwardTable->table[f].dwForwardIfIndex
                == pIpAddrTable->table[n].dwIndex &&
                pIpForwardTable->table[f].dwForwardNextHop
                != pIpAddrTable->table[n].dwAddr
               ) {

                nGate = pIpForwardTable->table[f].dwForwardNextHop;
                break;
            }
        }

#if 0
        MIB_IFROW interface;
        memset(&interface, 0, sizeof(interface));
        interface.dwIndex = pIpAddrTable->table[n].dwIndex;

        err = GetIfEntry(&interface);
        if (err == NO_ERROR) {
            printf("Interface %d: %ls %s %04x%04x MTU=%d\n",
                   interface.dwIndex, interface.wszName, interface.wszName,
                   interface.wszName[0], interface.wszName[1],
                   interface.dwMtu);
            printf("    %.*s\n",
                   interface.dwDescrLen, interface.bDescr);
        }
#endif

        // At this point, we have a valid external address
        //
        if (pNetwork && pNetwork->nAddr == nAddr) {
            // The network was known...
            // Update the flags, and move both list and table to the
            // next network.

#if 0
            printf("Existed: %s\n", SocketToString(nAddr));
#endif
            // If it was previously deleted, then it has been re-created.
            pNetwork->fCreated = pNetwork->fDeleted;
            pNetwork->fChanged = pNetwork->fDeleted;
            pNetwork->fDeleted = FALSE;

            if (pNetwork->nMask != nMask ||
                pNetwork->nCast != nCast ||
                pNetwork->nGate != nGate) {

                pNetwork->nMask = nMask;
                pNetwork->nCast = nCast;
                pNetwork->nGate = nGate;

                pNetwork->fChanged = TRUE;
            }

            if (pNetwork->fCreated ||
                pNetwork->fDeleted ||
                pNetwork->fChanged) {

                fChanged = TRUE;
            }

            pNetworkLast = &pNetwork->pNext;
            pNetwork = pNetwork->pNext;
            n++;
            continue;
        }
        else if (pNetwork == NULL || pNetwork->nAddr > nAddr) {
            // The table network is new...

#if 0
            printf("Created: %s\n", SocketToString(nAddr));
#endif
            CNetwork *pNew = new CNetwork;
            if (pNew != NULL) {
                pNew->pNext = pNetwork;
                pNew->nAddr = nAddr;
                pNew->nMask = nMask;
                pNew->nCast = nCast;
                pNew->nGate = nGate;
                pNew->fCreated = TRUE;
                pNew->fDeleted = FALSE;
                pNew->fChanged = FALSE;
                fChanged = TRUE;

                *pNetworkLast = pNew;
                pNetworkLast = &pNew->pNext;
            }
#if 0
            else {
                printf("Couldn't create: %s\n", SocketToString(nAddr));
            }
#endif
            n++;
            continue;
        }
        else if (pNetwork->nAddr < nAddr) {
            // The list network was deleted...

#if 0
            printf("Deleted: %s\n", SocketToString(nAddr));
#endif
            pNetwork->fCreated = FALSE;
            pNetwork->fDeleted = TRUE;
            pNetwork->fChanged = FALSE;
            fChanged = TRUE;

            pNetworkLast = &pNetwork->pNext;
            pNetwork = pNetwork->pNext;
            continue;
        }
        else {
            ASSERT(!"Untested case.");
        }
    }

    while (pNetwork != NULL) {
        // The list network was deleted...

#if 0
        printf("Deleted: %s\n", SocketToString(nAddr));
#endif
        pNetwork->fCreated = FALSE;
        pNetwork->fDeleted = TRUE;
        pNetwork->fChanged = FALSE;
        fChanged = TRUE;

        pNetworkLast = &pNetwork->pNext;
        pNetwork = pNetwork->pNext;
        continue;
    }

#if 0
    printf("------------------------------------------------------------------------------\n");
    for (pNetwork = s_pNetworks; pNetwork != NULL; pNetwork = pNetwork->pNext) {
        printf("    %-15.15s: %-15.15s %-15.15s %-15.15s %s%s%s\n",
               SocketToString(pNetwork->nAddr),
               SocketToString(pNetwork->nMask),
               SocketToString(pNetwork->nCast),
               SocketToString(pNetwork->nGate),
               pNetwork->fCreated ? "Created " : "",
               pNetwork->fDeleted ? "Deleted " : "",
               pNetwork->fChanged ? "Changed " : "");
    }
#endif


    if (pIpAddrTable != NULL) {
        delete[] (PUINT8)pIpAddrTable;
        pIpAddrTable = NULL;
    }
    if (pIpForwardTable != NULL) {
        delete[] (PUINT8)pIpForwardTable;
        pIpForwardTable = NULL;
    }
    if (ppNetworks) {
        *ppNetworks = s_pNetworks;
    }
    return FALSE;
}


//////////////////////////////////////////////////////////////////////////////
//

struct CSocketSource : public ISocketSource
{
    CSocketSource(ISocketSink *pSink);
    ~CSocketSource();

    // ISocketSource
  public:
    virtual UINT    SocketSend(UINT32 nAddr, UINT16 nPort, PBYTE pbData, UINT cbData);
    virtual UINT    SocketClose(UINT dwError);

  public:
    VOID OnRecv();

    SOCKET          m_nSocket;
    ISocketSink *   m_pSink;
};

//////////////////////////////////////////////////////////////////////////////
//
static HWND             s_hWnd;                         // Host Window
static UINT             s_nMsg;                         // Host Event
static CHashTable32<CSocketSource*> s_Sockets;

//////////////////////////////////////////////////////////////////////////////
//
CSocketSource::CSocketSource(ISocketSink *pSink)
    : m_nSocket(0),
      m_pSink(pSink)
{
}

CSocketSource::~CSocketSource()
{
    if (m_pSink)
    {
        ISocketSink *pSink = m_pSink;
        m_pSink = NULL;
        pSink->OnSocketClose(0);
    }
    if (m_nSocket)
    {
        closesocket(m_nSocket);
        m_nSocket = 0;
    }
}

UINT CSocketSource::SocketSend(UINT32 nAddr, UINT16 nPort, PBYTE pbData, UINT cbData)
{
    // Fill out server socket's address information.
    SOCKADDR_IN server_sin;
    server_sin.sin_family = AF_INET;
    server_sin.sin_port = htons(nPort);
    server_sin.sin_addr.s_addr = htonl(nAddr);

    int iRes = sendto(m_nSocket, (const char *)pbData, cbData,
                      0, (struct sockaddr FAR *) &server_sin, sizeof(server_sin));
    return (SOCKET_ERROR == iRes) ? WSAGetLastError() : 0;
}

VOID CSocketSource::OnRecv()
{
    SOCKADDR_IN from;
    int fromlen = sizeof(from);

    BYTE rbData[2048];
    int iRes = recvfrom(m_nSocket, (char *)rbData, sizeof(rbData), 0,
                        (struct sockaddr *)&from, &fromlen);
    int nErr = (iRes == SOCKET_ERROR) ? WSAGetLastError() : 0;

    if (nErr == WSAECONNRESET || nErr == WSAEWOULDBLOCK) {
        // Lost a packet.  Don't worry about it.
    }
    else {
        m_pSink->OnSocketRecv(nErr,
                              ntohl(from.sin_addr.s_addr),
                              ntohs(from.sin_port),
                              rbData,
                              iRes);
    }
}

UINT CSocketSource::SocketClose(UINT dwError)
{
    if (m_pSink)
    {
        ISocketSink *pSink = m_pSink;
        m_pSink = NULL;

        s_Sockets.Delete(m_nSocket);
        pSink->OnSocketClose(dwError);
        delete this;
    }
    return 0;
}

//////////////////////////////////////////////////////////////////////////////
//
VOID SocketInit(HWND hWnd, UINT nMsg)
{
    s_hWnd = hWnd;
    s_nMsg = nMsg;
}

LRESULT SocketEvent(WPARAM wParam, LPARAM lParam)
{
    WORD wSelectError = HIWORD(lParam);
    WORD wSelectEvent = LOWORD(lParam);
    DWORD dwSocket = wParam;

    (void)wSelectError;

    CSocketSource *pSource = s_Sockets.Find(dwSocket);
    if (pSource == NULL) {
        return 0;
    }

    if (wSelectEvent & FD_READ) {
        pSource->OnRecv();
    }
    return 0;
}

UINT SocketCreate(UINT32 nLocalAddr, UINT16 wLocalPort, ISocketSink *pSink)
{
    SOCKET s = INVALID_SOCKET;
    CSocketSource *pSource = NULL;
    UINT nError;
    int iRes;

    if (pSink == NULL) {
        nError = (UINT)E_INVALIDARG;
      Error:
        if (pSource) {
            delete pSource;
            pSource = NULL;
        }
        if (s != INVALID_SOCKET) {
            closesocket(s);
            s = INVALID_SOCKET;
        }
        return nError;
    }

    if ((pSource = new CSocketSource(pSink)) == NULL) {
        nError = (UINT)E_OUTOFMEMORY;
        goto Error;
    }

    // Create a datagram window socket.
    s = socket(AF_INET, SOCK_DGRAM, 0);
    if (INVALID_SOCKET == s) {
      SocketError:
        nError = WSAGetLastError();
        goto Error;
    }

    // allow broadcasts on this socket
    BOOL optBOOL = TRUE;
    iRes = setsockopt(s, SOL_SOCKET, SO_BROADCAST,
                      (char *)&optBOOL, sizeof(optBOOL));
    if (0 != iRes) {
        goto SocketError;
    }

    // Fill out the client socket's address information.
    SOCKADDR_IN client_sin;
    client_sin.sin_family = AF_INET;
    client_sin.sin_port = htons(wLocalPort);
    client_sin.sin_addr.s_addr = htonl(nLocalAddr);

    // Associate the client socket's address with the socket, Sock.
    iRes = bind(s, (LPSOCKADDR)&client_sin, sizeof(client_sin));
    if (0 != iRes) {
        goto SocketError;
    }

    // Set the socket as NON-BLOCKING.
    DWORD ioctlVal = TRUE;
    iRes = ioctlsocket(s, FIONBIO, &ioctlVal);
    if (SOCKET_ERROR == iRes) {
        goto SocketError;
    }

    // Set windows for async event..
    iRes = WSAAsyncSelect(s, s_hWnd, s_nMsg,
                          FD_READ | FD_WRITE | FD_OOB | FD_ACCEPT | FD_CONNECT);
    if (SOCKET_ERROR == iRes) {
        goto SocketError;
    }

    pSource->m_nSocket = s;

#if 0
    {
        // Fill out server socket's address information.
        SOCKADDR_IN server_sin;
        server_sin.sin_family = AF_INET;
        server_sin.sin_port = htons(4011);
        server_sin.sin_addr.s_addr = 0xffffffff;

        sendto(s, "OpenPort", 8,
               0, (struct sockaddr FAR *) &server_sin, sizeof(server_sin));
    }
#endif

    s_Sockets.Insert(s, pSource);

    pSink->OnSocketCreate(pSource);
    return 0;
}

//////////////////////////////////////////////////////////////////////////////
//
static inline UINT64 MakeId(UINT32 nAddr, UINT16 nPort) {
    return (UINT64)nAddr | ((UINT64)nPort << 32);
}

struct CSocketFactory : public ISocketSink,
                        public ISessionFactorySource
{
    friend struct CSocketSession;

    struct CSocketSession : public ISessionSource
    {
        CSocketSession(CSocketFactory *pOwner,
                       UINT32 nPeerAddr,
                       UINT16 nPeerPort)
            : m_pOwner(pOwner),
              m_nPeerAddr(nPeerAddr),
              m_nPeerPort(nPeerPort),
              m_pSink(NULL)
        {
        }
        ~CSocketSession()
        {
            if (m_pSink)
            {
                ISessionSink *pSink = m_pSink;
                m_pSink = NULL;
                pSink->OnSessionClose(0);
            }
        }

        // ISessionSource
      public:
        virtual UINT    SessionSend(PBYTE pbData, UINT cbData)
        {
            return m_pOwner->SocketSend(m_nPeerAddr, m_nPeerPort, pbData, cbData);
        }

        virtual UINT    SessionClose(UINT dwError)
        {
            if (m_pSink) {
                ISessionSink *pSink = m_pSink;
                m_pSink = NULL;

                m_pOwner->m_Sessions.Delete(MakeId(m_nPeerAddr, m_nPeerPort));
                pSink->OnSessionClose(dwError);
            }
            return 0;
        }

      public:
        VOID OnRecv(UINT dwError, PBYTE pbData, UINT cbData)
        {
            if (m_pSink)
            {
                m_pSink->OnSessionRecv(dwError, pbData, cbData);
            }
        }

        CSocketFactory *m_pOwner;
        UINT32          m_nPeerAddr;
        UINT16          m_nPeerPort;
        ISessionSink *  m_pSink;
    };

    //
  public:
    CSocketFactory(ISessionFactorySink *pSink)
        : m_pSource(NULL),
          m_pSink(pSink)
    {
    }

    ~CSocketFactory()
    {
        DoFactoryClose(0);
    }

    BOOL DoFactoryClose(UINT dwError)
    {
        if (m_pSink)
        {
            ISessionFactorySink *pSink = m_pSink;
            m_pSink = NULL;

            CSocketSession *pSession;
            UINT64 nKey;

            for (INT nIt = 0; (pSession = m_Sessions.Enumerate(nKey, nIt)) != NULL;) {
                pSession->SessionClose(dwError);
                pSession = NULL;
                // Sessions delete themselves from the m_Sessions.
            }
            pSink->OnFactoryClose(dwError);

            if (m_pSource) {
                ISocketSource *pSource = m_pSource;
                m_pSource = NULL;

                pSource->SocketClose(0);
            }
            return TRUE;
        }
        return FALSE;
    }

    // ISessionFactorySource
  public:
    virtual UINT    FactorySend(UINT32 nAddr, UINT16 nPort,
                                PBYTE pbData, UINT cbData)
    {
        return m_pSource->SocketSend(nAddr, nPort, pbData, cbData);
    }

    virtual UINT    FactoryClose()
    {
        if (DoFactoryClose(0)) {
            delete this;
        }
        return 0;
    }

    virtual UINT    FactorySessionCreate(UINT32 nPeerAddr,
                                         UINT16 nPeerPort,
                                         ISessionSink **ppSink,
                                         PVOID pvContext)
    {
        // Are we shutting down?
        if (m_pSink == NULL) {
            return (UINT)E_PENDING;
        }
        if (ppSink == NULL) {
            return (UINT)E_INVALIDARG;
        }

        CSocketSession *pSession = m_Sessions.Find(MakeId(nPeerAddr, nPeerPort));
        if (m_Sessions.Find(MakeId(nPeerAddr, nPeerPort))) {
            pSession->SessionClose((UINT)E_ABORT);
            pSession = NULL;

            printf("FactorySessionCreate: closed existing session.\n");

            // return (UINT)E_ABORT;
        }

        pSession = new CSocketSession(this, nPeerAddr, nPeerPort);
        if (pSession == NULL) {
            return (UINT)E_OUTOFMEMORY;
        }

        m_pSink->OnSessionCreate(nPeerAddr, nPeerPort, pSession, ppSink, pvContext);
        if (*ppSink == NULL) {
            delete pSession;
            return 1;
        }
        pSession->m_pSink = *ppSink;

        m_Sessions.Insert(MakeId(nPeerAddr, nPeerPort), pSession);
        (*ppSink)->OnSessionCreate(pSession, pvContext);

        return 0;
    }

    // ISocketSink
  public:
    virtual VOID    OnSocketCreate(ISocketSource *pSource)
    {
        m_pSource = pSource;
        m_pSink->OnFactoryCreate(this);
    }

    virtual VOID    OnSocketClose(UINT dwError)
    {
        if (DoFactoryClose(dwError)) {
            delete this;
        }
    }

    virtual VOID    OnSocketRecv(UINT dwError,
                                 UINT32 nAddr, UINT16 nPort,
                                 PBYTE pbData, UINT cbData)
    {
        CSocketSession *pSession = m_Sessions.Find(MakeId(nAddr, nPort));
        if (pSession) {
            pSession->OnRecv(dwError, pbData, cbData);
        }
        else {
            m_pSink->OnFactoryRecv(dwError, nAddr, nPort, pbData, cbData);
        }
    }

    UINT    SocketSend(UINT32 nAddr, UINT16 nPort, PBYTE pbData, UINT cbData)
    {
        return m_pSource->SocketSend(nAddr, nPort, pbData, cbData);
    }

  public:
    ISessionFactorySink *           m_pSink;
    ISocketSource *                 m_pSource;
    CHashTable64<CSocketSession*>   m_Sessions;
};

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////// UDP Sessions.
//////////////////////////////////////////////////////////////////////////////

UINT SessionFactoryCreate(UINT32 nLocalAddr, UINT16 nLocalPort,
                          ISessionFactorySink *pFactorySink)
{
    CSocketFactory *pFactory = new CSocketFactory(pFactorySink);
    if (pFactory == NULL) {
        return (UINT)E_OUTOFMEMORY;
    }

    UINT nError = SocketCreate(nLocalAddr, nLocalPort, pFactory);

    if (nError != 0) {
        delete pFactory;
    }
    return nError;
}

//
///////////////////////////////////////////////////////////////// End of File.
