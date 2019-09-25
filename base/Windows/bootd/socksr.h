//////////////////////////////////////////////////////////////////////////////
//
#pragma once

#ifndef UINT16
#define INT16   SHORT
#define UINT16  USHORT
#define UINT8   BYTE
#define PINT16  PSHORT
#define PUINT16 PUSHORT
#define PUINT8  PBYTE
#endif

#pragma warning(disable: 4512)

//////////////////////////////////////////////////////////////////////////////
//
class ITimerSink
{
  public:
    virtual VOID OnTimerFired(VOID) = 0;
};

//////////////////////////////////////////////////////////////////////////////
//
struct CNetwork
{
    CNetwork *  pNext;
    UINT32      nAddr;
    UINT32      nMask;
    UINT32      nCast;
    UINT32      nGate;
    BOOL        fCreated;           // Updated on SocketLoadNetworks.
    BOOL        fChanged;           // Updated on SocketLoadNetworks.
    BOOL        fDeleted;           // Updated on SocketLoadNetworks.
};

///////////////////////////////////////////////////////////////// UDP Sockets.
//
class ISocketSource
{
  public:
    virtual UINT    SocketSend(UINT32 nAddr,
                               UINT16 nPort,
                               PBYTE pbData,
                               UINT cbData) = 0;

    virtual UINT    SocketClose(UINT dwError) = 0;
};

class ISocketSink
{
  public:
    virtual VOID    OnSocketCreate(ISocketSource *pSource) = 0;

    virtual VOID    OnSocketRecv(UINT dwError,
                                 UINT32 nAddr,
                                 UINT16 nPort,
                                 PBYTE pbData,
                                 UINT cbRcvd) = 0;

    virtual VOID    OnSocketClose(UINT dwError) = 0;
};

//////////////////////////////////////////////////////////////////// Sessions.
//
class ISessionSource
{
  public:
    virtual UINT    SessionSend(PBYTE pbData, UINT cbData) = 0;
    virtual UINT    SessionClose(UINT dwError) = 0;
};

class ISessionSink
{
  public:
    virtual VOID    OnSessionCreate(ISessionSource *pSource,
                                    PVOID pvContext) = 0;

    virtual VOID    OnSessionRecv(UINT dwError,
                                  PBYTE pbData,
                                  UINT cbRcvd) = 0;

    virtual VOID    OnSessionClose(UINT dwError) = 0;
};

//////////////////////////////////////////////////////////////////////////////
//
class ISessionFactorySource
{
  public:
    virtual UINT    FactorySessionCreate(UINT32 nPeerAddr,
                                         UINT16 nPeerPort,
                                         ISessionSink **ppSink,
                                         PVOID pvContext) = 0;

    virtual UINT    FactorySend(UINT32 nAddr,
                                UINT16 nPort,
                                PBYTE pbData,
                                UINT cbData) = 0;

    virtual UINT    FactoryClose() = 0;
};

class ISessionFactorySink
{
  public:
    virtual VOID    OnFactoryCreate(ISessionFactorySource *pFactorySource) = 0;

    virtual VOID    OnFactoryRecv(UINT dwError,
                                  UINT32 nAddr,
                                  UINT16 nPort,
                                  PBYTE pbData,
                                  UINT cbRcvd) = 0;

    virtual VOID    OnFactoryClose(UINT dwError) = 0;

    virtual VOID    OnSessionCreate(UINT32 nPeerAddr,
                                    UINT16 nPeerPort,
                                    ISessionSource *pSource,
                                    ISessionSink **ppSink,
                                    PVOID pvContext) = 0;
};

//////////////////////////////////////////////////////////////////////////////
//
class CSocketSink : public ISocketSink
{
  public:
    CSocketSink()
        : m_pSource(NULL)
    {
    }

    ~CSocketSink()
    {
        if (m_pSource) {
            m_pSource->SocketClose(0);
            m_pSource = NULL;
        }
    }

    virtual VOID    OnSocketCreate(ISocketSource *pSource)
    {
        m_pSource = pSource;
    }

    virtual VOID    OnSocketClose(UINT dwError)
    {
        (void)dwError;
        m_pSource = NULL;
    }

    virtual VOID    OnSocketRecv(UINT dwError,
                                 UINT32 nAddr, UINT16 nPort,
                                 PBYTE pbData, UINT cbData) = 0;

    UINT    SocketSend(UINT32 nAddr, UINT16 nPort, PBYTE pbData, UINT cbData)
    {
        return m_pSource->SocketSend(nAddr, nPort, pbData, cbData);
    }

  public:
    ISocketSource * m_pSource;
};

class CSessionSink : public ISessionSink
{
  public:
    CSessionSink()
        : m_pSource(NULL)
    {
    }

    ~CSessionSink()
    {
        if (m_pSource) {
            m_pSource->SessionClose(0);
            m_pSource = NULL;
        }
    }

    virtual VOID    OnSessionCreate(ISessionSource *pSource, PVOID pvContext)
    {
        (void)pvContext;

        m_pSource = pSource;
    }

    virtual VOID    OnSessionClose(UINT dwError)
    {
        (void)dwError;
        m_pSource = NULL;
    }

    virtual VOID    OnSessionRecv(UINT dwError, PBYTE pbData, UINT cbData) = 0;

    UINT    SessionSend(PBYTE pbData, UINT cbData)
    {
        return m_pSource->SessionSend(pbData, cbData);
    }

  public:
    ISessionSource * m_pSource;
};

class CSessionFactorySink : public ISessionFactorySink
{
  public:
    CSessionFactorySink()
        : m_pFactorySource(NULL)
    {
    }

    ~CSessionFactorySink()
    {
        if (m_pFactorySource) {
            m_pFactorySource->FactoryClose();
            m_pFactorySource = NULL;
        }
    }

    // ISessionFactorySink
  public:
    virtual VOID    OnFactoryCreate(ISessionFactorySource *pFactorySource)
    {
        m_pFactorySource = pFactorySource;
    }

    virtual VOID    OnFactoryRecv(UINT dwError,
                                  UINT32 nAddr,
                                  UINT16 nPort,
                                  PBYTE pbData,
                                  UINT cbRcvd) = 0;

    virtual VOID    OnFactoryClose(UINT dwError)
    {
        (void)dwError;
        m_pFactorySource = NULL;
    }

    virtual VOID    OnSessionCreate(UINT32 nPeerAddr,
                                    UINT16 nPeerPort,
                                    ISessionSource *pSource,
                                    ISessionSink **ppSink,
                                    PVOID pvContext) = 0;

    UINT    FactorySessionCreate(UINT32 nPeerAddr,
                                 UINT16 nPeerPort,
                                 ISessionSink **ppSink,
                                 PVOID pvContext)
    {
        return m_pFactorySource->FactorySessionCreate(nPeerAddr, nPeerPort,
                                                      ppSink, pvContext);
    }

    UINT    FactorySend(UINT32 nAddr,
                        UINT16 nPort,
                        PBYTE pbData,
                        UINT cbData)
    {
        return m_pFactorySource->FactorySend(nAddr, nPort, pbData, cbData);
    }

    UINT    FactoryClose()
    {
        return m_pFactorySource->FactoryClose();
    }

  public:
    ISessionFactorySource * m_pFactorySource;
};

//////////////////////////////////////////////////////////////////////////////
//

BOOL    TimerSet(ITimerSink *pTimerSink, UINT nMilliseconds);
BOOL    TimerClr(ITimerSink *pTimerSink);

VOID    SocketInit(HWND hWnd, UINT nMsg);
LRESULT SocketEvent(WPARAM wParam, LPARAM lParam);
UINT    SocketCreate(UINT32 nLocalAddr, UINT16 wLocalPort,
                     ISocketSink *pSink);
UINT    SessionFactoryCreate(UINT32 nLocalAddr, UINT16 wLocalPort,
                             ISessionFactorySink *pFactorySink);

BOOL    SocketLoadNetworks(CNetwork ** ppNetworks);

PCSTR   SocketToString(UINT32 dwAddr);

//
///////////////////////////////////////////////////////////////// End of File.
