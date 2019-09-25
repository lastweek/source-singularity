//////////////////////////////////////////////////////////////////////////////
//

#pragma once
#include "hashtab.h"
#include "socksr.h"

#define DHCP_SERVER_PORT 67
#define DHCP_CLIENT_PORT 68
#define PXE_SERVER_PORT 4011

//////////////////////////////////////////////////////////////////////////////
//
class CDhcp;
class CDhcpNode;

class IDhcpSink
{
  public:
    virtual VOID OnDhcpMessage(UINT32 nAddr, PCSTR pszMessage, ...) = 0;
    virtual VOID OnDhcpSocketError(INT nErr) = 0;

    virtual VOID OnDhcpOffer(UINT32 nAddr, UINT64 idMac) = 0;
    virtual VOID OnDhcpAck(UINT32 nAddr, UINT64 idMac) = 0;
};

class CDhcpNode
{
  public:
    friend class CDhcpNode;
    CDhcpNode();

  public:
    BOOL    Enabled;
    CHAR    Name[64];

    UINT64  idMac;

    UINT32  iaLast;                                     // Last known good addr.
    UINT32  iaAssigned;                                 // Addr we want to assign.
};

class CDhcpState
{
  public:
    friend class CDhcp;

    CDhcpState();
    ~CDhcpState();

    VOID    Configure(IDhcpSink *pSink, INT argc, PCHAR *argv);

  public:
    CDhcpNode *FindMacEntry(UINT64 idMac);

  protected:
    VOID    CheckMacFlags(CDhcpNode *pMap);
    BOOL    ReadMacEntries(PCSTR pszFile);
    BOOL    AddMacEntry(PCSTR psz);

    BOOL    IsPxeDhcpPacket(PBYTE pbPacket, UINT32 cbPacket);

  protected:
    CHAR    m_szBootFile[MAX_PATH];
    CHAR    m_szCommand[MAX_PATH];
    BOOL    m_fQuiet;

    CHashTable64<CDhcpNode*>  m_MacsById;
    IDhcpSink *m_pSink;
};

class CDhcp : public CSocketSink
{
  public:
    CDhcp(CDhcp *pNext);
    ~CDhcp();

    VOID    Configure(UINT32 nAddr, UINT32 nMask, UINT32 nGate,
                      CDhcpState *pState, IDhcpSink *pSink, UINT16 nPort);

    VOID    OnSocketRecv(UINT dwError,
                         UINT32 nAddr, UINT16 nPort, PBYTE pbData, UINT cbData);

    VOID    OnNetworkChange(UINT32 nAddr, UINT32 nMask, UINT32 nGate);
    VOID    OnNetworkDelete(UINT32 nAddr, CDhcp **ppNext);

  protected:
    UINT32  m_nAddr;
    UINT32  m_nMask;
    UINT32  m_nGate;
    UINT16  m_nPort;

    CDhcp *m_pNext;
    CDhcpState *m_pState;
    IDhcpSink *m_pSink;
};

//
///////////////////////////////////////////////////////////////// End of File.
