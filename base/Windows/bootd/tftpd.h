//------------------------------------------------------------------------------
//
//  Microsoft Research
//  Copyright (C) Microsoft Corporation
//
//  Contents:   TFTP Daemon
//
//------------------------------------------------------------------------------

//
// Trivial File Transfer Protocol (TFTP) as per RFCs 1350, 1782, 1783 & 1784.
//

#define TFTP_PORT 69  // Internet standard

class ITftpSink
{
  public:
    virtual VOID OnTftpSocketError(INT nErr) = 0;
    virtual VOID OnTftpMessage(UINT32 nAddr, PCSTR pszMessage, ...) = 0;
    virtual VOID OnTftpAccessBegin(UINT32 nAddr, UINT16 nPort, BOOL bWrite, PCSTR pszFile) = 0;
    virtual VOID OnTftpAccessEnd(UINT32 nAddr, UINT16 nPort, BOOL bSuccess) = 0;
};

class CTftp : public CSessionFactorySink
{
  public:
    friend class CTftpNode;

    CTftp(CTftp *pNext);
    ~CTftp();

    static VOID ConfigureFiles(ITftpSink *pSink, INT argc, PCHAR *argv);
    static VOID OnFilesChange(ITftpSink *pSink);

    VOID    Configure(UINT32 nAddr, UINT16 nPort,
                      ITftpSink *pSink, INT argc, PCHAR *argv);

    VOID    OnNetworkChange(UINT32 nAddr, UINT32 nMask, UINT32 nGate);
    VOID    OnNetworkDelete(UINT32 nAddr, CTftp **ppNext);

    // ISessionFactorySink
  public:
    virtual VOID    OnFactoryRecv(UINT dwError,
                                  UINT32 nAddr,
                                  UINT16 nPort,
                                  PBYTE pbData,
                                  UINT cbRcvd);

    virtual VOID    OnFactoryClose(UINT dwError);

    virtual VOID    OnSessionCreate(UINT32 nPeerAddr,
                                    UINT16 nPeerPort,
                                    ISessionSource *pSource,
                                    ISessionSink **ppSink,
                                    PVOID pvContext);

  protected:
    VOID    Log(ULONG nAddr, PCSTR pszMsg, ...);

    inline UINT64 MakeId(UINT32 nAddr, UINT16 nPort) {
        return (UINT64)nAddr | ((UINT64)nPort << 32);
    }

  protected:
    ITftpSink *     m_pSink;
    UINT32          m_nAddr;
    UINT16          m_nPort;
    CTftp *         m_pNext;

    static UINT32   s_nSession;
};
//
///////////////////////////////////////////////////////////////// End of File.
