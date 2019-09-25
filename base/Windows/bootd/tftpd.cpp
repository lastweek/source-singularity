///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Contents:   Simple TFTP Daemon
//
//------------------------------------------------------------------------------

// #define DEBUG 1

#include <winlean.h>
#include <winsock.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>
#include "socksr.h"

//////////////////////////////////////////////////////////////////////////////
//
// Debugging
//

#define VERBOSE(x) if (s_fVerboseOutput) x

//#pragma warning(disable: 4127)

#define ARRAYOF(x)          (sizeof(x)/sizeof(x[0]))
#define OFFSETOF(s,m)       ((unsigned)&(((s *)0)->m))
#define assert(x)           if (!(x)) __asm int 3
#define WM_SOCKET_EVENT     (WM_USER+101)

typedef USHORT UINT16;

#include "hashtab.h"
#include "tftpd.h"

#include "hashtab.cpp"

//////////////////////////////////////////////////////////////////////////////
//

//
// Trivial File Transfer Protocol (TFTP) as per RFCs 1350, 1782, 1783 & 1784.
//

//
// Packet types and their opcodes.
//
#define TFTP_RRQ   1  // read request
#define TFTP_WRQ   2  // write request
#define TFTP_DATA  3  // data
#define TFTP_ACK   4  // acknowledgment
#define TFTP_ERROR 5  // error
#define TFTP_OACK  6  // option acknowledgment


//
// Error codes.
//
#define EUNDEF    0  // not defined, see error message (if any)
#define ENOTFOUND 1  // file not found
#define EACCESS   2  // access violation
#define ENOSPACE  3  // disk full or allocation exceeded
#define EBADOP    4  // illegal TFTP operation

//
// TFTP header structure.
//
struct TftpHdr {
    UINT16      Opcode;         // packet type
    union {
        CHAR    Options[1];     // options we accept (for OACK packets)
        UINT16  Block;          // block # (for DATA and ACK packets)
        UINT16  ErrorCode;      // error code (for ERROR packets)
    };
    CHAR        Data[1];        // data/error string

    PCSTR Dump(UINT cbData) {
        static CHAR szBuffer[2048];
        PCHAR pszBuffer = szBuffer;

        // In network order
        switch (ntohs(Opcode)) {
          default:
            sprintf(pszBuffer, "??? %04x", ntohs(Opcode));
            __asm int 3;
            return szBuffer;
          case TFTP_DATA:
            sprintf(pszBuffer, "DATA%5d %d bytes", ntohs(Block), cbData - 4);
            return szBuffer;
          case TFTP_ACK:
            sprintf(pszBuffer, "ACK %5d", ntohs(Block));
            return szBuffer;
          case TFTP_ERROR:
            sprintf(pszBuffer, "ERROR%4d %s", ntohs(ErrorCode), Data);
            return szBuffer;
          case TFTP_RRQ:
            pszBuffer += sprintf(pszBuffer, "RRQ  [");
            break;
          case TFTP_WRQ:
            pszBuffer += sprintf(pszBuffer, "WRQ  [");
            break;
          case TFTP_OACK:
            pszBuffer += sprintf(pszBuffer, "OACK [");
            break;
        }

        PCHAR pszTmp = Options;
        PCHAR pszEnd = ((PCHAR)this) + cbData;

        for (; pszTmp < pszEnd; pszTmp++) {
            if (*pszTmp) {
                *pszBuffer++ = *pszTmp;
            }
            else {
                *pszBuffer++ = '^';
            }
        }
        *pszBuffer++ = ']';
        *pszBuffer = '\0';
        return szBuffer;
    }
};

//
// With TFTP, all DATA packets except for the last one contain the same
// number of data bytes (plus four bytes of header).  Barring a "blksize"
// option in the request packet, this number is 512.
//
#define DEFAULT_BLOCKSIZE   512
#define MAX_BLOCKSIZE       8192

//
// The TFTP spec says nothing about default timeout values or retransmission
// algorithms.  RFC 1123, however, says me MUST use an adaptive timeout and
// recommends doing an exponential backoff.  To keep things simple, we start
// with DEFAULT_TIMEOUT (which client can override via "timeout" option) and
// double it for each retry up to MAX_RETRIES.  Each time we need to retransmit
// a packet to get it through, we double the initial timeout for the next and
// all successive packets.
//
// Keep DEFAULT_TIMEOUT and especially MAX_RETRIES to fairly small values
// (order 100 and order 10, respectively) or you'll break the implementation
// (and really try your patience).
//
#define DEFAULT_TIMEOUT     1  // in seconds
#define MAX_RETRIES         4

//////////////////////////////////////////////////////////////////////////////
//
CHAR s_rszRenames[64][64];
UINT s_nRenames     = 0;
UINT s_nRenamesBase = 0;
BOOL s_fRenames     = TRUE;

CHAR s_rszReadPaths[16][MAX_PATH];
CHAR s_szWritePath[MAX_PATH];
UINT s_nPaths = 0;

BOOL s_fExitOnENotFound = FALSE;
BOOL s_fVerboseOutput   = FALSE;

//////////////////////////////////////////////////////////////////////////////
//
// Structure for handing incoming requests off to per-connection threads.
//
class CTftpNode : public ITimerSink,
                  public ISessionSink
{
  public:
    CTftpNode(ISessionSource *pSource, ITftpSink *pEventSink,
              UINT32 nAddr, UINT16 nPort, UINT32 nSession);
    ~CTftpNode();

    UINT    CheckAndOpenFile(PCHAR pszName, HANDLE *phFile);
    UINT    CheckAndCreateFile(PCHAR pszName, BOOL fWrite, HANDLE *phFile);

    // Events:
    VOID    ResendPacket(BOOL fTimeout);
    VOID    ReadFinished(DWORD dwErrorCode, DWORD dwDone);

    // ISessionSink
  public:
    virtual VOID    OnSessionCreate(ISessionSource *pSource, PVOID pvContext);
    virtual VOID    OnSessionRecv(UINT dwError, PBYTE pbData, UINT cbRcvd);
    virtual VOID    OnSessionClose(UINT dwError);

  public:
    // ITimerSink:
    virtual VOID OnTimerFired();

  protected:
    // Subroutines:
    VOID    Ack(UINT16 nBlock);
    VOID    Nak(UINT16 nErrorCode);
    VOID    OAck();
    VOID    Data(UINT16 nBlock, PVOID pvPacket, UINT cbData);

    VOID    SetTimeout();
    VOID    ClrTimeout();

    UINT    SocketSend(PVOID pbData, UINT cbData);
    BOOL    ReadBlock(UINT nBlock);
    BOOL    WriteBlock(INT cbData);
    VOID    WriteFinished(DWORD dwErrorCode, DWORD dwDone);

    BOOL    IsActiveSession()       { return m_szFilename[0] != '\0'; }
    VOID    DeactivateSession();

    VOID    Log(PCSTR pszMsg, ...);

    BOOL    ValidateName(PCHAR pszDst, PCHAR pszSrc);

    static VOID CALLBACK ReadCallback(DWORD dwErr, DWORD dwDone, LPOVERLAPPED lpOvrlap);
    static VOID CALLBACK WriteCallback(DWORD dwErrorCode, DWORD dwDone, LPOVERLAPPED lpOverlap);

  public:
    UINT32  m_nSession;

  protected:
    ISessionSource *    m_pSource;
    ITftpSink *         m_pEventSink;

    UINT32  m_nAddr;
    UINT16  m_nPort;
    HANDLE  m_hFile;
    CHAR    m_szFilename[MAX_PATH];

    BOOL    m_fWrite;
    BOOL    m_fDone;
    BOOL    m_fUseOack;
    BOOL    m_fHadTsize;
    UINT    m_cbFileSize;

    UINT    m_cbBlock;
    UINT    m_cbBlockOpt;
    UINT    m_cbBlockRead;

    UINT    m_nTimeout;
    UINT    m_nTimeoutOpt;
    UINT    m_nTimeoutCount;
    UINT    m_nTimeoutValue;
    BOOL    m_fTimedOut;        // Set if a timeout was triggered since last recv.

    // n_nBlock the next block to read and wait for ACK.
    UINT16  m_nBlock;
    UINT32  m_nBlockLogLow;
    UINT32  m_nBlockLogHigh;

    BOOL    m_fIoDone;
    UINT    m_nIoOffset;
    BYTE    m_bIoBuffer[MAX_BLOCKSIZE + OFFSETOF(TftpHdr, Data)];

    OVERLAPPED m_Overlapped;
};

//////////////////////////////////////////////////////////////////////////////
//
CTftpNode::CTftpNode(ISessionSource *pSource, ITftpSink *pEventSink,
                     UINT32 nAddr, UINT16 nPort, UINT32 nSession)
    : m_pSource(pSource),
      m_pEventSink(pEventSink),
      m_nAddr(nAddr),
      m_nPort(nPort),
      m_nSession(nSession)
{
    m_szFilename[0] = '\0';
    m_hFile = INVALID_HANDLE_VALUE;
    m_nTimeout = DEFAULT_TIMEOUT;
    m_fUseOack = FALSE;
    m_fTimedOut = FALSE;
}

CTftpNode::~CTftpNode()
{
    ClrTimeout();
}

UINT CTftpNode::CheckAndCreateFile(PCHAR pszName, BOOL fWrite, HANDLE *phFile)
{
    *phFile = INVALID_HANDLE_VALUE;

    // Set the access and creation flags.
    //
    DWORD dwAccess;
    DWORD dwShare;
    DWORD dwCreation;
    PCHAR pszOp;

    if (fWrite) {
        dwAccess = GENERIC_WRITE;
        dwShare = 0 // don't let others see inconsistent file   
            /*FILE_SHARE_READ | FILE_SHARE_WRITE*/;
        dwCreation = CREATE_ALWAYS;
        pszOp = "write";

        if (s_szWritePath[0] == '\0') {
            // Writes not allowed
            goto fail;
        }

        // Writes are only allowed to the write path.
        CHAR szPath[MAX_PATH];

        strcpy(szPath, s_szWritePath);
        strcat(szPath, pszName);

        *phFile = CreateFile(szPath, dwAccess, dwShare, NULL, dwCreation,
                             FILE_FLAG_SEQUENTIAL_SCAN | FILE_FLAG_OVERLAPPED, NULL);

        if (*phFile != INVALID_HANDLE_VALUE) {
            Log("   %02d Write `%s'", m_nSession, szPath);
            return 0;
        }
    }
    else {
        dwAccess = GENERIC_READ;
        dwShare = FILE_SHARE_READ;
        dwCreation = OPEN_EXISTING;
        pszOp = "read";

        // Reads are allowed for any path.

        for (UINT n = 0; n < s_nPaths; n++)
        {
            CHAR szPath[MAX_PATH];

            strcpy(szPath, s_rszReadPaths[n]);
            strcat(szPath, pszName);

            *phFile = CreateFile(szPath, dwAccess, dwShare, NULL, dwCreation,
                                 FILE_FLAG_SEQUENTIAL_SCAN | FILE_FLAG_OVERLAPPED, NULL);

            if (*phFile != INVALID_HANDLE_VALUE) {
                Log("   %02d Read `%s'", m_nSession, szPath);
                return 0;
            }
        }
    }
  fail:
    Log("   %02d Failed %s `%s'", m_nSession, pszOp, pszName);
    return EACCESS;
}

UINT CTftpNode::CheckAndOpenFile(PCHAR pszName, HANDLE *phFile)
{
    *phFile = INVALID_HANDLE_VALUE;

    for (UINT n = 0; n < s_nPaths; n++)
    {
        CHAR szPath[MAX_PATH * 2];

        strcpy(szPath, s_rszReadPaths[n]);
        strcat(szPath, pszName);

        *phFile = CreateFile(szPath, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING,
                             FILE_FLAG_SEQUENTIAL_SCAN | FILE_FLAG_OVERLAPPED, NULL);

        if (*phFile != INVALID_HANDLE_VALUE) {
            Log("   %02d Read `%s'", m_nSession, szPath);
            return 0;
        }
    }
    Log("   %02d Failed read `%s'", m_nSession, pszName);
    return EACCESS;
}

VOID CTftpNode::OnSessionCreate(ISessionSource *pSource, PVOID pvContext)
{
    (void)pvContext;

    m_pSource = pSource;
}

VOID CTftpNode::OnSessionClose(UINT dwError)
{
    (void)dwError;
    VERBOSE(Log("   %02d close session: %d.", m_nSession, dwError));

    delete this;
}

VOID CTftpNode::Log(PCSTR pszMsg, ...)
{
    if (m_pEventSink) {
        CHAR szBuffer[2048];
        va_list args;

        va_start(args, pszMsg);
        vsprintf(szBuffer, pszMsg, args);
        va_end(args);

        m_pEventSink->OnTftpMessage(m_nAddr, "%s", szBuffer);
    }
}

UINT CTftpNode::SocketSend(PVOID pbData, UINT cbData)
{
    TftpHdr *pPacket = (TftpHdr*)pbData;

    if (ntohs(pPacket->Opcode) == TFTP_DATA) {
        UINT16 nBlock = ntohs(pPacket->Block);

        if (nBlock <= m_nBlockLogLow || nBlock >= m_nBlockLogHigh ||
            nBlock % 250 == 0 || m_fTimedOut) {
            Log("<= %02d %s%s", m_nSession, pPacket->Dump(cbData),
                m_fTimedOut ? " [Resend]" : "");
        }
    }
    else {
        Log("<= %02d %s", m_nSession, pPacket->Dump(cbData));
    }

    return m_pSource->SessionSend((PBYTE)pbData, cbData);
}

VOID CTftpNode::DeactivateSession()
{
    if (m_szFilename[0]) {
        VERBOSE(Log("-- %02d DeactivateSession", m_nSession));

        m_szFilename[0] = 0;
        if (m_hFile != INVALID_HANDLE_VALUE) {
            CancelIo(m_hFile);
            CloseHandle(m_hFile);
            m_hFile = INVALID_HANDLE_VALUE;
        }
        SetTimeout();
    }
}

BOOL CTftpNode::ReadBlock(UINT nBlock)
{
    (void)nBlock;

    VERBOSE(Log("   %02d ReadBlock(%d at %d)",
                m_nSession, nBlock, m_nIoOffset));

    m_fIoDone = FALSE;
    m_Overlapped.hEvent = (HANDLE)this;
    m_Overlapped.Offset = m_nIoOffset;
    m_Overlapped.OffsetHigh = 0;

    if (!ReadFileEx(m_hFile, m_bIoBuffer + OFFSETOF(TftpHdr, Data),
                    m_cbBlock, &m_Overlapped, ReadCallback)) {
        ReadFinished(GetLastError(), 0);
        return FALSE;
    }
    return TRUE;
}

VOID CTftpNode::ReadFinished(DWORD dwErrorCode, DWORD dwDone)
{
    VERBOSE(Log("   %02d ReadFinished(%d, %d)",
                m_nSession, dwErrorCode, dwDone));

    m_fIoDone = TRUE;
    m_nIoOffset += dwDone;
    m_cbBlockRead = dwDone;

    if (dwErrorCode == ERROR_HANDLE_EOF) {
        dwErrorCode = 0;
    }

    if (dwErrorCode != 0) {
        VERBOSE(Log("   %02d Read failed: %d", m_nSession, dwErrorCode));
        Nak(ENOSPACE);
    }
    else {
        ResendPacket(FALSE);
    }
}

VOID CTftpNode::ReadCallback(DWORD dwErrorCode, DWORD dwDone, LPOVERLAPPED lpOverlap)
{
    CTftpNode *pInfo = (CTftpNode *)lpOverlap->hEvent;
    pInfo->ReadFinished(dwErrorCode, dwDone);
}

BOOL CTftpNode::WriteBlock(INT cbData)
{
    m_fIoDone = FALSE;
    m_Overlapped.hEvent = (HANDLE)this;
    m_Overlapped.Offset = m_nIoOffset;
    m_Overlapped.OffsetHigh = 0;

    if (cbData == 0) {
        WriteFinished(0, 0);
    }
    else if (!WriteFileEx(m_hFile, m_bIoBuffer, cbData, &m_Overlapped, WriteCallback)) {
        WriteFinished(GetLastError(), 0);
        return FALSE;
    }
    return TRUE;
}

VOID CTftpNode::WriteFinished(DWORD dwErrorCode, DWORD dwDone)
{
    VERBOSE(Log("%08x WriteFinished(%d, %d)\n", this, dwErrorCode, dwDone));

    m_fIoDone = TRUE;
    m_nIoOffset += dwDone;

    if (dwErrorCode != 0) {
        VERBOSE(Log("%08x Write failed: %d\n", this, dwErrorCode));
        Nak(ENOSPACE);
    }
    else {
        m_nBlock++;
    }
    if (dwDone < 512) {
        m_fDone = TRUE;
    }

    ResendPacket(FALSE);
}

VOID CTftpNode::WriteCallback(DWORD dwErrorCode, DWORD dwDone, LPOVERLAPPED lpOverlap)
{
    CTftpNode *pInfo = (CTftpNode *)lpOverlap->hEvent;
    pInfo->WriteFinished(dwErrorCode, dwDone);
}


VOID CTftpNode::OnTimerFired()
{
    if (!m_fDone) {
        ResendPacket(TRUE);
    }
}

VOID CTftpNode::SetTimeout()
{
    if (m_nTimeoutValue == 0) {
        m_nTimeoutCount = 0;
        m_nTimeoutValue = m_nTimeout;
    }
    TimerSet(this, m_nTimeoutValue * 1000);
}

VOID CTftpNode::ClrTimeout()
{
    m_nTimeoutValue = 0;
    TimerClr(this);
}

//
// Send an TFTP_ACK packet.
//
VOID CTftpNode::Ack(UINT16 nBlock)
{
    BYTE Buffer[8];
    TftpHdr *pPacket = (TftpHdr *)Buffer;

    pPacket->Opcode = htons((UINT16)TFTP_ACK);
    pPacket->Block = htons(nBlock);
    SocketSend(pPacket, OFFSETOF(TftpHdr, Data));
    SetTimeout();
}

//
// Send a TFTP_DATA packet
//
VOID CTftpNode::Data(UINT16 nBlock, PVOID pvPacket, UINT cbData)
{
    TftpHdr *pPacket = (TftpHdr *)pvPacket;

    pPacket->Opcode = htons((UINT16)TFTP_DATA);
    pPacket->Block = htons(nBlock);
    SocketSend(pPacket, cbData + OFFSETOF(TftpHdr, Data));
    SetTimeout();
}

//
// Send a TFTP_NAK packet (i.e. an error message).
// Error code passed in is one of the standard TFTP codes,
//
VOID CTftpNode::Nak(UINT16 nErrorCode)
{
    BYTE Buffer[512];
    TftpHdr *pPacket = (TftpHdr *)Buffer;

    pPacket->Opcode = htons((UINT16)TFTP_ERROR);
    pPacket->ErrorCode = htons(nErrorCode);
    pPacket->Data[0] = '\0';

    //
    // Convert error code into the appropriate ASCII string message.
    //
    PCHAR pszError = "Undetermined error";

    switch (nErrorCode) {
      case ENOTFOUND: pszError = "File not found"; break;
      case EACCESS:   pszError = "Access violation"; break;
      case ENOSPACE:  pszError = "Disk full or allocation exceeded"; break;
      case EBADOP:    pszError = "Illegal TFTP operation"; break;
    }
    strcpy(pPacket->Data, pszError);

    INT cbData = OFFSETOF(TftpHdr, Data) + strlen(pPacket->Data) + 1;
    SocketSend(pPacket, cbData);

    VERBOSE(Log("   %02d Nak'd with errorcode %d (%s).",
                m_nSession, nErrorCode, pPacket->Data));

    if (m_pEventSink) {
        m_pEventSink->OnTftpAccessEnd(m_nAddr, m_nPort, 0);
    }

    // We don't call SetTimeout here because DeactivateSession does.
    DeactivateSession();

    if (s_fExitOnENotFound && nErrorCode == ENOTFOUND) {
        fflush(stdout);
        ExitProcess(ENOTFOUND);
    }
}

//
// Send a oack (option acknowledgment) packet.
// Non-zero options passed in are valid.
//
VOID CTftpNode::OAck()
{
    BYTE Buffer[2048];
    TftpHdr *pPacket;
    int cbData = 0;

    pPacket = (TftpHdr *)Buffer;
    pPacket->Opcode = htons((UINT16)TFTP_OACK);

    //
    // Convert Option/Value pairs into the appropriate ASCII string messages.
    //
    if (m_cbBlockOpt) {
        cbData += sprintf(pPacket->Options + cbData, "blksize") + 1;
        cbData += sprintf(pPacket->Options + cbData, "%d", m_cbBlockOpt) + 1;
    }
    if (m_nTimeoutOpt) {
        cbData += sprintf(pPacket->Options + cbData, "timeout") + 1;
        cbData += sprintf(pPacket->Options + cbData, "%d", m_nTimeoutOpt) + 1;
    }
    if (m_fHadTsize) {
        cbData += sprintf(pPacket->Options + cbData, "tsize") + 1;
        cbData += sprintf(pPacket->Options + cbData, "%d", m_cbFileSize) + 1;
    }

    SocketSend(Buffer, cbData + OFFSETOF(TftpHdr, Options));
    SetTimeout();

    VERBOSE(Log("   %02d OAck sent (%d bytes)", m_nSession, cbData));
}

//////////////////////////////////////////////////////////////////////////////
//
VOID CTftpNode::ResendPacket(BOOL fTimeout)
{
    if (fTimeout) {
        VERBOSE(Log("   %02d timeout (count=%d, value=%d)",
                m_nSession, m_nTimeoutCount, m_nTimeoutValue));

        m_nTimeoutValue *= 2;
        if (m_fDone || ++m_nTimeoutCount > MAX_RETRIES) {
            if (IsActiveSession()) {
                VERBOSE(Log("   %02d too many retries, aborting session",
                            m_nSession));
                Nak(EUNDEF);
            }

            // Close the session!
            m_pSource->SessionClose(0);
            return;
        }
    }
#if 0
    if (!IsActiveSession()) {
        SetTimeout();
        return;
    }
    else if (m_nBlock == 0 && m_nIoOffset == 0) {
        if (m_cbBlockOpt || m_nTimeoutOpt) {
            //
            // Need to send OACK packet to acknowledge options we accept.
            //
            // If client is making a read request, wait for an ack to our oack
            // to arrive (it should acknowledge block 0).  If client is making
            // a write request, wait for the first data packet to arrive.  In
            // either case, if we timeout before anything arrives, resend oack.
            //
            OAck(); //m_cbBlockOpt, m_nTimeoutOpt);
        }
        else {
            //
            // Need to acknowledge request with an ack for block 0
            // since we didn't send an oack.  RecvData() will handle
            // any retransmission that may be required of this ack.
            //
            Ack(0);
        }
    }
    else {
        if (m_fWrite) {
            printf(" Write: acking block %d\n",m_nBlock);
            Ack(m_nBlock);
        }
        else {
            Data(m_nBlock, m_bIoBuffer, m_cbBlockRead);
        }
    }
#endif
#if 1
    //printf(" m_nBlock=%d, m_nIoOffset=%d,m_fUseOack=%d,m_fWrite=%d\n",
    //        m_nBlock, m_nIoOffset, m_fUseOack,m_fWrite);

    if (!IsActiveSession()) {
        SetTimeout();
        return;
    }

    if (fTimeout) {
        m_fTimedOut = TRUE;
    }

    if (m_nBlock == 0 && m_nIoOffset == 0) {
        if (m_fUseOack) {
            //printf("Oacking\n");
            OAck();
            return;
        }
        else if (m_fWrite) {
            Ack(m_nBlock);
            return;
        }
    }
    else if (m_fWrite) {
        Ack(m_nBlock);
        return;
    }
    else if (m_fIoDone) {
        //printf("m_fIoDone\n");
        Data(m_nBlock, m_bIoBuffer, m_cbBlockRead);
        return;
    }
    else {
        // we only get here if we timed out, but the read also hasn't completed.
        Log("   %02d timeout with read pending (block=%d, count=%d, value=%d)",
            m_nSession, m_nBlock, m_nTimeoutCount, m_nTimeoutValue);
    }
#endif
}

BOOL CTftpNode::ValidateName(PCHAR pszDst, PCHAR pszSrc)
{
    PCHAR pszBeg = pszDst;

    // Remove leading '/'.
    //
    while (*pszSrc == '/' || *pszSrc == '\\') {
        // pszSrc++;
        return FALSE;
    }

    // Check for invalid characters, and copy string.
    //
    while (*pszSrc) {
        // Don't allow drive letters followed by colons.
        //
        if (*pszSrc == ':') {
            return FALSE;
        }

        // Don't allow "./" or "../" in file name.
        //
        if (pszDst == pszBeg || pszDst[-1] == '\\') {
            if ((pszSrc[0] == '.' && pszSrc[1] == '/') ||
                (pszSrc[0] == '.' && pszSrc[1] == '\\') ||
                (pszSrc[0] == '.' && pszSrc[1] == '.' && pszSrc[2] == '/') ||
                (pszSrc[0] == '.' && pszSrc[1] == '.' && pszSrc[2] == '\\')) {
                return FALSE;
            }
        }

        if (*pszSrc == '/') {
            *pszDst++ = '\\';
            pszSrc++;
        }
        else {
            *pszDst++ = *pszSrc++;
        }
    }
    *pszDst++ = '\0';

    if (s_fRenames) {
        if (strncmp(pszBeg, "pxe.com.", 8) == 0) {
            UINT n = atoi(pszBeg + 8);

            if (n != 0 && n >= s_nRenamesBase && n < s_nRenamesBase + s_nRenames) {
                strcpy(pszBeg, s_rszRenames[n - s_nRenamesBase]);
            }
        }
    }
    return TRUE;
}

VOID CTftpNode::OnSessionRecv(UINT dwError, PBYTE pbData, UINT cbData)
{
    (void)dwError;

    TftpHdr *pPacket = (TftpHdr *)pbData;

    UINT16 nOpcode = ntohs(pPacket->Opcode);
    UINT16 nBlock = ntohs(pPacket->Block);

    if (nOpcode == TFTP_ACK) {
        if (nBlock <= m_nBlockLogLow || nBlock >= m_nBlockLogHigh ||
            nBlock % 250 == 0 || m_fTimedOut) {
            Log("=> %02d %s%s", m_nSession, pPacket->Dump(cbData),
                m_fTimedOut ? " [Resend]" : "");
        }
    }
    else {
        Log("=> %02d %s", m_nSession, pPacket->Dump(cbData));
    }
    m_fTimedOut = FALSE;

    if (nOpcode == TFTP_RRQ  || nOpcode == TFTP_WRQ) {
        //
        // Abort an existing session if there is one.
        //
        DeactivateSession();

        //
        // Set initial variables...
        //
        m_fWrite = (nOpcode == TFTP_WRQ);
        m_fDone = FALSE;
        m_szFilename[0] = '\0';
        m_cbBlock = DEFAULT_BLOCKSIZE;
        m_cbBlockOpt = 0;
        m_nTimeout = DEFAULT_TIMEOUT;
        m_nTimeoutOpt = 0;
        m_fHadTsize = FALSE;
        m_cbFileSize = 0;

        //
        // Parse request fields (filename mode [option1 value1[opt2 val2 [...]]]).
        // Note: all matches (including filename!) are case-insensitive.
        //
        PCHAR pszVal;
        PCHAR pszEnd = (PCHAR)pbData + cbData;

        PCHAR pszOpt = pPacket->Options;
        PCHAR pszTmp = pszOpt + strlen(pszOpt) + 1;
        if (pszTmp > pszEnd || !ValidateName(m_szFilename, pszOpt)) {
            if (m_pEventSink) {
                m_pEventSink->OnTftpAccessBegin(m_nAddr, m_nPort, m_fWrite, "<illegal>");
            }

            VERBOSE(Log("   %02d formatted filename packet", m_nSession));
            Nak(ENOTFOUND);
            return;
        }
        else {
            if (m_pEventSink) {
                m_pEventSink->OnTftpAccessBegin(m_nAddr, m_nPort, m_fWrite, pszOpt);
            }
        }

        pszOpt = pszTmp;
        pszTmp += strlen(pszTmp) + 1;
        if (pszTmp <= pszEnd) {
            // Note: we always use binary.
            if (_stricmp("octet", pszOpt) != 0 && _stricmp("netascii", pszOpt) != 0) {
                // Unknown recognized mode.
                Nak(EBADOP);
                return;
            }
        }

        while (pszTmp < pszEnd) {
            pszOpt = pszTmp;
            pszTmp += strlen(pszTmp) + 1;
            if (pszTmp >= pszEnd) {
                break;
            }
            pszVal = pszTmp;
            pszTmp += strlen(pszTmp) + 1;
            if (pszTmp > pszEnd) {
                break;
            }

            if (_stricmp(pszOpt, "blksize") == 0) {
                //
                // "blksize" option: (#octets).
                //
                m_cbBlockOpt = min(max(atoi(pszVal), 8), MAX_BLOCKSIZE);
                m_cbBlock = m_cbBlockOpt;
                m_fUseOack = TRUE;
                VERBOSE(Log("   %02d blksize: %d", m_nSession, m_cbBlockOpt));
            }
            else if (_stricmp(pszOpt, "timeout") == 0) {
                //
                // End of "timeout" option value string (#seconds).
                //
                m_nTimeoutOpt = min(max(atoi(pszVal), 1), 10);
                m_nTimeout = m_nTimeoutOpt;
                m_fUseOack = TRUE;
                VERBOSE(Log("   %02d timeout: %d", m_nSession, m_nTimeoutOpt));
            }
            else if (_stricmp(pszOpt, "tsize") == 0) {
                //
                // "tsize" transmit option value string (#size).
                //
                m_fHadTsize = 1;
                m_fUseOack = TRUE;
                VERBOSE(Log("   %02d tsize: %d", m_nSession, atoi(pszVal)));
            }
            else {
                // Just ignore the unknown option.
                VERBOSE(Log("   %02d unknown option: `%s'",
                            m_nSession, pszOpt));
            }
        }

        if (pszTmp > pszEnd) {
            //
            // Buffer overrun on packet.
            //
            VERBOSE(Log("   %02d badly formatted request packet", m_nSession));
            Nak(EBADOP);
            return;
        }

        //
        // Open the file.
        //
        // PBAR       UINT nErr = CheckAndOpenFile(m_szFilename, &m_hFile);
        UINT nErr = CheckAndCreateFile(m_szFilename, m_fWrite, &m_hFile);

        if (nErr != 0) {
            Nak((UINT16)nErr);
            return;
        }

        m_cbFileSize = GetFileSize(m_hFile, NULL);
        if (m_cbFileSize < 0) {
            m_cbFileSize = 0;
        }
        VERBOSE(Log("   %02d File is %d bytes or %d blocks.",
                    m_nSession, m_cbFileSize,
                    (m_cbFileSize + m_cbBlock - 1) / m_cbBlock));

        //
        // Set final variables...
        //
        m_nTimeoutValue = 0;
        m_nTimeoutCount = 0;
        m_cbBlockRead = m_cbBlock;
        m_fIoDone = TRUE;
        m_nIoOffset = 0;
        m_nBlockLogLow = 3;
        m_nBlockLogHigh = (m_cbFileSize / m_cbBlockRead) - 3;
        m_nBlockLogHigh = m_nBlockLogHigh <= 0 ? 0 : m_nBlockLogHigh;

        if (m_fUseOack) {
            m_nBlock = 0;
            ResendPacket(FALSE);
        }
        else if (m_fWrite) {
            m_nBlock = 0;
            ResendPacket(FALSE);
        }
        else {
            m_nBlock = 1;
            ReadBlock(0);
        }
    }
    else if (nOpcode == TFTP_DATA ||
             nOpcode == TFTP_ACK ||
             nOpcode == TFTP_ERROR ||
             nOpcode == TFTP_OACK) {

        if (!IsActiveSession()) {
            return;
        }

        if (m_szFilename[0] == '\0') {
            // Ignore packets if we don't have an active session.
            return;
        }

        if (nOpcode == TFTP_ERROR) {
            VERBOSE(Log("   %02d Client reports error (code %d): %s",
                    m_nSession, nBlock, pPacket->Data));
            DeactivateSession();
            return;
        }

        if (m_fWrite) {
            // Write requests...
            //
            printf("WRITE\n");
            if (nOpcode == TFTP_DATA) {
                printf("DATA\n");
                if (nBlock == (UINT16)(m_nBlock + 1)) {
                    printf("NEXT\n");
                    VERBOSE(Log("   %02d got data block %d (%d bytes)\n",
                            m_nSession, m_nBlock,
                                cbData - OFFSETOF(TftpHdr, Data)));
                    printf("   %02d got data block %d (%d bytes)\n",
                           m_nSession, m_nBlock,
                           cbData - OFFSETOF(TftpHdr, Data));

                    if (m_fIoDone) {
                        m_cbBlockRead = cbData - OFFSETOF(TftpHdr, Data);
                        //printf("WRITEBLOCK\n");
                        // Buffer is available, initiate the write.
                        CopyMemory(m_bIoBuffer, pPacket->Data, m_cbBlockRead);
                        WriteBlock(m_cbBlockRead);
                    }
                    else {
                        // Client will either re-send the packet either on timeout,
                        // or when we ACK the last packet.
                        //printf("NOWRITE\n");
                    }
                }
                else if (nBlock == m_nBlock) {
                    //printf("SAME\n");
                    // If we got the same block, then we resend our ACK.
                    ResendPacket(FALSE);
                }
                else {
                    VERBOSE(Log("   %02d Strange ACK %d to %d\n",
                                m_nSession, nBlock, m_nBlock));
                    Nak(EBADOP);
                    return;
                }
            }
            else {
                // Write streams from clients only contain TFTP_DATA packets.
                VERBOSE(Log("   %02d aborting due to weird packet when expecting data.\n",
                            m_nSession));
                Nak(EBADOP);
                return;
            }
        }
        else {

            // Read requests...
            //
            if (nOpcode == TFTP_ACK) {
                if (nBlock == m_nBlock) {
                    // Client ACK'd our packet, read the next block.
                    if (m_cbBlockRead == m_cbBlock) {
                        ReadBlock(++m_nBlock);
                    }
                    else {
                        // Client ACK'd our last packet, we're out of here.
                        if (m_pEventSink) {
                            m_pEventSink->OnTftpAccessEnd(m_nAddr, m_nPort, TRUE);
                        }
                        DeactivateSession();
                    }
                }
                else if (nBlock == (UINT16)(m_nBlock - 1)) {
                    // Client ACK'd the previous block, resend it.
                    ResendPacket(FALSE);
                }
                else {
                    VERBOSE(Log("   %02d Strange ACK %d to %d",
                                m_nSession, nBlock, m_nBlock));
                    Nak(EBADOP);
                    return;
                }
            }
            else {
                // Read streams from clients only contain TFTP_ACK packets.
                VERBOSE(Log("   %02d aborting due to weird packet when expecting data.",
                        m_nSession));
                Nak(EBADOP);
                return;
            }
        }
    }
    else {
        VERBOSE(Log("   %02d bogus following opcode (%d)",
                    m_nSession, nOpcode));
        DeactivateSession();
        return;
    }
}

//////////////////////////////////////////////////////////////////////////////
//
UINT32 CTftp::s_nSession = 1;

CTftp::CTftp(CTftp *pNext)
{
    m_pNext = pNext;
    m_pSink = NULL;
    m_nAddr = 0;
    m_nPort = 0;
}

CTftp::~CTftp()
{
    if (m_pNext) {
        delete m_pNext;
        m_pNext = NULL;
    }

    if (m_pSink) {
        m_pSink->OnTftpMessage(m_nAddr, "Server stopped.");
    }

    m_pSink = NULL;
}

static BOOL CheckDir(PCHAR pszDir)
{
    if (pszDir == NULL || pszDir[0] == '\0') {
        return FALSE;
    }

    PCHAR pszBeg = pszDir;

    while (*pszDir) {
        pszDir++;
    }
    if (pszDir > pszBeg && pszDir[-1] != '\\') {
        *pszDir++ = '\\';
        *pszDir = '\0';
    }
    return TRUE;
}

VOID CTftp::OnNetworkChange(UINT32 nAddr, UINT32 nMask, UINT32 nGate)
{
    if (m_nAddr == nAddr) {
    }
    if (m_pNext) {
        m_pNext->OnNetworkChange(nAddr, nMask, nGate);
    }
}

VOID CTftp::OnNetworkDelete(UINT32 nAddr, CTftp **ppNext)
{
    if (m_nAddr == nAddr) {
        *ppNext = m_pNext;

        if (m_pNext) {
            m_pNext->OnNetworkDelete(nAddr, ppNext);
        }
        m_pNext = NULL;

        delete this;
    }
    else {
        if (m_pNext) {
            m_pNext->OnNetworkDelete(nAddr, &m_pNext);
        }
    }
}

VOID CTftp::ConfigureFiles(ITftpSink *pSink, INT argc, PCHAR *argv)
{
    for (INT arg = 0; arg < argc; arg++) {
        if (argv[arg][0] == '-' || argv[arg][0] == '/') {
            CHAR args[1024];
            strcpy(args, argv[arg]);
            char *argn = args+1;                        // Argument name
            char *argp = argn;                          // Argument parameter

            while (*argp && *argp != ':') {
                argp++;
            }
            if (*argp == ':') {
                *argp++ = '\0';
            }

            switch (argn[0]) {
              case 'e':                                 // Exit on first ENOTFOUND
              case 'E':
                s_fExitOnENotFound = TRUE;
                break;
              case 'r':                                 // Disable rename.
              case 'R':
                s_fRenames = FALSE;
                break;
              case 'v':
              case 'V':
                s_fVerboseOutput = TRUE;
                break;
              case 'w':                                 // Allow writes.
              case 'W':
                strcpy(s_szWritePath, argp);
                if (pSink) {
                    pSink->OnTftpMessage(0, "Write: %s", argp);
                }
                if (s_nPaths < ARRAYOF(s_rszReadPaths)) {
                    strcpy(s_rszReadPaths[s_nPaths], argv[arg]);
                    if (CheckDir(s_rszReadPaths[s_nPaths])) {
                        s_nPaths++;
                    }
                }
                break;
            }
        }
        else {
            if (s_nPaths < ARRAYOF(s_rszReadPaths)) {
                strcpy(s_rszReadPaths[s_nPaths], argv[arg]);
                if (CheckDir(s_rszReadPaths[s_nPaths])) {
                    if (pSink) {
                        pSink->OnTftpMessage(0, "Read: %s",
                                             s_rszReadPaths[s_nPaths]);
                    }
                    s_nPaths++;
                }
            }
        }
    }
    if (s_fRenames) {
        OnFilesChange(pSink);
    }
}

VOID CTftp::OnFilesChange(ITftpSink *pSink)
{
    s_nRenames = 0;
    s_nRenamesBase = 0;

    // First, could the pxe.com files:
    for (UINT nPath = 0; nPath < s_nPaths; nPath++) {
        CHAR szPath[MAX_PATH];
        WIN32_FIND_DATA wfd;

        strcpy(szPath, s_rszReadPaths[nPath]);
        strcat(szPath, "pxe.com.*");

        HANDLE hFind = FindFirstFile(szPath, &wfd);
        while (hFind != INVALID_HANDLE_VALUE) {
            if ((wfd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == 0) {
                if (strlen(wfd.cFileName) > 8) {
                    UINT num = atoi(wfd.cFileName + 8);
                    if (s_nRenamesBase <= num) {
                        s_nRenamesBase = num + 1;
                    }
                }
            }

            if (!FindNextFile(hFind, &wfd)) {
                FindClose(hFind);
                break;
            }
        }
    }

    // Then see what files we can rename.
    for (UINT nPath = 0; nPath < s_nPaths; nPath++) {
        CHAR szPath[MAX_PATH];
        WIN32_FIND_DATA wfd;

        strcpy(szPath, s_rszReadPaths[nPath]);
        strcat(szPath, "*.x86");

        HANDLE hFind = FindFirstFile(szPath, &wfd);
        while (hFind != INVALID_HANDLE_VALUE) {
            if ((wfd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) != 0) {
                goto next;
            }

            strcpy(szPath, s_rszReadPaths[nPath]);
            strcat(szPath, wfd.cFileName);

            if (s_nRenames >= ARRAYOF(s_rszRenames)) {
                goto next;
            }

            HANDLE hFile = CreateFile(szPath, GENERIC_READ, FILE_SHARE_READ, NULL,
                                      OPEN_EXISTING, FILE_FLAG_SEQUENTIAL_SCAN, NULL);
            if (hFile == INVALID_HANDLE_VALUE) {
                goto next;
            }

            CHAR rbBlock[512];
            DWORD dwRead = 0;
            if (ReadFile(hFile, rbBlock, sizeof(rbBlock), &dwRead, NULL) &&
                dwRead == sizeof(rbBlock)) {

                if (rbBlock[0] = 'M' && rbBlock[1] == 'Z' &&
                    *(DWORD*)&rbBlock[64] == 0) {

                    sprintf(s_rszRenames[s_nRenames], "%ls", &rbBlock[68]);
                    if (pSink) {
                        pSink->OnTftpMessage(0, "Rename pxe.com.%d to %s",
                                             s_nRenamesBase + s_nRenames,
                                             s_rszRenames[s_nRenames]);
                    }
                    s_nRenames++;
                }
            }
            CloseHandle(hFile);

          next:
            if (!FindNextFile(hFind, &wfd)) {
                FindClose(hFind);
                break;
            }
        }
    }
}

VOID CTftp::Configure(UINT32 nAddr, UINT16 nPort,
                      ITftpSink *pSink, INT argc, PCHAR *argv)
{
    m_pSink = pSink;
    m_nAddr = nAddr;
    m_nPort = nPort;

    for (INT arg = 0; arg < argc; arg++) {
        if (argv[arg][0] == '-' || argv[arg][0] == '/') {
            CHAR args[1024];
            strcpy(args, argv[arg]);
            char *argn = args+1;                        // Argument name
            char *argp = argn;                          // Argument parameter

            while (*argp && *argp != ':') {
                argp++;
            }
            if (*argp == ':') {
                *argp++ = '\0';
            }

            switch (argn[0]) {
              case '?':
                break;
            }
        }
    }
    if (m_pSink) {
        m_pSink->OnTftpMessage(0,
                               "TFTP Server: %s:%d",
                               SocketToString(m_nAddr), m_nPort);
    }
}

//////////////////////////////////////////////////////////////////////////////
//
VOID CTftp::OnSessionCreate(UINT32 nPeerAddr,
                            UINT16 nPeerPort,
                            ISessionSource *pSource,
                            ISessionSink **ppSink,
                            PVOID pvContext)
{
    (void)pvContext;

    *ppSink = new CTftpNode(pSource, m_pSink, nPeerAddr, nPeerPort, s_nSession++);
}

VOID CTftp::OnFactoryRecv(UINT dwError,
                          UINT32 nAddr, UINT16 nPort, PBYTE pbData, UINT cbData)
{
    if (dwError) {
        m_pSink->OnTftpSocketError(dwError);
        return;
    }

    // Drop anything that clearly isn't a valid TFTP request packet.
    //
    if (cbData < OFFSETOF(TftpHdr, Data)) {
        VERBOSE(Log(nAddr, "<= packet port %d too small (%d bytes)",
                    nPort, cbData));
        return;
    }

    // If we receive then their wasn't a client for this packet.

    TftpHdr *pPacket = (TftpHdr *)pbData;
    UINT16 nOpcode = ntohs(pPacket->Opcode);
    if (nOpcode != TFTP_RRQ) {
        VERBOSE(Log(nAddr, "<= packet from port %d wrong initial opcode (%d)",
                    nPort, nOpcode));
        return;
    }

    // New request.
    ISessionSink *pSession = NULL;
    FactorySessionCreate(nAddr, nPort, &pSession, NULL);
    CTftpNode *pClient = static_cast<CTftpNode *>(pSession);

    if (pClient != NULL) {
        VERBOSE(Log(nAddr, "** %02d session opened port %d",
                    pClient->m_nSession, nPort));
        pClient->OnSessionRecv(0, pbData, cbData);
    }
    else {
        Log(nAddr, "Out of memory!");
    }
}

VOID CTftp::OnFactoryClose(UINT dwError)
{
    if (dwError) {
        m_pSink->OnTftpSocketError(dwError);
    }
}

VOID CTftp::Log(ULONG nAddr, PCSTR pszMsg, ...)
{
    if (m_pSink) {
        CHAR szBuffer[2048];
        va_list args;

        va_start(args, pszMsg);
        vsprintf(szBuffer, pszMsg, args);
        va_end(args);

        m_pSink->OnTftpMessage(nAddr, "%s", szBuffer);
    }
}
//
///////////////////////////////////////////////////////////////// End of File.
