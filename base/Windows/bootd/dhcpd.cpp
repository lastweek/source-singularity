// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

#include <winlean.h>
#include <winsock.h>
#include <stdio.h>
#include <assert.h>
#include <ctype.h>
#include <iphlpapi.h>

#include "dhcpd.h"

//
// DHCP Standard Options.
// 
#define DHCP_OPTION_PAD                      0
#define DHCP_OPTION_SUBNET_MASK              1
#define DHCP_OPTION_TIME_OFFSET              2
#define DHCP_OPTION_ROUTER_ADDRESS           3
#define DHCP_OPTION_TIME_SERVERS             4
#define DHCP_OPTION_IEN116_NAME_SERVERS      5
#define DHCP_OPTION_DOMAIN_NAME_SERVERS      6
#define DHCP_OPTION_LOG_SERVERS              7
#define DHCP_OPTION_COOKIE_SERVERS           8          // overridden w/ Command Line
#define DHCP_OPTION_LPR_SERVERS              9
#define DHCP_OPTION_IMPRESS_SERVERS          10         // overridden w/ Boot File
#define DHCP_OPTION_RLP_SERVERS              11
#define DHCP_OPTION_HOST_NAME                12
#define DHCP_OPTION_BOOT_FILE_SIZE           13
#define DHCP_OPTION_MERIT_DUMP_FILE          14
#define DHCP_OPTION_DOMAIN_NAME              15
#define DHCP_OPTION_SWAP_SERVER              16
#define DHCP_OPTION_ROOT_DISK                17
#define DHCP_OPTION_EXTENSIONS_PATH          18

//
// IP Layer Parameters - per host
// 
#define DHCP_OPTION_BE_A_ROUTER              19
#define DHCP_OPTION_NON_LOCAL_SOURCE_ROUTING 20
#define DHCP_OPTION_POLICY_FILTER_FOR_NLSR   21
#define DHCP_OPTION_MAX_REASSEMBLY_SIZE      22
#define DHCP_OPTION_DEFAULT_TTL              23
#define DHCP_OPTION_PMTU_AGING_TIMEOUT       24
#define DHCP_OPTION_PMTU_PLATEAU_TABLE       25

//
// IP Layer Parameters - per interface.
// 
#define DHCP_OPTION_MTU                      26
#define DHCP_OPTION_ALL_SUBNETS_MTU          27
#define DHCP_OPTION_BROADCAST_ADDRESS        28
#define DHCP_OPTION_PERFORM_MASK_DISCOVERY   29
#define DHCP_OPTION_BE_A_MASK_SUPPLIER       30
#define DHCP_OPTION_PERFORM_ROUTER_DISCOVERY 31
#define DHCP_OPTION_ROUTER_SOLICITATION_ADDR 32
#define DHCP_OPTION_STATIC_ROUTES            33
#define DHCP_OPTION_TRAILERS                 34
#define DHCP_OPTION_ARP_CACHE_TIMEOUT        35
#define DHCP_OPTION_ETHERNET_ENCAPSULATION   36

//
// TCP Parameters - per host
// 
#define DHCP_OPTION_TTL                      37
#define DHCP_OPTION_KEEP_ALIVE_INTERVAL      38
#define DHCP_OPTION_KEEP_ALIVE_DATA_SIZE     39

//
// Application Layer Parameters
// 
#define DHCP_OPTION_NETWORK_INFO_SERVICE_DOM 40
#define DHCP_OPTION_NETWORK_INFO_SERVERS     41
#define DHCP_OPTION_NETWORK_TIME_SERVERS     42

//
// Vender Specific Information Option
// 
#define DHCP_OPTION_VENDOR_SPEC_INFO         43

//
// NetBIOS Over TCP/IP Name Server Options
// 
#define DHCP_OPTION_NETBIOS_NAME_SERVER      44
#define DHCP_OPTION_NETBIOS_DATAGRAM_SERVER  45
#define DHCP_OPTION_NETBIOS_NODE_TYPE        46
#define DHCP_OPTION_NETBIOS_SCOPE_OPTION     47

//
// X Window System Options
// 
#define DHCP_OPTION_XWINDOW_FONT_SERVER      48
#define DHCP_OPTION_XWINDOW_DISPLAY_MANAGER  49

//
// DHCP Extensions
// 
#define DHCP_OPTION_REQUESTED_ADDRESS        50
#define DHCP_OPTION_LEASE_TIME               51
#define DHCP_OPTION_OK_TO_OVERLAY            52
#define DHCP_OPTION_MESSAGE_TYPE             53
#define DHCP_OPTION_SERVER_IDENTIFIER        54
#define DHCP_OPTION_PARAMETER_REQUEST_LIST   55
#define DHCP_OPTION_MESSAGE                  56
#define DHCP_OPTION_MESSAGE_LENGTH           57
#define DHCP_OPTION_RENEWAL_TIME             58      // T1   
#define DHCP_OPTION_REBIND_TIME              59      // T2   
#define DHCP_OPTION_CLIENT_CLASS_INFO        60
#define DHCP_OPTION_CLIENT_ID                61

//
// More Application Layer Parameters
// 
#define DHCP_OPTION_NIS_PLUS_DOM             64
#define DHCP_OPTION_NIS_PLUS                 65

//
// Overlaid Header Field Replacements
// 
#define DHCP_OPTION_TFTP_SERVER_NAME         66
#define DHCP_OPTION_TFTP_BOOTFILE_NAME       67

//
// Even More Application Layer Parameters
// 
#define DHCP_OPTION_MOBILE_IP_HOME_AGENTS    68
#define DHCP_OPTION_SMTP_SERVERS             69
#define DHCP_OPTION_POP_SERVERS              70
#define DHCP_OPTION_NNTP_SERVERS             71
#define DHCP_OPTION_WWW_SERVERS              72
#define DHCP_OPTION_FINGER_SERVERS           73
#define DHCP_OPTION_IRC_SERVERS              74
#define DHCP_OPTION_STREETTALK_SERVERS       75
#define DHCP_OPTION_STREETTALK_DIR_SERVERS   76

//
// Option codes from 77 to 127 are reserved through the
// Internet Assigned Numbers Authority (iana@isi.edu).
// 

//
// PXE Parameters
// 
#define DHCP_OPTION_PXE_CLIENT_ARCH_ID       93
#define DHCP_OPTION_PXE_CLIENT_NIC_ID        94
#define DHCP_OPTION_PXE_CLIENT_ID            97


//
// Option codes from 128 to 254 are for site-specific options.
// 
#define DHCP_OPTION_END                      255

//////////////////////////////////////////////////////////////////////////////

#define DHCP_MAGIC_COOKIE 0x63825363

#pragma pack(push)
#pragma pack(1)

struct OPTIONS {
    BYTE    Code;
    BYTE    Length;
    BYTE    Data[1];
};

struct DHCP_CMD {
    BYTE    op;
    BYTE    htype;
    BYTE    hlen;
    BYTE    hops;
    UINT32  xid;
    UINT16  secs;
    UINT16  flags;  // UNUSED for BOOTP
    UINT32  ciaddr;
    UINT32  yiaddr;
    UINT32  siaddr;
    UINT32  giaddr;
    BYTE    chaddr[16];
    CHAR    sname[64];
    CHAR    file[128];
    union {
        struct {
            UINT32   cookie;
            OPTIONS  options;
        } DHCP;
        struct {
            OPTIONS options;
        } BOOTP;
    };
};

#pragma pack(pop)

typedef enum {
    BOOTREQUEST = 1,
    BOOTREPLY   = 2
} BOOT_MESSAGE_TYPE;

typedef enum {
    DHCPDISCOVER = 1,
    DHCPOFFER    = 2,
    DHCPREQUEST  = 3,
    DHCPDECLINE  = 4,
    DHCPACK      = 5,
    DHCPNAK      = 6,
    DHCPRELEASE  = 7,
    DHCPINFORM   = 8
} DHCP_MESSAGE_TYPE;

#define MESSAGE_TYPE_MIN DHCPDISCOVER
#define MESSAGE_TYPE_MAX DHCPINFORM
#define MESSAGE_TYPE_COUNT (MESSAGE_TYPE_MAX-MESSAGE_TYPE_MIN+1)

CHAR *szMessageTypes[MESSAGE_TYPE_COUNT] = {"Discover",
                                            "Offer",
                                            "Request",
                                            "Decline",
                                            "Ack",
                                            "Nak",
                                            "Release",
                                            "Inform" };


#define OPERATOR_TYPE_MIN BOOTREQUEST
#define OPERATOR_TYPE_MAX BOOTREPLY
#define OPERATOR_TYPE_COUNT (OPERATOR_TYPE_MAX-OPERATOR_TYPE_MIN+1)

CHAR *szOperatorTypes[OPERATOR_TYPE_COUNT] = {"Request",
                                              "Reply"};

#define ARRAYOF(x)  (sizeof(x)/sizeof(x[0]))

//////////////////////////////////////////////////////////////////////////////
//
static void NormalizeMacRep(PSTR str)
{
    do {
        if (*str == ':')
            *str = '-';
    } while (*++str != '\0');
}

//////////////////////////////////////////////////////////////////////////////
//
static UINT64 IdFromMac(PBYTE pbMac)
{
    UINT64 idMac = 0;
    ((PBYTE)&idMac)[0] = pbMac[5];
    ((PBYTE)&idMac)[1] = pbMac[4];
    ((PBYTE)&idMac)[2] = pbMac[3];
    ((PBYTE)&idMac)[3] = pbMac[2];
    ((PBYTE)&idMac)[4] = pbMac[1];
    ((PBYTE)&idMac)[5] = pbMac[0];
    return idMac;
}

#if 0
static VOID MacFromId(UINT64 idMac, PBYTE pbMac)
{
    pbMac[0] = ((PBYTE)&idMac)[5];
    pbMac[1] = ((PBYTE)&idMac)[4];
    pbMac[2] = ((PBYTE)&idMac)[3];
    pbMac[3] = ((PBYTE)&idMac)[2];
    pbMac[4] = ((PBYTE)&idMac)[1];
    pbMac[5] = ((PBYTE)&idMac)[0];
}
#endif

//////////////////////////////////////////////////////////////////////////////
//
CDhcpNode::CDhcpNode()
{
    Enabled = FALSE;
    Name[0] = '\0';

    idMac = 0;
    iaLast = 0;
    iaAssigned = 0;
}

//////////////////////////////////////////////////////////////////////////////
//
CDhcpState::CDhcpState()
{
    strcpy(m_szBootFile, "pxe.com");
    strcpy(m_szCommand, "");
}

CDhcpState::~CDhcpState()
{
}

//////////////////////////////////////////////////////////////////////////////
//
static UINT32 ReadIpAddr(PCHAR psz)
{
    UINT32 nAddr = 0;
    UINT32 nDigit = 0;

    for (; *psz; psz++) {
        if (*psz >= '0' && *psz <= '9') {
            nDigit = nDigit * 10 + *psz - '0';
        }
        else if (*psz == '.') {
            nAddr = (nAddr << 8) | nDigit;
            nDigit = 0;
        }
    }
    nAddr = (nAddr << 8) | nDigit;
    return nAddr;
}

static void ReadMacFlags(CDhcpNode *pNode, PCHAR pszFlags)
{
    while (*pszFlags) {

        /////////////////////////////////////////////////////////// Find Flag.
        //
        while (*pszFlags && isspace(*pszFlags)) {
            pszFlags++;
        }
        if (*pszFlags == '\0' || *pszFlags == ';' || *pszFlags == '#') {
            break;
        }

        char *argn = pszFlags;                          // Argument name
        while (*pszFlags && !isspace(*pszFlags) &&
               *pszFlags != ':' && *pszFlags != '=') {
            pszFlags++;
        }

        if (*pszFlags == ':' || *pszFlags == '=') {     // Terminate name.
            *pszFlags++ = '\0';
        }

        char *argp = pszFlags;                          // Argument parameter
        while (*pszFlags && !isspace(*pszFlags)) {
            pszFlags++;
        }
        if (*pszFlags) {                                // Terminate parameter
            *pszFlags++ = '\0';
        }

        //////////////////////////////////////////////////////// Process Flag.
        //
        if (_strnicmp(argn, "enable", 4) == 0) {
            pNode->Enabled = TRUE;
        }
        else if (_strnicmp(argn, "disable", 4) == 0) {
            pNode->Enabled = FALSE;
        }
        else if (_strnicmp(argn, "name", 4) == 0) {
            strcpy(pNode->Name, argp);
        }
    }
}

void CDhcpState::CheckMacFlags(CDhcpNode *pNode)
{
    if (pNode->Name[0] == '\0') {
        sprintf(pNode->Name, "IP_%d_%d_%d_%d",
                ((PBYTE)&pNode->iaAssigned)[3],
                ((PBYTE)&pNode->iaAssigned)[2],
                ((PBYTE)&pNode->iaAssigned)[1],
                ((PBYTE)&pNode->iaAssigned)[0]);
    }
    else {
        PCHAR psz;
        if ((psz = strchr(pNode->Name, '.')) != NULL) {
            *psz = '\0';
        }
    }
}

BOOL CDhcpState::AddMacEntry(PCSTR psz)
{
    UINT IdMac[6] = { 0,0,0,0,0,0};
    UINT IpAddr[4] = { 0,0,0,0 };

    INT nRead = sscanf(psz,
                       "%02x-%02x-%02x-%02x-%02x-%02x,%d.%d.%d.%d",
                       &IdMac[5],
                       &IdMac[4],
                       &IdMac[3],
                       &IdMac[2],
                       &IdMac[1],
                       &IdMac[0],
                       &IpAddr[3],
                       &IpAddr[2],
                       &IpAddr[1],
                       &IpAddr[0]);
    if (nRead != 6 && nRead != 10) {
        return FALSE;
    }

    CDhcpNode *pNode = new CDhcpNode;
    pNode->Enabled = TRUE;
    pNode->idMac = 0;
    for (INT n = 0; n < 6; n++) {
        ((PBYTE)&pNode->idMac)[n] = (BYTE)IdMac[n];
    }
    for (INT n = 0; n < 4; n++) {
        ((PBYTE)&pNode->iaAssigned)[n] = (BYTE)IpAddr[n];
    }

    CheckMacFlags(pNode);

    if (m_pSink) {
        m_pSink->OnDhcpMessage(pNode->iaAssigned,
                               "Added mac %02x-%02x-%02x-%02x-%02x-%02x",
                               ((PBYTE)&pNode->idMac)[5],
                               ((PBYTE)&pNode->idMac)[4],
                               ((PBYTE)&pNode->idMac)[3],
                               ((PBYTE)&pNode->idMac)[2],
                               ((PBYTE)&pNode->idMac)[1],
                               ((PBYTE)&pNode->idMac)[0]
                              );
    }

    m_MacsById.Insert(pNode->idMac, pNode);
    return TRUE;
}

BOOL CDhcpState::ReadMacEntries(PCSTR pszFile)
{
    PCHAR psz;
    CHAR entry[768];

    FILE *fMap = fopen(pszFile, "r");
    if (fMap != NULL) {
        while ((psz = fgets(entry, sizeof(entry), fMap)) != NULL) {
            while (*psz && isspace(*psz)) {
                psz++;
            }

            if (*psz == '\0' || *psz == ';' || *psz == '#') { // Comment
                continue;
            }
            else if (*psz == '*') {                     // Defaults
            }
            else {
                char flags[768] = "";
                UINT IdMac[6] = { 0,0,0,0,0,0};
                UINT IpAddr[4] = { 0,0,0,0 };
                CDhcpNode *pNode = new CDhcpNode;

                NormalizeMacRep(psz);

                pNode->idMac = 0;
                INT nRead = sscanf(psz,
                                   "%02x-%02x-%02x-%02x-%02x-%02x %d.%d.%d.%d %[^\n]s",
                                   &IdMac[5],
                                   &IdMac[4],
                                   &IdMac[3],
                                   &IdMac[2],
                                   &IdMac[1],
                                   &IdMac[0],
                                   &IpAddr[3],
                                   &IpAddr[2],
                                   &IpAddr[1],
                                   &IpAddr[0],
                                   flags);

                pNode->idMac = 0;
                for (INT n = 0; n < 6; n++) {
                    ((PBYTE)&pNode->idMac)[n] = (BYTE)IdMac[n];
                }
                for (INT n = 0; n < 4; n++) {
                    ((PBYTE)&pNode->iaAssigned)[n] = (BYTE)IpAddr[n];
                }

                if (nRead == 6 || nRead >= 10) {
                    ReadMacFlags(pNode, flags);
                    CheckMacFlags(pNode);

                    m_MacsById.Insert(pNode->idMac, pNode);
                    pNode = NULL;
                }
                else {
                    delete pNode;
                    pNode = NULL;

                    if (m_pSink) {
                        m_pSink->OnDhcpMessage(0, "INI Error: %s", psz);
                    }
                }

            }
        }
        fclose(fMap);
        return TRUE;
    }
    return FALSE;
}

CDhcpNode *CDhcpState::FindMacEntry(UINT64 idMac)
{
    return m_MacsById.Find(idMac);
}

BOOL CDhcpState::IsPxeDhcpPacket(PBYTE pbPacket, UINT32 cbPacket)
{
    DHCP_CMD *dhcpPacket = (DHCP_CMD *)pbPacket;
    OPTIONS *pOption = NULL;
    OPTIONS *pOptionEnd = (OPTIONS *)(pbPacket + cbPacket);

    if (DHCP_MAGIC_COOKIE == ntohl(dhcpPacket->DHCP.cookie)) {
        pOption = &dhcpPacket->DHCP.options;
    }
    else {
        pOption = &dhcpPacket->BOOTP.options;
    }

    while (pOption < pOptionEnd) {
        if (pOption->Code == DHCP_OPTION_CLIENT_CLASS_INFO) {
            if (pOption->Length >= 9 &&
                memcmp(pOption->Data, "PXEClient", 9) == 0) {
                return TRUE;
            }
        }

        if (pOption->Code == 0)
            pOption = (OPTIONS *)(((CHAR *)pOption) + 1);
        else
            pOption = (OPTIONS *)(((CHAR *)pOption) + pOption->Length + 2);
    }
    return FALSE;
}

static BOOL GetDhcpOptions(DHCP_CMD *dhcpPacket,
                           UINT32 cbPacket,
                           PCHAR pszName,
                           PCHAR pszType,
                           PCHAR pszClas,
                           PUINT16 pusPxeArch,
                           PUINT16 pusPxeVers,
                           GUID * pguidPxeClientId
                          )
{
    OPTIONS *pOptionEnd = (OPTIONS *)(((CHAR *)dhcpPacket) + cbPacket);

    // dump all the options
    OPTIONS *pOption = NULL;
    if (DHCP_MAGIC_COOKIE == ntohl(dhcpPacket->DHCP.cookie)) {
        pOption = &dhcpPacket->DHCP.options;
    }
    else {
        pOption = &dhcpPacket->BOOTP.options;
    }

    CHAR szTemp[256];
    if (pszName == NULL) {
        pszName = szTemp;
    }
    if (pszType == NULL) {
        pszType = szTemp;
    }
    if (pszClas == NULL) {
        pszClas = szTemp;
    }

    pszName[0] = pszType[0] = pszClas[0] = '\0';
    *pusPxeArch = 0;
    *pusPxeVers = 0;
    memset(pguidPxeClientId, 0, sizeof(*pguidPxeClientId));

    while (pOption < pOptionEnd) {
        switch (pOption->Code) {
          case DHCP_OPTION_HOST_NAME: // HOST NAME
            strncpy(pszName, (PCHAR)pOption->Data, pOption->Length);
            pszName[pOption->Length] = '\0';
            break;
          case DHCP_OPTION_MESSAGE_TYPE:
            if ((MESSAGE_TYPE_MAX >= pOption->Data[0]) &&
                (MESSAGE_TYPE_MIN <= pOption->Data[0])) {
                strcpy(pszType, szMessageTypes[pOption->Data[0] - MESSAGE_TYPE_MIN]);
            }
            else {
                sprintf(pszType, "UNKNOWN (0x%02x)", pOption->Data[0]);
            }
            break;
          case DHCP_OPTION_CLIENT_CLASS_INFO: // CLASS IDENTIFIER
            strncpy(pszClas, (PCHAR)pOption->Data, pOption->Length);
            pszClas[pOption->Length] = '\0';
            break;
          case DHCP_OPTION_PXE_CLIENT_ARCH_ID:
            *pusPxeArch = ntohs(*(PUINT16)pOption->Data);
            break;
          case DHCP_OPTION_PXE_CLIENT_NIC_ID:
            if (pOption->Data[0] == 1) {
                *pusPxeArch = ntohs(*(PUINT16)(pOption->Data + 1));
            }
            break;
          case DHCP_OPTION_PXE_CLIENT_ID:
            if (pOption->Data[0] == 0) {
                memcpy(pguidPxeClientId, pOption->Data + 1, 16);
            }
            break;
          case DHCP_OPTION_END:
            pOption = pOptionEnd;
            break;
        }
        if (0 == pOption->Code)
            pOption = (OPTIONS *)(((CHAR *)pOption) + 1);
        else
            pOption = (OPTIONS *)(((CHAR *)pOption) + pOption->Length + 2);
    }

    return TRUE;
}

void AddOption(OPTIONS *&pOption, BYTE code, BYTE len, BYTE *data)
{
    pOption->Code = code;
    pOption->Length = len;
    if (len > 0) {
        memcpy(pOption->Data, data, len);
    }

    // increment pointer to next option location, include code and len bytes too
    if (DHCP_OPTION_PAD == pOption->Code || DHCP_OPTION_END == pOption->Code) {
        pOption = (OPTIONS *)(((CHAR *)pOption) + 1);
    }
    else {
        pOption = (OPTIONS *)(((CHAR *)pOption) + pOption->Length + 2);
    }
}

void AddOption(OPTIONS *&pOption, BYTE code, UINT32 iaAddr)
{
    iaAddr = htonl(iaAddr);
    AddOption(pOption, code, sizeof(iaAddr), (BYTE*)&iaAddr);
}

VOID CDhcpState::Configure(IDhcpSink *pSink, INT argc, PCHAR *argv)
{
    m_pSink = pSink;
    m_fQuiet = FALSE;

    for (INT arg = 0; arg < argc; arg++) {
        if (argv[arg][0] == '-' || argv[arg][0] == '/') {
            CHAR args[1024];
            strcpy(args, argv[arg]);
            char *argn = args+1;                   // Argument name
            char *argp = argn;                          // Argument parameter

            while (*argp && *argp != ':') {
                argp++;
            }
            if (*argp == ':') {
                *argp++ = '\0';
            }
            switch (argn[0]) {
              case 'b':                                 // Set boot file.
              case 'B':
                strcpy(m_szBootFile, argp);
                break;

              case 'c':                                 // Set cookie.
              case 'C':
                if (m_szCommand[0]) {
                    strcat(m_szCommand, " ");
                    strcat(m_szCommand, argp);
                }
                else {
                    strcpy(m_szCommand, argp);
                }
                break;

              case 'i':                                 // Set .ini file name.
              case 'I':
                if (!ReadMacEntries(argp)) {
                    m_pSink->OnDhcpMessage(0, "Error reading `%s'.");
                }
                break;
              case 'm':                                 // Mac address of client
              case 'M':
                NormalizeMacRep(argp);
                AddMacEntry(argp);
                break;

              case 'q':
              case 'Q':
                m_fQuiet = TRUE;
                break;

              case '?':
              case 'h':
              case 'H':
                break;
            }
        }
        else {
        }
    }
    m_pSink->OnDhcpMessage(0, "Boot File: %s", m_szBootFile);
    m_pSink->OnDhcpMessage(0, "CommandLn: %s", m_szCommand);
}

//////////////////////////////////////////////////////////////////////////////
//
CDhcp::CDhcp(CDhcp *pNext)
{
    m_pNext = pNext;
    m_pState = NULL;
    m_pSink = NULL;
    m_nAddr = 0;
    m_nPort = 0;
}

CDhcp::~CDhcp()
{
    if (m_pSink) {
        m_pSink->OnDhcpMessage(m_nAddr, "Server stopped.");
    }

    if (m_pNext) {
        delete m_pNext;
        m_pNext = NULL;
    }
}

VOID CDhcp::OnNetworkChange(UINT32 nAddr, UINT32 nMask, UINT32 nGate)
{
    if (m_nAddr == nAddr) {
        m_nMask = nMask;
        m_nGate = nGate;
        if (m_pSink) {
            m_pSink->OnDhcpMessage(nAddr,
                                   "Network change %s/%s",
                                   SocketToString(m_nMask),
                                   SocketToString(m_nGate));
        }
    }
    if (m_pNext) {
        m_pNext->OnNetworkChange(nAddr, nMask, nGate);
    }
}

VOID CDhcp::OnNetworkDelete(UINT32 nAddr, CDhcp **ppNext)
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

VOID CDhcp::Configure(UINT32 nAddr, UINT32 nMask, UINT32 nGate,
                      CDhcpState *pState, IDhcpSink *pSink, UINT16 nPort)
{
    m_pState = pState;
    m_nAddr = nAddr;
    m_nMask = nMask;
    m_nGate = nGate;
    m_nPort = nPort;
    m_pSink = pSink;

    if (m_pSink) {
        m_pSink->OnDhcpMessage(0,
                               "DHCP Server: %s:%d",
                               SocketToString(m_nAddr), m_nPort);
    }
}

VOID CDhcp::OnSocketRecv(UINT dwError,
                         UINT32 nAddr, UINT16 nPort, PBYTE pbData, UINT cbData)
{
#if 0
    m_pSink->OnDhcpMessage(nAddr,
                           "=> port %d to %d",
                           nPort, m_nPort);
#endif

    if (dwError) {
        m_pSink->OnDhcpSocketError(dwError);

      done:
        return;
    }

    if (nAddr == 0) {
        nAddr = INADDR_BROADCAST;
    }

    CHAR szName[256];
    CHAR szType[256];
    CHAR szClas[256];
    UINT16 usPxeArchId;
    UINT16 usPxeUndiId;
    GUID guidPxeClientId;

    DHCP_CMD *dhcpRequest = (DHCP_CMD *)pbData;
    UINT64 idMac = IdFromMac(dhcpRequest->chaddr);
    CDhcpNode *pEntry = m_pState->FindMacEntry(idMac);
    BOOL fIsPxe = m_pState->IsPxeDhcpPacket(pbData, cbData);

    if (idMac == 0) {
        // Ignore requests without the ETHERNET Address.
        goto done;
    }

    GetDhcpOptions(dhcpRequest, cbData, szName, szType, szClas,
                   &usPxeArchId, &usPxeUndiId, &guidPxeClientId);

    if (BOOTREQUEST != dhcpRequest->op ||
        DHCP_MAGIC_COOKIE != ntohl(dhcpRequest->DHCP.cookie)) {
        goto done;
    }

    if ((DHCP_OPTION_MESSAGE_TYPE != dhcpRequest->DHCP.options.Code) ||
        (DHCPREQUEST != dhcpRequest->DHCP.options.Data[0] &&
         DHCPDISCOVER != dhcpRequest->DHCP.options.Data[0])) {
        goto done;
    }

    if (pEntry == NULL && DHCPDISCOVER != dhcpRequest->DHCP.options.Data[0]) {
        goto done;
    }

    if (pEntry == NULL && m_pState->m_fQuiet) {
        goto done;
    }

    if (m_pSink) {
        m_pSink->OnDhcpMessage(nAddr,
                               "=> %s from %02x-%02x-%02x-%02x-%02x-%02x port %d",
                               szType,
                               ((PBYTE)&idMac)[5],
                               ((PBYTE)&idMac)[4],
                               ((PBYTE)&idMac)[3],
                               ((PBYTE)&idMac)[2],
                               ((PBYTE)&idMac)[1],
                               ((PBYTE)&idMac)[0],
                               nPort);
        m_pSink->OnDhcpMessage(nAddr,
                               "   %s%s %s",
                               fIsPxe ? "[PXE] " : "",
                               szClas,
                               szName);
    }

    if (pEntry == NULL || pEntry->Enabled == FALSE) {
        goto done;
    }

    ///// Send the Reply.
    BYTE PacketOut[1600];

    // fill in packet before sending
    DHCP_CMD *pdhcpReply = (DHCP_CMD *)PacketOut;

    memset(pdhcpReply, 0, sizeof(*pdhcpReply));

    // broadcast, or use the client specified address for replies
    if (dhcpRequest->ciaddr) {
        pEntry->iaLast = ntohl(dhcpRequest->ciaddr);
    }

    pdhcpReply->op     = BOOTREPLY; // REPLY
    pdhcpReply->htype  = 1; // ETHERNET
    pdhcpReply->hlen   = 6; // 6 BYTE HARDWARE ADDRESS LENGTH (MAC)
    pdhcpReply->hops   = 0;
    pdhcpReply->xid    = dhcpRequest->xid;
    pdhcpReply->secs   = 0;
    pdhcpReply->flags  = dhcpRequest->flags;
    pdhcpReply->ciaddr = dhcpRequest->ciaddr;
    if (fIsPxe && dhcpRequest->ciaddr == htonl(pEntry->iaAssigned)) {
        pdhcpReply->yiaddr = 0;
    }
    else {
        pdhcpReply->yiaddr = htonl(pEntry->iaAssigned);
    }
    pdhcpReply->siaddr = htonl(m_nAddr);
    pdhcpReply->giaddr = 0;
    memcpy(pdhcpReply->chaddr, dhcpRequest->chaddr, 16);
    sprintf(pdhcpReply->sname, "%d.%d.%d.%d",
            ((BYTE *)&m_nAddr)[3],
            ((BYTE *)&m_nAddr)[2],
            ((BYTE *)&m_nAddr)[1],
            ((BYTE *)&m_nAddr)[0]);
    strcpy(pdhcpReply->file, m_pState->m_szBootFile);
    pdhcpReply->DHCP.cookie = htonl(DHCP_MAGIC_COOKIE);

    // start pointing to first location for options
    OPTIONS *pOptions = &pdhcpReply->DHCP.options;

    // START OF OPTION ADDITIONS

    // DHCP MESSAGE TYPE OPTION - MUST BE FIRST OPTION
    BYTE data[1] = { DHCPACK };
    if (dhcpRequest->DHCP.options.Data[0] == DHCPREQUEST) {
        data[0] = DHCPACK;
        if (m_pSink) {
            m_pSink->OnDhcpAck(pEntry->iaAssigned, idMac);
        }
    }
    else if (dhcpRequest->DHCP.options.Data[0] == DHCPDISCOVER) {
        data[0] = DHCPOFFER;
        if (m_pSink) {
            m_pSink->OnDhcpOffer(pEntry->iaAssigned, idMac);
        }
    }

    AddOption(pOptions, DHCP_OPTION_MESSAGE_TYPE, 1, data);
    if (fIsPxe) {
        AddOption(pOptions, DHCP_OPTION_SERVER_IDENTIFIER, m_nAddr);
        if (m_nGate) {
            AddOption(pOptions, DHCP_OPTION_ROUTER_ADDRESS, m_nGate);
        }
        else {
            // Older PXE implementations (like the Windows Boot Floppy)
            // won't boot without a router address.
            AddOption(pOptions, DHCP_OPTION_ROUTER_ADDRESS, m_nAddr);
        }
        AddOption(pOptions, DHCP_OPTION_SUBNET_MASK, m_nMask);

        BYTE ClientId[17];
        ClientId[0] = 0x00;
        memcpy(ClientId + 1, &guidPxeClientId, sizeof(guidPxeClientId));

        AddOption(pOptions, DHCP_OPTION_PXE_CLIENT_ID, sizeof(ClientId), ClientId);
        AddOption(pOptions, DHCP_OPTION_CLIENT_CLASS_INFO, 9, (BYTE*)"PXEClient");
        AddOption(pOptions, DHCP_OPTION_HOST_NAME,
                  (BYTE)strlen(pEntry->Name), (BYTE*)pEntry->Name);
        AddOption(pOptions, DHCP_OPTION_COOKIE_SERVERS,
                  (BYTE)strlen(m_pState->m_szCommand), (BYTE*)m_pState->m_szCommand);
        AddOption(pOptions, DHCP_OPTION_END, 0, NULL);
    }
    else {
        AddOption(pOptions, DHCP_OPTION_SERVER_IDENTIFIER, m_nAddr);
        if (m_nGate) {
            AddOption(pOptions, DHCP_OPTION_ROUTER_ADDRESS, m_nGate);
        }
        AddOption(pOptions, DHCP_OPTION_SUBNET_MASK, m_nMask);
        AddOption(pOptions, DHCP_OPTION_HOST_NAME,
                  (BYTE)strlen(pEntry->Name), (BYTE*)pEntry->Name);
        // AddOption(pOptions, DHCP_OPTION_END, 0, NULL);
    }

    // END OF OPTION ADDITIONS

    // calc size of added options, minus the single option already included
    UINT32 dwOptionSize = (UINT32)pOptions - (UINT32)&pdhcpReply->DHCP.options;
    UINT32 dwPacketOutSize = sizeof(*pdhcpReply) + dwOptionSize - 3;
    // 3 since first option is already included in structure

    // always AF_INET
    if (nAddr == 0) {
        nAddr = INADDR_BROADCAST;
    }

    // broadcast, or use the client specified address for replies
    if (ntohs(dhcpRequest->flags) & 0x8000) {
        nAddr = INADDR_BROADCAST;
    }
    else {
        if (dhcpRequest->ciaddr) {
            nAddr = pEntry->iaLast;
        }
        else {
            nAddr = INADDR_BROADCAST;
        }
    }
#if 0
    nAddr = INADDR_BROADCAST;
#endif
    m_pSink->OnDhcpMessage(nAddr, "<= Reply to %02x-%02x-%02x-%02x-%02x-%02x\n",
                           ((PBYTE)&pEntry->idMac)[5],
                           ((PBYTE)&pEntry->idMac)[4],
                           ((PBYTE)&pEntry->idMac)[3],
                           ((PBYTE)&pEntry->idMac)[2],
                           ((PBYTE)&pEntry->idMac)[1],
                           ((PBYTE)&pEntry->idMac)[0]);

    SocketSend(nAddr, DHCP_CLIENT_PORT, (PBYTE)PacketOut, dwPacketOutSize);
    goto done;
}

//
///////////////////////////////////////////////////////////////// End of File.
