////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   NtlmWinHost.cpp
//
//  Note:
//
//		This program is part of the unit test for the NTLM authentication library.
//		Run this program on a Windows machine, and run Application\Tests\NtlmUnitTest
//		on Singularity.  Specify the @remote command, and provide -user=username
//		and -password=password, and the IP address the machine running this program.
//		NtlmUnitTest will then connect to the Windows machine and perform an NTLM
//		exchange.
//
//	TODO:
//
//		*	Clean up this file.
//

#include <windows.h>
#define SECURITY_WIN32
#include <security.h>

using namespace System;
using namespace System::Net;
using namespace System::Net::Sockets;
using namespace System::Diagnostics;
using namespace System::Runtime::InteropServices;
using namespace System::Threading;
using namespace System::Text;
using namespace System::Reflection;
using namespace System::Runtime::CompilerServices;
using namespace System::Security::Permissions;


typedef System::Byte byte;
typedef System::UInt32 uint;
typedef System::UInt16 ushort;
typedef System::UInt64 ulong;

const int NtlmUnitTestPort = 720;

#pragma comment(lib,"secur32.lib")

[StructLayout(LayoutKind::Sequential)]
value struct TestMessageHeader
{
public:
	uint TotalLength;
	uint MessageType;
};

[StructLayout(LayoutKind::Sequential)]
value struct ResultMessage
{
public:
	int Succeeded;
	// unicode string of error follows, no nul terminator
};

enum class TestMessageType
{
	Negotiate = 1,
	Challenge = 2,
	Response = 3,
	Result = 4,	
};

ref class Util
{
public:

	literal String^ HexDigits = "0123456789abcdef";

	static void DumpException(Exception^ chain)
	{
		for (Exception^ ex = chain; ex != nullptr; ex = ex->InnerException) {
			Console::WriteLine("{0}: {1}", ex->GetType()->FullName, ex->Message);
		}
	}

	static array<byte>^ GetSubArray(array<byte>^ arr, int offset, int length)
	{
		array<byte>^ newarray = gcnew array<byte>(length);
		Buffer::BlockCopy(arr, offset, newarray, 0, length);
		return newarray;
	}

	static String^ ByteArrayToString(array<byte>^ arr)
	{
		StringBuilder^ buf = gcnew StringBuilder(arr->Length * 2);
		for (int i = 0; i < arr->Length; i++) {
			byte b = arr[i];
			buf->Append(HexDigits[b >> 4]);
			buf->Append(HexDigits[b & 0xf]);
		}
		return buf->ToString();
	}

public:
    static String^ FormatMessageFromSystem(ULONG message);

    static void DumpBuffer(PUCHAR buffer, int length);
    static void DumpBuffer(array<byte>^ buffer, int offset, int length);

    [DllImport("KERNEL32.DLL", CharSet = CharSet::Unicode)]
    static int FormatMessage(DWORD dwFlags, LPCVOID lpSource, DWORD dwMessageId,
        DWORD dwLanguageId, LPTSTR lpBuffer, DWORD nSize, PVOID Arguments);


    generic<typename T> static int CompareArraySpans(array<T>^ array1, int offset1, array<T>^ array2, int offset2, int length)
    {
        for (int i = 0; i < length; i++)
        {
            T element1 = array1[i];
            T element2 = array2[i];
            if (element1 < element2)
                return -1;
            if (element1 > element2)
                return 1;
        }

        return 0;
    }


};


//
//
//struct {
//      byte    protocol[8];     // 'N', 'T', 'L', 'M', 'S', 'S', 'P', '\0'
//      byte    type;            // 0x01
//      byte    zero[3];
//      short   flags;           // 0xb203
//      byte    zero[2];
//
//0x10    short   dom_len;         // domain string length
//      short   dom_len;         // domain string length
//      short   dom_off;         // domain string offset
//      byte    zero[2];
//
//0x18    short   host_len;        // host string length
//      short   host_len;        // host string length
//      short   host_off;        // host string offset (always 0x20)
//      byte    zero[2];
//
//0x20    byte    host[*];         // host string (ASCII)
//      byte    dom[*];          // domain string (ASCII)
//  } type-1-message
//
//
//

public enum class NtlmMessageType
{
    Negotiate = 1,
    Challenge = 2,
    Response = 3,
};

[Flags]
public enum class NtlmNegotiateFlags
{
    None = 0,

    NegotiateUnicode = 0x00000001,// Text strings are in unicode
    NegotiateOem = 0x00000002,// Text strings are in OEM
    RequestTarget = 0x00000004,// Server should return its authentication realm

    NegotiateSign = 0x00000010,// Request signature capability
    NegotiateSeal = 0x00000020,// Request confidentiality
    NegotiateDatagram = 0x00000040,// Use datagram style authentication
    NegotiateLmKey = 0x00000080,// Use LM session key for sign/seal

    NegotiateNetware = 0x00000100,// NetWare authentication
    NegotiateNtlm = 0x00000200,// NTLM authentication
    NegotiateNtOnly = 0x00000400,// NT authentication only (no LM)
    NegotiateNullSession = 0x00000800,// NULL Sessions on NT 5.0 and beyond

    NegotiateOemDomainSupplied = 0x1000,// Domain Name supplied on negotiate
    NegotiateOemWorkstationSupplied = 0x2000,// Workstation Name supplied on negotiate
    NegotiateLocalCall = 0x00004000,// Indicates client/server are same machine
    NegotiateAlwaysSign = 0x00008000,// Sign for all security levels
};


#define NTLM_CHALLENGE_LENGTH 8

public ref class NtlmConstants
{
public:

    static initonly array<Byte>^ MessageSignature = { 'N', 'T', 'L', 'M', 'S', 'S', 'P', 0 };
};

public ref class NtlmUtil
{
private:
    
    literal int HeaderLength = 0x10;

public:


    static ushort GetUInt16(array<Byte>^ message, int pos)
    {
        return message[pos] + (message[pos + 1] << 8);
    }

    static array<Byte>^ GetCountedBytesAt(array<Byte>^ message, int pos)
    {
        int length = GetUInt16(message, pos + 0);
        int maxlength = GetUInt16(message, pos + 2);
        int offset = GetUInt16(message, pos + 4);

        if (offset >= message->Length)
            throw gcnew Exception("String has invalid offset");

        if (offset + length > message->Length)
            throw gcnew Exception("String has invalid offset / length");

        return Util::GetSubArray(message, offset, length);
    }

    static String^ GetCountedStringAt(array<Byte>^ message, int pos)
    {
        int length = GetUInt16(message, pos + 0);
        int maxlength = GetUInt16(message, pos + 2);
        int offset = GetUInt16(message, pos + 4);

        if (offset >= message->Length)
            throw gcnew Exception("String has invalid offset");

        if (offset + length > message->Length)
            throw gcnew Exception("String has invalid offset / length");

        String^ result = Encoding::Unicode->GetString(message, offset, length);
        return result;
    }

    static void DumpMessage(array<Byte>^ message)
    {
        DumpMessage(message, message->Length);
    }

    static void DumpMessage(array<Byte>^ message, int length)
    {
        Console::WriteLine("");
        Console::WriteLine("NTLM message:");
        Util::DumpBuffer(message, 0, length);

        if (length < HeaderLength) {
            Console::WriteLine("    Message is invalid; too short");
            return;
        }

        for (int i = 0; i < NtlmConstants::MessageSignature->Length; i++) {
            if (message[i] != NtlmConstants::MessageSignature[i]) {
                Console::WriteLine("    Message is invalid; signature does not match");
                return;
            }
        }

        NtlmMessageType type = (NtlmMessageType)message[8];

        switch (type) {
            case NtlmMessageType::Negotiate:
                {
//
//typedef struct _NEGOTIATE_MESSAGE {
//  UCHAR Signature[sizeof(NTLMSSP_SIGNATURE)];
//  NTLM_MESSAGE_TYPE MessageType;
//  ULONG NegotiateFlags;
//  STRING32 OemDomainName;
//  STRING32 OemWorkstationName;
//  ULONG64 Version;
//} NEGOTIATE_MESSAGE, *PNEGOTIATE_MESSAGE;
//
//
                    Console::WriteLine("    Type: Negotiate");
                    NtlmNegotiateFlags flags = (NtlmNegotiateFlags)GetUInt16(message, 12);
                    Console::WriteLine(String::Format("    Flags: 0x{0:x8}  {1}", (UInt32)flags, flags.ToString()));
                    String^ domain = GetCountedStringAt(message, 0x10);
                    Console::WriteLine("    Domain: " + domain);
                }

                break;

            case NtlmMessageType::Challenge:
                {
                    //
//typedef struct _CHALLENGE_MESSAGE {
    //UCHAR Signature[sizeof(NTLMSSP_SIGNATURE)];             // 0x00
    //NTLM_MESSAGE_TYPE MessageType;                          // 0x08
    //STRING32 TargetName;                                    // 0x0c
    //ULONG NegotiateFlags;                                   // 0x10
    //UCHAR Challenge[MSV1_0_CHALLENGE_LENGTH];               // 0x14
    //ULONG64 ServerContextHandle;                            // 0x20
    //STRING32 TargetInfo;                                    // 0x28
    //ULONG64 Version;                                        // 0x30
                    //                                      // 0x38
//} CHALLENGE_MESSAGE, *PCHALLENGE_MESSAGE;
                    //

                    Console::WriteLine("    Type: Challenge");
                    String^ TargetName = GetCountedStringAt(message, 0x0c);
                    array<Byte>^ Challenge = Util::GetSubArray(message, 0x14, NTLM_CHALLENGE_LENGTH);
                    Console::WriteLine("    TargetName:     " + TargetName);
                    Console::WriteLine("    Challenge:      " + Util::ByteArrayToString(Challenge));

                }
                break;

            case NtlmMessageType::Response:
                {
                    //
//typedef struct _AUTHENTICATE_MESSAGE {
    //UCHAR Signature[sizeof(NTLMSSP_SIGNATURE)];
    //NTLM_MESSAGE_TYPE MessageType;
    //STRING32 LmChallengeResponse;
    //STRING32 NtChallengeResponse;
    //STRING32 DomainName;
    //STRING32 UserName;
    //STRING32 Workstation;
    //STRING32 SessionKey;
    //ULONG NegotiateFlags;
    //ULONG64 Version;
//} AUTHENTICATE_MESSAGE, *PAUTHENTICATE_MESSAGE;
//
//typedef struct _OLD_AUTHENTICATE_MESSAGE {
    //UCHAR Signature[sizeof(NTLMSSP_SIGNATURE)];         // 0
    //NTLM_MESSAGE_TYPE MessageType;                      // 8
    //STRING32 LmChallengeResponse;                       // 12   0x0c
    //STRING32 NtChallengeResponse;                       // 20   0x14
    //STRING32 DomainName;                                // 28   0x1c
    //STRING32 UserName;                                  // 36   0x24
    //STRING32 Workstation;                               // 42   0x2c
//} OLD_AUTHENTICATE_MESSAGE, *POLD_AUTHENTICATE_MESSAGE;
  //

                    Console::WriteLine("    Type: Response");
                    array<Byte>^ LmChallengeResponse = GetCountedBytesAt(message, 0x0c);
                    array<Byte>^ NtChallengeResponse = GetCountedBytesAt(message, 0x14);
                    String^ DomainName = GetCountedStringAt(message, 28);
                    String^ UserName = GetCountedStringAt(message, 36);
                    String^ Workstation = GetCountedStringAt(message, 44);

                    Console::WriteLine("    LmChallengeResponse:  " + Util::ByteArrayToString(LmChallengeResponse));
                    Console::WriteLine("    NtChallengeResponse:  " + Util::ByteArrayToString(NtChallengeResponse));
                    
                    Console::WriteLine("    DomainName:   " + DomainName);
                    Console::WriteLine("    UserName:     " + UserName);
                    Console::WriteLine("    Workstation:  " + Workstation);
                }
                break;

            default:
                Console::WriteLine("    Message is invalid; message type byte is not recognized");
                return;
        }

        Console::WriteLine("");

    }
};

#define ThrowStatus(status, message) do { \
    Console::WriteLine("ThrowStatus: " + message); \
    Console::WriteLine(Util::FormatMessageFromSystem(status)); \
    throw gcnew Exception(String::Format("FAILED: {0} - {1}", message, Util::FormatMessageFromSystem(status))); \
} while (0)


#if 0
void CheckStatus(SECURITY_STATUS status, String^ message)
{
    if (status != SEC_E_OK)
        Throwstatus(status);
    Console::WriteLine(message + " - ok");
}
#else

#define CheckStatus(status, message) do { \
    if (status != SEC_E_OK) ThrowStatus(status, message); \
    Console::WriteLine(message + " - ok"); \
    } while(false)

#endif

class StringWrapperW
{
private:
    wchar_t* _buffer;

public:
    StringWrapperW(String^ str)
    {
        _buffer = (wchar_t*)(void*)Marshal::StringToHGlobalUni(str);
    }

    ~StringWrapperW()
    {
        Marshal::FreeHGlobal((IntPtr)(void*)_buffer);
    }

    operator wchar_t*()
    {
        return _buffer;
    }
};

class StringWrapperA
{
private:
    char* _buffer;

public:
    StringWrapperA(String^ str)
    {
        _buffer = (char*)(void*)Marshal::StringToHGlobalAnsi(str);
    }

    ~StringWrapperA()
    {
        Marshal::FreeHGlobal((IntPtr)(void*)_buffer);
    }

    operator char*()
    {
        return _buffer;
    }
};



value struct ManagedSecHandle
{
public:
    ULONG_PTR dwLower;
    ULONG_PTR dwUpper;

public:
    ManagedSecHandle(SecHandle handle)
    {
        dwLower = handle.dwLower;
        dwUpper = handle.dwUpper;
    }

    operator SecHandle()
    {
        SecHandle handle;
        handle.dwLower = dwLower;
        handle.dwUpper = dwUpper;
        return handle;
    }
};

typedef ManagedSecHandle ManagedCredHandle;
typedef ManagedSecHandle ManagedCtxtHandle;



#if 0
ref class SspiNtlmSupplicant : NtlmSupplicant
{
public:
    ManagedCredHandle _credentials;
    ManagedCtxtHandle _context;

    virtual array<Byte>^ GetNegotiate(
        String^ username,
        String^ domain,
        String^ password) override
    {
        SECURITY_STATUS status;

        StringWrapperW username_w(username);
        StringWrapperW domain_w(domain);
        StringWrapperW password_w(password);

        //
        // First, generate the NTLM client credentials
        //

        SEC_WINNT_AUTH_IDENTITY clientIdentity;
        ZeroMemory(&clientIdentity, sizeof(clientIdentity));
        clientIdentity.Domain = domain_w;
        clientIdentity.DomainLength = _tcslen(domain_w);
        clientIdentity.User = username_w;
        clientIdentity.UserLength = _tcslen(username_w);
        clientIdentity.Password = password_w;
        clientIdentity.PasswordLength = _tcslen(password_w);
        clientIdentity.Flags = SEC_WINNT_AUTH_IDENTITY_UNICODE;

        TimeStamp expires;

        CredHandle credentials = { 0, 0 };

        status = AcquireCredentialsHandle(
            NULL,
            L"NTLM",
            SECPKG_CRED_OUTBOUND,           // credentials use
            NULL,                           // logon id (LUID, not used)
            &clientIdentity,                // auth data
            NULL,                           // pGetKeyFn - not used
            NULL,                           // pGetKeyArgument - not used
            &credentials,                  // the credentials returned
            &expires                        // not used
            );

        CheckStatus(status, "Client - Failed to acquire credentials");

        _credentials = ManagedCredHandle(credentials);

        TimeStamp contextExpires;

        SecBuffer outputBuffer;

        array<Byte>^ hello = gcnew array<Byte>(0x100);
        pin_ptr<Byte> hello_pinned = &hello[0];

        outputBuffer.BufferType = SECBUFFER_TOKEN;
        outputBuffer.cbBuffer = hello->Length;
        outputBuffer.pvBuffer = hello_pinned;

        SecBufferDesc outputDesc;
        outputDesc.pBuffers = &outputBuffer;
        outputDesc.cBuffers = 1;
        outputDesc.ulVersion = SECBUFFER_VERSION;

        ULONG attributes;
        CtxtHandle context = { 0, 0 };
        status = InitializeSecurityContext(
            &credentials,                   // credentials
            NULL,                           // existing context handle (none)
            NULL,                           // service principal name (none)
            ISC_REQ_CONNECTION,                              // context requirements (most don't apply)
            0,                              // reserved
            SECURITY_NETWORK_DREP,          // data representation
            NULL,                           // input token (none on first call)
            0,                              // reserved
            &context,                       // the new context handle
            &outputDesc,                    // the output buffer
            &attributes,                    // returns context attributes
            &contextExpires                 // when it expires
            );

        switch (status) {
            case SEC_I_CONTINUE_NEEDED:
                // This is the expected case.
                Console::WriteLine("Client - SEC_I_CONTINUE_NEEDED");
                Console::WriteLine(String::Format("    attributes: 0x{0:x}", attributes));
                _context = ManagedCtxtHandle(context);
                return Util::GetSubArray(hello, 0, outputBuffer.cbBuffer);

            default:
                ThrowStatus(status, "Client - AcquireCredentialsHandle");
        }
    }


    // Returns the response.
    virtual array<Byte>^ ProcessChallenge(array<Byte>^ challenge) override
    {
        TimeStamp contextExpires;

        pin_ptr<Byte> challenge_pinned = &challenge[0];

        SecBuffer challengeSecBuffer;
        challengeSecBuffer.BufferType = SECBUFFER_TOKEN;
        challengeSecBuffer.cbBuffer = challenge->Length;
        challengeSecBuffer.pvBuffer = challenge_pinned;

        SecBufferDesc challengeDesc;
        challengeDesc.cBuffers = 1;
        challengeDesc.pBuffers = &challengeSecBuffer;
        challengeDesc.ulVersion = SECBUFFER_VERSION;

        array<Byte>^ response_buffer = gcnew array<Byte>(0x100);
        pin_ptr<Byte> response_pinned = &response_buffer[0];

        SecBuffer outputBuffer;
        outputBuffer.BufferType = SECBUFFER_TOKEN;
        outputBuffer.cbBuffer = response_buffer->Length;
        outputBuffer.pvBuffer = response_pinned;

        SecBufferDesc outputDesc;
        outputDesc.pBuffers = &outputBuffer;
        outputDesc.cBuffers = 1;
        outputDesc.ulVersion = SECBUFFER_VERSION;

        CredHandle credentials = _credentials;
        CtxtHandle context = _context;

        ULONG attributes;
        SECURITY_STATUS status = InitializeSecurityContext(
            &credentials,                   // credentials
            &context,                       // existing context handle
            NULL,                           // service principal name (none)
            0,                              // context requirements (most don't apply)
            0,                              // reserved
            SECURITY_NETWORK_DREP,          // data representation
            &challengeDesc,                 // input token (none on first call)
            0,                              // reserved
            &context,                       // the new context handle
            &outputDesc,                    // the output buffer
            &attributes,                    // returns context attributes
            &contextExpires                 // when it expires
            );

        _context = ManagedCtxtHandle(context);

        switch (status) {
            case SEC_E_OK:
                // This is the expected case.
                Console::WriteLine("Client - SEC_E_OK");
                Console::WriteLine(String::Format("    attributes: 0x{0:x}", attributes));
                return Util::GetSubArray(response_buffer, 0, outputBuffer.cbBuffer);

            default:
                ThrowStatus(status, "Client - AcquireCredentialsHandle");
        }
    }
};
#endif


//
//This class wraps the Windows NTLMSSP, through the SSPI.
//

ref class SspiNtlmAuthenticator
{
private:

    ManagedCredHandle _credentials;
    ManagedCtxtHandle _context;

public:

    void Initialize()
    {
        SECURITY_STATUS status;

        CredHandle credentials = { 0, 0 };

        TimeStamp expires;
        status = AcquireCredentialsHandle(
            NULL,
            L"NTLM",
            SECPKG_CRED_INBOUND,            // credentials use
            NULL,                           // logon id (LUID, not used)
            NULL,                           // auth data
            NULL,                           // pGetKeyFn - not used
            NULL,                           // pGetKeyArgument - not used
            &credentials,                   // the credentials returned
            &expires                        // not used
            );

        CheckStatus(status, "Server - AcquireCredentialsHandle");

        _credentials = ManagedCredHandle(credentials);
    }

    array<byte>^ GetChallenge(array<byte>^ negotiate)
    {
        pin_ptr<byte> negotiate_pinned = &negotiate[0];

        SecBuffer negotiateSecBuffer;
        negotiateSecBuffer.BufferType = SECBUFFER_TOKEN | SECBUFFER_READONLY;
        negotiateSecBuffer.cbBuffer = negotiate->Length;
        negotiateSecBuffer.pvBuffer = negotiate_pinned;

        SecBufferDesc negotiateDesc;
        negotiateDesc.cBuffers = 1;
        negotiateDesc.pBuffers = &negotiateSecBuffer;
        negotiateDesc.ulVersion = SECBUFFER_VERSION;

        array<byte>^ challenge_buffer = gcnew array<Byte>(0x200);
        pin_ptr<byte> challenge_pinned = &challenge_buffer[0];

        SecBuffer challengeSecBuffer;
        challengeSecBuffer.BufferType = SECBUFFER_TOKEN;
        challengeSecBuffer.cbBuffer = challenge_buffer->Length;
        challengeSecBuffer.pvBuffer = challenge_pinned;

        SecBufferDesc challengeDesc;
        challengeDesc.ulVersion = SECBUFFER_VERSION;
        challengeDesc.cBuffers = 1;
        challengeDesc.pBuffers = &challengeSecBuffer;

        TimeStamp expires;
        ULONG attributes;
        CredHandle credentials = _credentials;
        CtxtHandle context = { 0, 0 };

        SECURITY_STATUS status = AcceptSecurityContext(
            &credentials,
            NULL,                       // no previous context
            &negotiateDesc,             // input buffer
            0,                          // context requirements
            SECURITY_NETWORK_DREP,      // data representation
            &context,
            &challengeDesc,
            &attributes,
            &expires
            );

        switch (status) {
            case SEC_I_CONTINUE_NEEDED:
			{
                // This is the expected success case.

                Console::WriteLine("Server - AcceptSecurityContext succeeded");
                array<byte>^ challenge = gcnew array<Byte>(challengeSecBuffer.cbBuffer);
                Array::Copy(challenge_buffer, 0, challenge, 0, challenge->Length);
                _context = ManagedCtxtHandle(context);
                return challenge;
			}

            default:
                ThrowStatus(status, "Server - AcceptSecurityContext");
        }
    }

    void VerifyResponse(array<Byte>^ response)
    {
        SECURITY_STATUS status;

        pin_ptr<Byte> response_pinned = &response[0];

        SecBuffer responseSecBuffer;
        responseSecBuffer.BufferType = SECBUFFER_TOKEN;
        responseSecBuffer.cbBuffer = response->Length;
        responseSecBuffer.pvBuffer = response_pinned;

        SecBufferDesc responseDesc;
        responseDesc.ulVersion = SECBUFFER_VERSION;
        responseDesc.pBuffers = &responseSecBuffer;
        responseDesc.cBuffers = 1;

        TimeStamp expires;
        ULONG attributes;
        CtxtHandle context = _context;
        CredHandle credentials = _credentials;

        status = AcceptSecurityContext(
            &credentials,
            &context,                   // previous context
            &responseDesc,              // input buffer
            0,                          // context requirements
            SECURITY_NETWORK_DREP,      // data representation
            &context,
            NULL,                       // no output buffer
            &attributes,
            &expires
            );

        _context = ManagedCtxtHandle(context);

        switch (status) {
            case SEC_E_OK:
                Console::WriteLine("Server - Authentication complete");
                break;

            default:
                ThrowStatus(status, "Server - Authentication failed");
        }

        HANDLE token;

        status = QuerySecurityContextToken(&context, &token);
        CheckStatus(status, "Server - QuerySecurityContextToken");

        Console::WriteLine(String::Format("token - 0x{0:x8}", (ULONG_PTR)token));

    }

};



ref class Client
{
private:

	initonly Socket^ _socket;

	Client(Socket^ socket)
	{
		_socket = socket;
	}

	array<Byte>^ ReceiveMessage(TestMessageType% type)
	{
		array<byte>^ headerBuffer = gcnew array<byte>(sizeof(TestMessageHeader));
		
		int length = _socket->Receive(headerBuffer, sizeof(TestMessageHeader), SocketFlags::None);
		if (length == 0) {
			throw gcnew Exception("Server has closed socket.");
		}
		
		if (length < (int)sizeof(TestMessageHeader)) {
			throw gcnew Exception("Received short data from server.");
		}
		pin_ptr<byte> headerBuffer_ptr = &headerBuffer[0];

		TestMessageHeader header = *(TestMessageHeader*)headerBuffer_ptr;
		
		if (header.TotalLength < sizeof(TestMessageHeader)) {
			throw gcnew Exception("Received invalid header from server (length is too short)");
		}
		
		if (header.TotalLength > 0x10000) {
			throw gcnew Exception("Received excessively large message from server.");
		}
		
		int bodyLength = (int)(header.TotalLength - sizeof(TestMessageHeader));
		array<byte>^ body = gcnew array<byte>(bodyLength);
		
		length = _socket->Receive(body, bodyLength, SocketFlags::None);
		if (length == 0)
			throw gcnew Exception("Server has closed socket.");
		
		if (length < bodyLength)
			throw gcnew Exception("Received short data (payload) from server.");
		
		type = (TestMessageType)header.MessageType;
		return body;
	}

	array<byte>^ ReceiveExpectedMessage(TestMessageType type)
	{
		TestMessageType actualType;
		array<byte>^ msg = ReceiveMessage(actualType);
		if (actualType != type) {
			Console::WriteLine("Received message, but its type is not the expected type!");
			Console::WriteLine("Received type {0}, wanted type {1}", actualType, type);
			throw gcnew Exception("Invalid message received.");
		}
		return msg;
	}

	void SendMessage(TestMessageType type, array<byte>^ payload)
	{
		TestMessageHeader header;
		header.TotalLength = (uint)(sizeof(TestMessageHeader) + payload->Length);
		header.MessageType = (uint)type;
		
		array<byte>^ headerBuffer = gcnew array<byte>(sizeof(TestMessageHeader));
		pin_ptr<byte> headerBuffer_pinned = &headerBuffer[0];
		*(TestMessageHeader*)headerBuffer_pinned = header;
		_socket->Send(headerBuffer);
		
		_socket->Send(payload);
	}

	void ThreadRoutine()
	{
		try {
			for (;;) {
				Console::WriteLine("Waiting for Negotiate");
				array<Byte>^ negotiate = ReceiveExpectedMessage(TestMessageType::Negotiate);

				Console::WriteLine("Received Negotiate:");
				NtlmUtil::DumpMessage(negotiate);

				SspiNtlmAuthenticator authenticator;
				authenticator.Initialize();

				array<byte>^ challenge = authenticator.GetChallenge(negotiate);

				Console::WriteLine("Sending Challenge:");
				NtlmUtil::DumpMessage(challenge);
				
				SendMessage(TestMessageType::Challenge, challenge);

				Console::WriteLine("Waiting for Response");

				array<byte>^ response = ReceiveExpectedMessage(TestMessageType::Response);

				Console::WriteLine("Received Response:");
				NtlmUtil::DumpMessage(response);

				String^ resulttext;
				bool succeeded;

				try {
					authenticator.VerifyResponse(response);
					Console::WriteLine("Authentication succeeded");
					resulttext = "OK";
					succeeded = true;
				} catch(Exception^ ex) {
					Console::WriteLine("Authentication failed");
					Util::DumpException(ex);
					resulttext = "FAILED: " + ex->Message;
					succeeded = false;
				}

				ResultMessage result;
				result.Succeeded = succeeded ? 1 : 0;

				Console::WriteLine("Sending Result: " + resulttext);

				Encoding^ encoding = Encoding::Unicode;
				array<byte>^ response_buffer = gcnew array<byte>(sizeof(ResultMessage) + encoding->GetByteCount(resulttext));
				pin_ptr<byte> response_pinned = &response_buffer[0];
				*(ResultMessage*)response_pinned = result;
				encoding->GetBytes(resulttext, 0, resulttext->Length, response_buffer, sizeof(ResultMessage));

				SendMessage(TestMessageType::Result, response_buffer);
			}

		} catch (Exception^ ex) {
			Console::WriteLine("Exception on client: " + _socket->RemoteEndPoint->ToString());
			Util::DumpException(ex);
		} finally {
			_socket->Close();
		}
		Console::WriteLine("Client thread has terminated.");
	}

public:
	static void StartThread(Socket^ socket)
	{
		Client^ client = gcnew Client(socket);
		Thread^ thread = gcnew Thread(gcnew ThreadStart(client, &Client::ThreadRoutine));
		thread->Start();
	}
};

ref class NtlmWinHost
{
public:

	static void Main(array<String^>^ args)
	{
		try {
			Socket^ listener = gcnew Socket(AddressFamily::InterNetwork, SocketType::Stream, ProtocolType::Tcp);

			IPEndPoint^ listenAddress = gcnew IPEndPoint(IPAddress::Any, NtlmUnitTestPort);

			try {
				listener->Bind(listenAddress);
			} catch(Exception^) {
				Console::WriteLine("Failed to bind to listen address: " + listenAddress);
				Console::WriteLine("Check to see if any other apps (including an instance of this one) are using the port.");
				throw;
			}

			listener->Listen(4);

			for (;;) {
				Console::WriteLine("Waiting for clients on address: " + listenAddress);
				Socket^ clientsocket = listener->Accept();
				Client::StartThread(clientsocket);
			}

		} catch(Exception^ ex) {
			Util::DumpException(ex);
		}
	}
};

int main(array<String^> ^args)
{
	NtlmWinHost::Main(args);
    return 0;
}









String^ FormatMessageFromSystem(ULONG message)
{
    array<Char>^ buffer = gcnew array<Char>(0x200);
    pin_ptr<Char> buffer_pinned = &buffer[0];
    int length;

    length = Util::FormatMessage(
        FORMAT_MESSAGE_FROM_SYSTEM,
        NULL,
        message,
        LANG_NEUTRAL,
        buffer_pinned,
        buffer->Length,
        NULL);

    if (length == 0)
        return String::Format("(unknown error 0x{0:x8} {0})", message);
    else {
        String^ b = gcnew String(buffer, 0, length);
        String^ result = String::Format("{0} (0x{1:x8} {1})", b, message, message);
        return result;
    }
}

String^ Util::FormatMessageFromSystem(ULONG message)
{
    return ::FormatMessageFromSystem(message);
}

void Util::DumpBuffer(PUCHAR buffer, int length)
{
    StringBuilder line;

    for (int i = 0; i < length; i += 0x10) {

        line.Length = 0;

        for (int j = 0; j < 0x10; j++) {

            if (i + j < length) {
                line.Append(" ");
                byte b = buffer[i + j];
                line.Append((Char)HexDigits[b >> 4]);
                line.Append((Char)HexDigits[b & 0xf]);
            } else {
                line.Append("   ");
            }
        }

        line.Append(" : ");
        for (int j = 0; j < 0x10; j++) {

            if (i + j < length) {
                byte b = buffer[i + j];
                if (b >= 32 && b <= 127) {
                    line.Append((Char)b);
                } else {
                    line.Append(".");
                }
            } else {
                break;
            }
        }

        Console::WriteLine(line.ToString());
    }
}


void Util::DumpBuffer(array<byte>^ buffer, int offset, int length)
{
    StringBuilder line;

    for (int i = 0; i < length; i += 0x10) {

        line.Length = 0;

        for (int j = 0; j < 0x10; j++) {

            if (i + j < length) {
                line.Append(" ");
                byte b = buffer[offset + i + j];
                line.Append((Char)HexDigits[b >> 4]);
                line.Append((Char)HexDigits[b & 0xf]);
            } else {
                line.Append("   ");
            }
        }

        line.Append(" : ");
        for (int j = 0; j < 0x10; j++) {

            if (i + j < length) {
                byte b = buffer[offset + i + j];
                if (b >= 32 && b <= 127) {
                    line.Append((Char)b);
                } else {
                    line.Append(".");
                }
            } else {
                break;
            }
        }

        Console::WriteLine(line.ToString());
    }
}



//
// General Information about an assembly is controlled through the following
// set of attributes. Change these attribute values to modify the information
// associated with an assembly.
//
[assembly:AssemblyTitleAttribute("NtlmWinHost")];
[assembly:AssemblyDescriptionAttribute("Unit test for NTLM authentication library")];
[assembly:AssemblyConfigurationAttribute("")];
[assembly:AssemblyCompanyAttribute("Microsoft")];
[assembly:AssemblyProductAttribute("NtlmWinHost")];
[assembly:AssemblyCopyrightAttribute("Copyright (c)  2006")];
[assembly:AssemblyTrademarkAttribute("")];
[assembly:AssemblyCultureAttribute("")];

//
// Version information for an assembly consists of the following four values:
//
//      Major Version
//      Minor Version
//      Build Number
//      Revision
//
// You can specify all the value or you can default the Revision and Build Numbers
// by using the '*' as shown below:

[assembly:AssemblyVersionAttribute("1.0.*")];

[assembly:ComVisible(false)];

[assembly:CLSCompliantAttribute(true)];

[assembly:SecurityPermission(SecurityAction::RequestMinimum, UnmanagedCode = true)];
