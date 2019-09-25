// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//
// This helper class assists in forming HTTP requests and retrieving the
// resulting data.
// 

using System;
using System.Collections;
using System.Collections.Specialized;
using System.Diagnostics;
using System.Globalization;
using System.Net;
using System.Net.Sockets;
using System.Text;

public class HttpRequest
{
    private string fRequestUri, fHost, fResource, fMethod, fContentType;
    private int fHostPort;
    private byte[] fRequestData;
    private Hashtable fRequestHeaders;
    private long fTimeout; // Zero for infinite

    // CONSTANTS
    private static string proxyHost = null;
    private static int proxyPort = 0;
    const int readIncrementSize = 1024 * 2; // 2Kbytes
    const int bodySizeGuess = 5 * 1024; // 5KBytes

    public static void ConfigureProxy(string host, int port)
    {
        proxyHost = host;
        proxyPort = port;
    }

    public HttpRequest(string! uri)
    {
        fRequestUri = uri;

        // Parse the URI into a host-part and a path-part.
        const string httpPrefix = "http://";
        if (!uri.StartsWith(httpPrefix)) {
            throw new ArgumentException("URI must begin with 'http://'");
        }

        int startIndex = httpPrefix.Length;
        int firstSlash = uri.IndexOf('/',startIndex);

        string fHost;
        if (firstSlash != -1) {
            fHost = uri.Substring(startIndex, firstSlash - startIndex);
            fResource = uri.Substring(firstSlash);
        }
        else {
            // Host is the entire Uri
            fHost = uri.Substring(startIndex);
            fResource = String.Empty;
        }

        int firstColon = fHost.IndexOf(':');

        if (firstColon != -1) {
            fHostPort = Int32.Parse(fHost.Substring(firstColon + 1));
        }
        else {
            fHostPort = 80; // default
        }

        this.fRequestHeaders = new Hashtable();
        this.fMethod = "GET";
        this.fHost = fHost;
    }

    public void AddHeader(string! headerName, string headerValue)
    {
        fRequestHeaders[headerName] = headerValue;
    }

    public string Method
    {
        get { return fMethod; }
        set { fMethod = value; }
    }

    public string ContentType
    {
        get { return fContentType; }
        set { fContentType = value; }
    }

    public byte[] RequestData
    {
        get { return fRequestData; }
        set { fRequestData = value; }
    }

    public long Timeout
    {
        get { return fTimeout; }
        set { fTimeout = value; }
    }

    public string Resource
    {
        get { return fResource; }
    }

    // Perform the HTTP hit and return the result!
    public HttpResponse GetResponse()
    {
        //
        // Step 1: Connect to the remote server
        //
        Socket httpSocket = new Socket(AddressFamily.InterNetwork, SocketType.Stream,
            ProtocolType.Tcp);

        string serverName, requestUri;
        int serverPort;

        if (proxyPort > 0) {
            serverName = proxyHost;
            serverPort = proxyPort;
            requestUri = fRequestUri; // Use the full URI
        }
        else {
            serverName = fHost;
            serverPort = fHostPort;
            requestUri = fResource; // Use just the resource
        }

        IPAddress serverAddress;

        try {
            serverAddress = IPAddress.Parse(serverName);
        }
        catch (Exception) {
            // Hostname didn't parse as an IP address; try to resolve it
            IPHostEntry! entry = (!)Dns.Resolve(serverName);
            IPAddress[]! addresses = (!)entry.AddressList;

            if (addresses.Length == 0) {
                throw new Exception("Couldn't resolve host name");
            }

            serverAddress = addresses[0];
        }

        IPEndPoint serverEndpoint = new IPEndPoint(serverAddress, serverPort);

        // Connect to the remote server
        httpSocket.Connect(serverEndpoint);

        //
        // Step 2: Formulate and transmit the request line and any supporting data
        //
        // Send the request line
        string requestLine = fMethod + " " + requestUri + " HTTP/1.1\r\nHost: " +
            fHost + "\r\nConnection: Close\r\n";

        // Send an indication of the request data content type and size, if appropriate
        if (fRequestData != null) {
            requestLine += "Content-Length: " + fRequestData.Length + "\r\n" +
                "Content-Type: " + fContentType + "\r\n";
        }

        // Add any user-specified headers
        foreach (string! headerName in fRequestHeaders.Keys) {
            requestLine += headerName + ": " + fRequestHeaders[headerName] + "\r\n";
        }

        requestLine += "\r\n";
        byte[] requestBytes = Encoding.ASCII.GetBytes(requestLine);
        httpSocket.Send(requestBytes);

        // Send any request data
        if (fRequestData != null) {
            httpSocket.Send(fRequestData);
        }

        // Signal we're done sending
        httpSocket.Shutdown(SocketShutdown.Send);

        //
        // Step 3: Parse the response line and headers
        //

        // Pump the response into an HttpHeadersParser
        ByteBuffer scratchBuffer = new ByteBuffer();
        HttpHeadersParser headerParser = new HttpHeadersParser(scratchBuffer);
        bool doneWithout100Continue = false, doneWithHeaders = false;
        int nextWritePos = 0;
        HttpResponse response = null;

        do
        {
            while (!doneWithHeaders) {
                // Make 2K available for each read
                scratchBuffer.EnsureSize(nextWritePos + readIncrementSize);
                int numReadBytes = httpSocket.Receive(scratchBuffer.UnderlyingBuffer, nextWritePos,
                    scratchBuffer.Size - nextWritePos, SocketFlags.None);

                if (numReadBytes == 0) {
                    // We ran out of data before we finished parsing headers.
                    throw new Exception("Unexpected end of data");
                }

                nextWritePos += numReadBytes;

                if (headerParser.Pump(nextWritePos)) {
                    // Finished parsing headers!
                    response = headerParser.GetResponse();
                    doneWithHeaders = true;
                }
            }

            if (response == null) {
                throw new Exception("HTTP response data unexpectedly null");
            }

            // Special case: if we see a 100-continue, we want to carefully start
            // over at the next chunk of data!
            if (response.StatusCode == 100) {
                // Switch to a new scratch buffer that will contain the data
                // following the 100-continue.
                int remainderBeginning = headerParser.BodyDataOffset;
                int remainderLength = nextWritePos - remainderBeginning;
                ByteBuffer newScratch = new ByteBuffer();
                ByteBuffer oldScratch = scratchBuffer;

                // Reset parsing by creating a new parser
                headerParser = new HttpHeadersParser(newScratch);

                // Switch over!
                scratchBuffer = newScratch;
                nextWritePos = remainderLength;

                if (remainderLength > 0) {
                    // Copy the beginning of the next data chunk into newScratch
                    newScratch.EnsureSize(remainderLength);
                    Buffer.BlockCopy(oldScratch.UnderlyingBuffer, remainderBeginning,
                        newScratch.UnderlyingBuffer, 0, remainderLength);

                    // Make sure the fragment we were already holding gets pumped in
                    if (headerParser.Pump(nextWritePos)) {
                        // Interestingly, we're already done
                        response = headerParser.GetResponse();
                        if (response == null) {
                            throw new Exception("HTTP response data unexpectedly null");
                        }
                        Debug.Assert(response.StatusCode != 100);
                        doneWithout100Continue = true;
                    }
                    else {
                        // Go back and carry on
                        doneWithHeaders = false;
                    }
                }
                else {
                    // The chunk we were chewing on exactly contained the 100-continue,
                    // so we definitely need to go back and read some more...
                    doneWithHeaders = false;
                }
            }
            else {
                // The response was not 100-continue, so we're all done
                doneWithout100Continue = true;
            }
        }
        while (!doneWithout100Continue);

        //
        // Step 4: Process the body data
        //
        // Now figure out how we're going to deal with the actual body
        // of the response. We almost certainly already have an initial
        // chunk of the body data in the scratchBuffer, since we read the
        // headers in 2K chunks
        //
        int bodyScratchBeginning = headerParser.BodyDataOffset;
        int scratchBodyLength = nextWritePos - bodyScratchBeginning;

        string transferEncoding = response.GetHeader("Transfer-Encoding");
        if (transferEncoding != null &&
            transferEncoding.ToLower().Equals("chunked"))
        {
            // Chunked encoding is special: the beginning of the body data
            // already specifies some chunk information. Run this through our
            // chunk decoder to straighten it out.
            byte[] initialBodyChunk = scratchBuffer.TrimAndCopy(bodyScratchBeginning, scratchBodyLength);
            ChunkedEncodingParser chunkParser = new ChunkedEncodingParser(initialBodyChunk, httpSocket);
            ByteBuffer bodyData = chunkParser.Run();
            response.BodyData = bodyData.TrimAndCopy(bodyData.Size);
        }
        else {
            ByteBuffer bodyBuffer;

            // Non-chunked encoding. First, move the beginning of the body
            // data to a new ByteBuffer for sanity.
            // Separate out any initial body data into a new ByteBuffer, for sanity
            int bodySize = (response.ContentLength > 0) ? response.ContentLength : bodySizeGuess;

            // Hard to imagine how this would happen...
            if (bodySize < scratchBodyLength) {
                bodySize = scratchBodyLength;
            }

            bodyBuffer = new ByteBuffer(bodySize);
            Buffer.BlockCopy(scratchBuffer.UnderlyingBuffer, bodyScratchBeginning,
                bodyBuffer.UnderlyingBuffer, 0, scratchBodyLength);
            int nextBodyPos = scratchBodyLength;

            if (response.ContentLength > 0) {
                // Read until we've gotten exactly the expected number of bytes
                int bodyDataLeft = response.ContentLength - scratchBodyLength;

                while (bodyDataLeft > 0) {
                    int numReadBytes = httpSocket.Receive(bodyBuffer.UnderlyingBuffer, nextBodyPos,
                        bodyDataLeft, SocketFlags.None);

                    if (numReadBytes == 0) {
                        throw new Exception("Connection closed unexpectedly");
                    }

                    nextBodyPos += numReadBytes;
                    bodyDataLeft -= numReadBytes;
                }
            }
            else {
                // No indicated ContentLength; Just read until the connection gets closed!
                int numReadBytes = 0;

                // Read until the remote side closes
                do
                {
                    bodyBuffer.EnsureSize(bodyBuffer.Size + readIncrementSize);
                    numReadBytes = httpSocket.Receive(bodyBuffer.UnderlyingBuffer, nextBodyPos,
                        bodyBuffer.Size - nextBodyPos, SocketFlags.None);
                    nextBodyPos += numReadBytes;
                }
                while (numReadBytes > 0);
            }

            response.BodyData = bodyBuffer.TrimAndCopy(nextBodyPos);
        }

        // All done!
        httpSocket.Close();

        return response;
    }

    private class HttpHeadersParser
    {
        // The buffer we are chewing on
        ByteBuffer fBuffer;

        // The response we are forming
        private HttpResponse fResponse;
        private int fContentLength;

        // Working state
        private State fState;
        private int fPosition;
        private int fBufferLimit; // One more than the last usable index in the buffer

        private enum State
        {
            BeforeStatusLine,
            ParsingHeaders,
            Complete
        }

        public HttpHeadersParser(ByteBuffer buffer)
        {
            fBuffer = buffer;
            fResponse = new HttpResponse();
        }

        public bool Pump(int newBufferLimit)
        {
            bool allDone = false, outOfRoom = false;

            while ((!allDone) && (!outOfRoom)) {
                PumpInternal(newBufferLimit, out allDone, out outOfRoom);
            }

            return allDone;
        }

        private void PumpInternal(int newBufferLimit, out bool allDone, out bool outOfRoom)
        {
            fBufferLimit = newBufferLimit;

            if (fState == State.Complete) {
                // We've already completed
                allDone = true;
                outOfRoom = false;
                return;
            }

            int CRLFOffset = FindNextCRLF(fPosition, fBufferLimit);

            if (fState == State.BeforeStatusLine) {
                if (CRLFOffset != -1) {
                    HandleStatusLine(fPosition, CRLFOffset - fPosition);
                    fState = State.ParsingHeaders;
                    fPosition = CRLFOffset + 2;
                    allDone = false;
                    outOfRoom = false;
                    return;
                }
                else {
                    // We couldn't see another CRLF before the end of the
                    // usable part of the buffer, so we're out of room.
                    allDone = false;
                    outOfRoom = true;
                    return;
                }
            }
            else if (fState == State.ParsingHeaders) {
                // Special case: if the unprocessed part starts with CRLF it
                // means we are looking at the end of the headers, since we consume
                // the trailing CRLF on a single header line when parsing.
                if (CRLFOffset == fPosition) {
                    fState = State.Complete;
                    fPosition += 2;
                    allDone = true;
                    outOfRoom = false;
                    return;
                }
                else if (CRLFOffset != -1) {
                    HandleHeaderLine(fPosition, CRLFOffset - fPosition);
                    fPosition = CRLFOffset + 2;
                    allDone = false;
                    outOfRoom = false;
                    return;
                }
                else {
                    // We couldn't see another CRLF before the end of the
                    // usable part of the buffer, so we're out of room.
                    allDone = false;
                    outOfRoom = true;
                    return;
                }
            }

            // Someone must have added a state or mucked up the code
            allDone = false;
            outOfRoom = false;
            Debug.Assert(false);
        }

        public HttpResponse GetResponse()
        {
            if (fState == State.Complete) {
                return fResponse;
            }
            else {
                // Not allowed to have half-baked results!
                return null;
            }
        }

        public int BodyDataOffset
        {
            get
            {
                if (fState == State.Complete) {
                    return fPosition;
                }
                else {
                    // No answer if we're not done processing
                    return -1;
                }
            }
        }

        public int ContentLength
        {
            get
            {
                if (fState == State.Complete) {
                    return fContentLength;
                }
                else {
                    // Not available if we're not done processing
                    return -1;
                }
            }
        }

        private void HandleStatusLine(int startOffset, int length)
        {
            string status = Encoding.ASCII.GetString(fBuffer.UnderlyingBuffer, startOffset, length);
            const string HTTP11 = "HTTP/1.1 ";

            if (!status.StartsWith(HTTP11)) {
                throw new Exception("Response was not HTTP/1.1");
            }

            int secondSpace = status.IndexOf(' ', HTTP11.Length);
            string statusString;

            if (secondSpace == -1) {
                // Assume this means there is a status code with no explanation string
                statusString = status.Substring(HTTP11.Length);
            }
            else {
                // Grab just the status code
                statusString = status.Substring(HTTP11.Length, secondSpace - HTTP11.Length);
            }

            int statusCode = Int32.Parse(statusString);
            fResponse.StatusCode = statusCode;
        }

        private void HandleHeaderLine(int startOffset, int length)
        {
            string header = Encoding.ASCII.GetString(fBuffer.UnderlyingBuffer, startOffset, length);
            int firstColon = header.IndexOf(':');

            if (firstColon == -1) {
                throw new Exception("Malformed header string");
            }

            string headerName = header.Substring(0, firstColon);
            string headerValue = header.Substring(firstColon + 1).Trim();

            if (headerName.ToLower().Equals("content-length")) {
                fContentLength = Int32.Parse(headerValue);
            }
            else {
                fResponse.AddHeader(headerName, headerValue);
            }
        }

        private int FindNextCRLF(int startOffset, int limitOffset)
        {
            int offset = startOffset;

            while (offset < limitOffset) {
                if (fBuffer[offset] == (byte)'\r') {
                    if ((offset + 1 < limitOffset) && (fBuffer[offset + 1] == (byte)'\n')) {
                        return offset;
                    }
                }

                offset++;
            }

            return -1;
        }
    }

    private class ChunkedEncodingParser
    {
        // This buffer is what we start with; it has an initial
        // fragment of the body data
        private byte[] fInitialFragment;
        private int fFragmentOffset; // How far into fInitialFragment we are
        private Socket fSocket; // Socket to read additional data from
        private byte[] fSingleByte;

        public ChunkedEncodingParser(byte[] initialFragment, Socket readSocket)
        {
            fInitialFragment = initialFragment;
            fSocket = readSocket;
            fSingleByte = new byte[1];
        }

        public ByteBuffer! Run()
        {
            ByteBuffer bodyData = new ByteBuffer();
            int chunkSize = 0;

            while (true) {
                ByteBuffer! chunkLine = ReadToCRLF();
                string! chunkString = (!)Encoding.ASCII.GetString(chunkLine.UnderlyingBuffer, 0, chunkLine.Size);
                chunkString = (!)chunkString.Trim();
                int firstSemi = chunkString.IndexOf(';');

                if (firstSemi != -1) {
                    // Use only the portion before the semicolon
                    chunkSize = Int32.Parse(chunkString.Substring(0, firstSemi),
                        NumberStyles.AllowHexSpecifier);
                }
                else {
                    // No semicolon; use the entire line
                    chunkSize = Int32.Parse(chunkString, NumberStyles.AllowHexSpecifier);
                }

                if (chunkSize == 0) {
                    // We're done! Don't bother reading the trailer
                    return bodyData;
                }

                // Read in the amount indicated by the chunk header. It may take multiple passes
                // to do this.
                int writeOffset = bodyData.Size;
                bodyData.EnsureSize(bodyData.Size + chunkSize);

                while (chunkSize > 0) {
                    int numBytesRead = MassRead(bodyData.UnderlyingBuffer, writeOffset, chunkSize);
                    chunkSize -= numBytesRead;
                    writeOffset += numBytesRead;
                }

                // Peel off the CRLF that trails a chunk
                ByteBuffer emptyLine = ReadToCRLF();
                if (emptyLine.Size != 0) {
                    throw new Exception("Malformed HTTP/1.1 chunk -- no trailing lone CRLF");
                }
            }
        }

        private ByteBuffer! ReadToCRLF()
        {
            ByteBuffer retval = new ByteBuffer();
            InnerReadToCRLF(retval);
            return retval;
        }

        private void InnerReadToCRLF(ByteBuffer buffer) // buffer can be null
        {
            // Read characters into buffer until we see a CRLF (don't include)
            byte nextByte = GetNextByte();

            while (true) {
                if (nextByte == (byte)'\r') {
                    nextByte = GetNextByte();

                    if (nextByte == (byte)'\n') {
                        // Done
                        return;
                    }
                    else {
                        if (buffer != null) {
                            buffer.Add((byte)'\r');
                        }

                        // Don't read again; nextByte might
                        // be the first byte of CRLF.
                    }
                }
                else {
                    if (buffer != null) {
                        buffer.Add(nextByte);
                    }
                    nextByte = GetNextByte();
                }
            }
        }

        private void DiscardToCRLF()
        {
            InnerReadToCRLF(null);
        }

        private byte GetNextByte()
        {
            if (fFragmentOffset < fInitialFragment.Length) {
                return fInitialFragment[fFragmentOffset++];
            }
            else {
                int received = fSocket.Receive(fSingleByte, 0, 1, SocketFlags.None);
                if (received == 1) {
                    return fSingleByte[0];
                }
                else {
                    throw new Exception("Connection closed unexpectedly");
                }
            }
        }

        private int MassRead(byte[] buffer, int offset, int maxLength)
        {
            if (fFragmentOffset < fInitialFragment.Length) {
                // Still data left in the original fragment; return as much
                // of that as possible.
                int initialFragmentLeft = fInitialFragment.Length - fFragmentOffset;
                int amountToUse = maxLength <= initialFragmentLeft ? maxLength : initialFragmentLeft;
                Buffer.BlockCopy(fInitialFragment, fFragmentOffset, buffer, offset, amountToUse);
                fFragmentOffset += amountToUse;
                return amountToUse;
            }
            else {
                // No data left in the initial fragment; read from the network.
                return fSocket.Receive(buffer, offset, maxLength, SocketFlags.None);
            }
        }
    }
}
