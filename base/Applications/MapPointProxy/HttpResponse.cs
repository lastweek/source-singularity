// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System.Collections.Specialized;

public class HttpResponse
{
    private string fContentType;
    private byte[] fBodyData;
    private StringDictionary fHeaders;
    private int fStatusCode;

    internal HttpResponse()
    {
        fHeaders = new StringDictionary();
    }

    public int ContentLength
    {
        get
        {
            if (fBodyData != null) {
                return fBodyData.Length;
            }
            else {
                return 0;
            }
        }
    }

    public string ContentType
    {
        get { return fContentType; }
        set { fContentType = value; }
    }

    public byte[] BodyData
    {
        get { return fBodyData; }
        set { fBodyData = value; }
    }

    public int StatusCode
    {
        get { return fStatusCode; }
        set { fStatusCode = value; }
    }

    public string GetHeader(string! headerName)
    {
        return fHeaders[headerName.ToLower()];
    }

    public void AddHeader(string! headerName, string! headerValue)
    {
        fHeaders[headerName.ToLower()] = headerValue;
    }
}
