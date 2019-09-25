// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Diagnostics;
using System.Text;
using Microsoft.Singularity.Crypto;

public class HttpAuthenticator
{
    private HttpRequest fRequest;
    private string fUsername, fPassword;
    private MD5 fMD5;

    public HttpAuthenticator(HttpRequest request, string username, string password)
    {
        fRequest = request;
        fUsername = username;
        fPassword = password;
        fMD5 = new MD5();
    }

    public HttpResponse GetResponse()
    {
        // First try the original request
        HttpResponse response = fRequest.GetResponse();

        if (response == null) {
            throw new Exception("Initial HTTP request failed");
        }

        int status = response.StatusCode;

        if (status != 401) {
            // No authentication was actually required
            return response;
        }
        else {
            // Authentication is required. Go spelunking for the crypto challenge.
            string challenge = response.GetHeader("WWW-Authenticate");

            if (challenge == null) {
                throw new Exception("401 without a WWW-Authenticate header");
            }

            if (!challenge.StartsWith("Digest")) {
                throw new Exception("Invalid WWW-Authenticate header");
            }

            string realm = GetTaggedQuotedString(challenge, "realm");
            string nonce = GetTaggedQuotedString(challenge, "nonce");
            string opaque = GetTaggedQuotedString(challenge, "opaque");
            string algorithm = GetTaggedQuotedString(challenge, "algorithm");

            if ((algorithm != null) && (!algorithm.ToLower().Equals("md5"))) {
                throw new Exception("Unknown authentication scheme");
            }

            if ((realm == null) || (nonce == null)) {
                throw new Exception("Missing essential elements of WWW-Challenge");
            }

            // Compute the crypto response
            string authResponse = "Digest username=\"" + fUsername +
                "\",realm=\"" + realm +
                "\",nonce=\"" + nonce +
                "\",uri=\"" + fRequest.Resource +
                "\",response=\"";

            //
            // The crypto response is specified (RFC 2069) as:
            //
            // MD5( concat(A1, ":", B))
            // where A1 is:  MD5( concat( username, ":", realm, ":", password) )
            // and B is:     concat( nonce, ":", A2)
            // and A2 is:    MD5( concat (method, ":", digest-uri) )
            // Where MD5(X) is a string of hex digits representing the MD5 digest of X.
            // Got all that?
            //

            // Form A1 = MD5(username : realm : password)
            string a1 = MD5(fUsername + ":" + realm + ":" + fPassword);

            // Form A2 = md5(method : digest-uri)
            string a2 = MD5(fRequest.Method + ":" + fRequest.Resource);

            // Form B = nonce : A2
            string b = nonce + ":" + a2;

            // Form the unhashed final answer as MD5(A1 : B)
            authResponse += MD5(a1 + ":" + b) + "\"";

            // Echo the server's opaque string if present.
            if (opaque != null) {
                authResponse += ",opaque=\"" + opaque + "\"";
            }

            fRequest.AddHeader("Authorization", authResponse);

            // Rerun the request
            response = fRequest.GetResponse();

            if ((response != null) && (response.StatusCode == 401)) {
                // Authentication failed; credentials must be bad
                throw new Exception("Bad credentials");
            }

            // Looks like it worked after authentication
            return response;
        }
    }

    private string GetTaggedQuotedString(string! baseString, string tagName)
    {
        string tagPreamble = tagName + "=\"";
        int tagStart = baseString.IndexOf(tagPreamble);

        if (tagStart == -1) {
            return null;
        }

        int tagEnd = tagStart + tagPreamble.Length;
        int quoteEnd = baseString.IndexOf('"', tagEnd);

        if (quoteEnd == -1) {
            throw new Exception("Malformed tagged+quoted string");
        }

        return baseString.Substring(tagEnd, quoteEnd - tagEnd);
    }

    private string MD5(string! hashValue)
    {
        byte[] vals = Encoding.ASCII.GetBytes(hashValue);
        byte[] result = (!)fMD5.Hash(vals);
        return ToHexString(result);
    }

    private string ToHexString(byte[]! vals)
    {
        string retval = String.Empty;

        for (int i = 0; i < vals.Length; ++i) {
            retval += vals[i].ToString("x2");
        }

        return retval;
    }
}
