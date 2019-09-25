////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    This file was ported, from the Coriolis codebase to Singularity.
//

namespace System.Web
{
    public class HttpException : System.Exception
    {
        // Do-nothing placeholder for now
        public HttpException(string message) :
            base(message)
        {
        }
    }
}
