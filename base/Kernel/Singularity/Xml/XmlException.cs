// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;

namespace Microsoft.Singularity.Xml
{
    /// <summary>
    /// Summary description for XmlException.
    /// </summary>
    public class XmlException : Exception
    {
        public readonly int line;
        public XmlException(int line, string message) : base(message)
        {
            this.line = line;
        }
    }
}
