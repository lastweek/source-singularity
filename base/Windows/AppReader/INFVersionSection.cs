// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace ManifestReader
{
    using System;
    using System.IO;
    using System.Collections;
    using System.Xml;
    using System.Diagnostics;

	public class INFVersionSection : INFSection 
	{	
		string guid;
		public string Guid
		{
			get
			{
				return guid;
			}
			set
			{
				guid = value;
			}
		}

		public INFVersionSection(string line) : base(line)
		{
			guid = null;
		}
	}
}
