// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace ManifestReader
{

	public class Pair
	{
		object first;
		object second;
		public object First
		{
			get { return first; }
		}

		public object Second
		{
			get { return second; }
		}

		public Pair(object first, object second)
		{
			this.first = first;
			this.second = second;
		}
	}
}
