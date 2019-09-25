// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

namespace System
{

    using System;
    // The base class for all event classes.
    //| <include path='docs/doc[@for="EventArgs"]/*' />
    public class EventArgs {
        //| <include path='docs/doc[@for="EventArgs.Empty"]/*' />
        public static readonly EventArgs Empty = new EventArgs();

        //| <include path='docs/doc[@for="EventArgs.EventArgs"]/*' />
        public EventArgs()
        {
        }
    }
}
