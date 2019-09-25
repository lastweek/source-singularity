// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

namespace NetStack
{
    namespace Runtime 
    {               
        // A timeout context declaration.
        // A module creates a context for a timeout event
        // and pass it to the runtime upon request.
        public class TimeOutContext 
        {
            // the timeout value
            protected uint timeValue;

            // the timeout handler
            protected TimeOutHandler handler;

            // module specific context
            protected object context;

            // the handler declaration
            public delegate NetStatus TimeOutHandler();

            // ctor
            public TimeOutContext(uint time,TimeOutHandler tHandler,object ctx)
            {
                timeValue=time;
                handler=tHandler;
                context=ctx;
            }

            // properties
            public TimeOutHandler Handler
            {
                get {return handler;} set {handler=value;}
            }

            public uint TimeOutValue
            {
                get {return timeValue;} set {timeValue=value;}
            }

            public object Context
            {
                get {return context;} set {context=value;}
            }
        }
    }
}
