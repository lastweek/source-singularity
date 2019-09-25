// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class: Environment
//
// Purpose: Provides some basic access to some environment
// functionality.
//
//============================================================  
namespace System
{
    using System.Globalization;
    using System.Collections;
    using System.Text;
    using System.Runtime.InteropServices;
    using System.Reflection;
    using System.Diagnostics;
    using Microsoft.Singularity;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="Environment"]/*' />
    public sealed class Environment {

        private Environment() {}              // Prevent from begin created

        //==================================TickCount===================================
        //Action: Gets the number of ticks since the system was started.
        //Returns: The number of ticks since the system was started.
        //Arguments: None
        //Exceptions: None
        //==============================================================================  
        //| <include path='docs/doc[@for="Environment.TickCount"]/*' />
        public static int TickCount {
            get {
                // 100ns to millisecond conversion.
                return unchecked((int)(SystemClock.KernelUpTime.Milliseconds));
            }
        }

        //===================================NewLine====================================
        //Action: A property which returns the appropriate newline string for the given
        //        platform.
        //Returns: \r\n on Win32.
        //Arguments: None.
        //Exceptions: None.
        //==============================================================================  
        //| <include path='docs/doc[@for="Environment.NewLine"]/*' />
        public static String NewLine {
            get {
                return "\r\n";
            }
        }
    }
}
