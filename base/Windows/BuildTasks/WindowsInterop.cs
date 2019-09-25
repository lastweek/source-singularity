// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

#if ENABLE_INTEROP

using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Text;

namespace Windows
{
    static class User32
    {
        [DllImport(User32DllName, CharSet=CharSet.Unicode, ExactSpelling=true, SetLastError=true)]
        public static extern bool PostThreadMessageW(uint threadId, uint message, IntPtr wParam, IntPtr lParam);

        [DllImport(User32DllName, CharSet = CharSet.Unicode, ExactSpelling = true, SetLastError = true)]
        public static extern unsafe bool TranslateMessage(MSG* msg);

        [DllImport(User32DllName, CharSet = CharSet.Unicode, ExactSpelling = true, SetLastError = true)]
        public static extern unsafe bool GetMessageW([Out]MSG* msg, IntPtr hwnd, uint wMsgFilterMin, uint wMsgFilterMax);

        [DllImport(User32DllName, CharSet = CharSet.Unicode, ExactSpelling = true, SetLastError = true)]
        public static extern unsafe bool PeekMessageW([Out]MSG* msg, IntPtr hwnd, uint wMsgFilterMin, uint wMsgFilterMax, uint wRemoveMsg);

        public const uint PM_REMOVE = 1;



        [DllImport(User32DllName, CharSet = CharSet.Unicode, ExactSpelling = true, SetLastError = true)]
        public static extern unsafe IntPtr DispatchMessageW([Out]MSG* msg);

        [DllImport(User32DllName, SetLastError = true)]
        public static extern uint RegisterWindowMessage(string name);

        [DllImport(User32DllName, SetLastError = true)]
        public unsafe static extern Kernel32.WaitResult MsgWaitForMultipleObjects(
            int nCount,
            IntPtr* pHandles,
            bool bWaitAll,
            uint dwMilliseconds,
            uint dwWakeMask
            );

        /// <summary>
        /// Event mask for MsgWaitForMultipleObjects.
        /// </summary>
        public static uint QS_ALLEVENTS = 0x04bf;

        public const uint InfiniteTimeout = ~0u;

        const string User32DllName = "USER32.DLL";

        public const uint WM_NULL = 0;
    }

    static class Kernel32
    {
        [DllImport(DllName)]
        public static extern uint GetCurrentThreadId();

        /// <summary>
        /// Results for WaitFor functions (including MsgWaitForMultipleObjects)
        /// </summary>
        public enum WaitResult : uint
        {
            Object0 = 0,
            Object1 = 1,
            Object2 = 2,
            // ... up to 63
            
            Timeout = 258,
            Failed = ~0u
        }

        const string DllName = "KERNEL32.DLL";
    }

    [StructLayout(LayoutKind.Sequential)]
    struct MSG
    {
        public IntPtr hwnd;
        public uint message;
        public IntPtr wParam;
        public IntPtr lParam;
        public uint time;
        public POINT pt;
    }

    [StructLayout(LayoutKind.Sequential)]
    struct POINT
    {
        public int x;
        public int y;
    }
}

#endif
