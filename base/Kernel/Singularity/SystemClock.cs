////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   SystemClock.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.Hal;

namespace Microsoft.Singularity
{
    /// <remarks>
    /// The system clock provides an interface to the clock device that
    /// caters for the difference between the Clock and UTC.  The Clock time
    /// is typically held in persistent storage and set by the user.  The
    /// clock time is typically stored local time rather than UTC.
    /// </remarks>
    [CLSCompliant(false)]
    public class SystemClock
    {
        private static HalClock clockDevice;
        private static long rtcUtcOffset;
        
        private const int year = 2007;
        private const int month = 1;
        private const int day = 1;
         
        /// <summary>
        /// Constructor.
        /// <param name="device">Underlying clock device to use.</param>
        /// <param name="rtcUtcDelta">The UTC offset of the Real-Time Clock
        /// associated with the clock device. </param>
        /// </summary>
        [NoHeapAllocation]
        public static void Initialize(HalClock device, long rtcUtcDelta)
        {
            clockDevice  = device;
            rtcUtcOffset = rtcUtcDelta;
        }

        /// <summary>
        /// Get the offset applied to the Real-Time Clock device.
        /// </summary>
        [NoHeapAllocation]
        public static long GetRtcUtcOffset(long ticks)
        {
            return rtcUtcOffset;
        }

        /// <summary>
        /// Set the offset applied to the Real-Time Clock device.
        /// <param name="ticks">Offset in units of 100ns.</param>
        /// <returns>true on success, false if offset is greater than 12 hours.
        /// </returns>
        /// </summary>
        [NoHeapAllocation]
        public static bool SetRtcUtcOffset(long ticks)
        {
            if (UtcOffsetValid(ticks) == false)
                return false;
            rtcUtcOffset = ticks;
            return true;
        }

        public static DateTime GetUtcTime()
        {
            if (clockDevice == null) {
                // the clock device is not initialized yet 
                // This will happen when we try to set the times for 
                // the inital objects in the Directory Service
                // We will cons up a fixed value; 
                return new DateTime(year,month,day);
            }
            DateTime rtc = new DateTime(clockDevice.GetRtcTime());
            return rtc.AddTicks(rtcUtcOffset);
        }

        public static void SetUtcTime(DateTime now)
        {
            DateTime utc = now.AddTicks(-rtcUtcOffset);
            clockDevice.SetRtcTime(utc.Ticks);
        }

        /// <summary> Get the time elapsed since booting.  All
        /// kernel timers and timing calculations should be
        /// based on the time returned by this method to avoid
        /// problems following <c>TimeZone</c> changes or time updates.
        /// <returns>Time in units of 100ns. </returns>
        /// </summary>
        public static TimeSpan KernelUpTime
        {
            [NoHeapAllocation]
            get {
                return new TimeSpan(clockDevice.GetKernelTicks());
            }
        }

        /// <summary> Get the time since booting in kernel ticks of 100ns.
        /// </summary>
        //
        //[NoHeapAllocation]
        //public static long GetKernelTicks()
        //{
        //  return clockDevice.GetKernelTicks();
        //}
        //

        [NoHeapAllocation]
        private static bool UtcOffsetValid(long offset)
        {
            return (offset >= TimeSpan.TicksPerDay / 2 &&
                    offset <= TimeSpan.TicksPerDay / 2);
        }
    }
}
