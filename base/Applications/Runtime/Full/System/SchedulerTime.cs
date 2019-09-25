// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
//   Defines absolute time as used by the scheduler that is independent of the
//   DateTime/timezone settings.
//
//   Used to keep track of timeouts and deadline in thread scheduling
//
// ==--==
namespace System
{

    using Microsoft.Singularity;

    using System;
    using System.Threading;
    using System.Globalization;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using CultureInfo = System.Globalization.CultureInfo;

#if !SINGULARITY_KERNEL
    using Microsoft.Singularity.V1.Services;
#endif

    // This value type represents an absolute time on the scheduler timeline,
    // which is kernel time increasing monotonically and independently of
    // the world time the machine thinks it is on.
    // The reason to separate world time and scheduler time is that world time can
    // change at any time due to users changing the time and date, or due to
    // adjustments for accuracy or daylight-savings.
    //
    [StructLayout(LayoutKind.Auto)]
    [AccessedByRuntime("referenced by c++ via Thread")]
    public struct SchedulerTime : IComparable
    {
        // Number of 100ns ticks per time unit
        public const long TicksPerMillisecond = 10000;
        public const long TicksPerSecond = TicksPerMillisecond * 1000;
        public const long TicksPerMinute = TicksPerSecond * 60;
        public const long TicksPerHour = TicksPerMinute * 60;
        public const long TicksPerDay = TicksPerHour * 24;

        // Number of milliseconds per time unit
        private const int MillisPerSecond = 1000;
        private const int MillisPerMinute = MillisPerSecond * 60;
        private const int MillisPerHour = MillisPerMinute * 60;
        private const int MillisPerDay = MillisPerHour * 24;

        // Number of days in a non-leap year
        private const int DaysPerYear = 365;
        // Number of days in 4 years
        private const int DaysPer4Years = DaysPerYear * 4 + 1;
        // Number of days in 100 years
        private const int DaysPer100Years = DaysPer4Years * 25 - 1;
        // Number of days in 400 years
        private const int DaysPer400Years = DaysPer100Years * 4 + 1;

        private const int DaysTo10000 = DaysPer400Years * 25;

        private const long MinTicks = 0;
        private const long MaxTicks = DaysTo10000 * TicksPerDay - 1;
        private const long MaxMillis = (long)DaysTo10000 * MillisPerDay;

        //| <include path='docs/doc[@for="SchedulerTime.MinValue"]/*' />
        public static readonly SchedulerTime MinValue = new SchedulerTime(MinTicks);
        //| <include path='docs/doc[@for="SchedulerTime.MaxValue"]/*' />
        public static readonly SchedulerTime MaxValue = new SchedulerTime(MaxTicks);

        //
        // NOTE yslin: Before the time zone is introduced, ticks is based on 1/1/0001 local time.
        //
        private long ticks;

        // Constructs a SchedulerTime from a tick count. The ticks
        // argument specifies the date as the number of 100-nanosecond intervals
        // that have elapsed since 1/1/0001 12:00am.
        //
        //| <include path='docs/doc[@for="SchedulerTime.SchedulerTime"]/*' />
        [NoHeapAllocation]
        public SchedulerTime(long ticks) {
            if (ticks < MinTicks) {
                this.ticks = MinTicks;
            }
            else if (ticks > MaxTicks) {
                this.ticks = MaxTicks;
            }
            else {
                this.ticks = ticks;
            }
        }



        // Returns the SchedulerTime resulting from adding the given
        // TimeSpan to this SchedulerTime.
        //
        //| <include path='docs/doc[@for="SchedulerTime.Add"]/*' />
        [NoHeapAllocation]
        public SchedulerTime Add(TimeSpan value) {
            return new SchedulerTime(ticks + value._ticks);
        }

        // Returns the SchedulerTime resulting from adding a number of
        // time units to this SchedulerTime.
        private SchedulerTime Add(long value, int scale) {
            long millis = value * scale;
            if (millis <= -MaxMillis || millis >= MaxMillis) {
                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_AddValue");
            }
            return new SchedulerTime(ticks + millis * TicksPerMillisecond);
        }

        // Returns the SchedulerTime resulting from adding a number of
        // days to this SchedulerTime. The result is computed by rounding the
        // fractional number of days given by value to the nearest
        // millisecond, and adding that interval to this SchedulerTime. The
        // value argument is permitted to be negative.
        //
        //| <include path='docs/doc[@for="SchedulerTime.AddDays"]/*' />
        public SchedulerTime AddDays(long value) {
            return Add(value, MillisPerDay);
        }

        // Returns the SchedulerTime resulting from adding a number of
        // hours to this SchedulerTime. The result is computed by rounding the
        // fractional number of hours given by value to the nearest
        // millisecond, and adding that interval to this SchedulerTime. The
        // value argument is permitted to be negative.
        //
        //| <include path='docs/doc[@for="SchedulerTime.AddHours"]/*' />
        public SchedulerTime AddHours(long value) {
            return Add(value, MillisPerHour);
        }

        // Returns the SchedulerTime resulting from the given number of
        // milliseconds to this SchedulerTime. The result is computed by rounding
        // the number of milliseconds given by value to the nearest integer,
        // and adding that interval to this SchedulerTime. The value
        // argument is permitted to be negative.
        //
        //| <include path='docs/doc[@for="SchedulerTime.AddMilliseconds"]/*' />
        public SchedulerTime AddMilliseconds(long value) {
            return Add(value, 1);
        }

        // Returns the SchedulerTime resulting from adding a number of
        // minutes to this SchedulerTime. The result is computed by rounding the
        // fractional number of minutes given by value to the nearest
        // millisecond, and adding that interval to this SchedulerTime. The
        // value argument is permitted to be negative.
        //
        //| <include path='docs/doc[@for="SchedulerTime.AddMinutes"]/*' />
        public SchedulerTime AddMinutes(long value) {
            return Add(value, MillisPerMinute);
        }

        // Returns the SchedulerTime resulting from adding a number of
        // seconds to this SchedulerTime. The result is computed by rounding the
        // fractional number of seconds given by value to the nearest
        // millisecond, and adding that interval to this SchedulerTime. The
        // value argument is permitted to be negative.
        //
        //| <include path='docs/doc[@for="SchedulerTime.AddSeconds"]/*' />
        public SchedulerTime AddSeconds(long value) {
            return Add(value, MillisPerSecond);
        }

        // Returns the SchedulerTime resulting from adding the given number of
        // 100-nanosecond ticks to this SchedulerTime. The value argument
        // is permitted to be negative.
        //
        //| <include path='docs/doc[@for="SchedulerTime.AddTicks"]/*' />
        public SchedulerTime AddTicks(long value) {
            return new SchedulerTime(ticks + value);
        }


        // Compares two SchedulerTime values, returning an integer that indicates
        // their relationship.
        //
        //| <include path='docs/doc[@for="SchedulerTime.Compare"]/*' />
        [NoHeapAllocation]
        public static int Compare(SchedulerTime t1, SchedulerTime t2) {
            if (t1.ticks > t2.ticks) return 1;
            if (t1.ticks < t2.ticks) return -1;
            return 0;
        }

        // Compares this SchedulerTime to a given object. This method provides an
        // implementation of the IComparable interface. The object
        // argument must be another SchedulerTime, or otherwise an exception
        // occurs.  Null is considered less than any instance.
        //
        // Returns a value less than zero if this  object
        //| <include path='docs/doc[@for="SchedulerTime.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) return 1;
            if (!(value is SchedulerTime)) {
                throw new ArgumentException("Arg_MustBeSchedulerTime");
            }

            long t = ((SchedulerTime)value).ticks;
            if (ticks > t) return 1;
            if (ticks < t) return -1;
            return 0;
        }


        // Return the tick count corresponding to the given hour, minute, second.
        // Will check the if the parameters are valid.
        private static long TimeToTicks(int hour, int minute, int second)
        {
            //TimeSpan.TimeToTicks is a family access function which does no error checking, so
            //we need to put some error checking out here.
            if (hour >= 0 && hour < 24 && minute >= 0 && minute < 60 && second >= 0 && second < 60) {
                return (TimeSpan.TimeToTicks(hour, minute, second));
            }
            throw new ArgumentOutOfRangeException("ArgumentOutOfRange_BadHourMinuteSecond");
        }


        // Checks if this SchedulerTime is equal to a given object. Returns
        // true if the given object is a boxed SchedulerTime and its value
        // is equal to the value of this SchedulerTime. Returns false
        // otherwise.
        //
        //| <include path='docs/doc[@for="SchedulerTime.Equals"]/*' />
        public override bool Equals(Object value) {
            if (value is SchedulerTime) {
                return ticks == ((SchedulerTime)value).ticks;
            }
            return false;
        }

        // Compares two SchedulerTime values for equality. Returns true if
        // the two SchedulerTime values are equal, or false if they are
        // not equal.
        //
        //| <include path='docs/doc[@for="SchedulerTime.Equals1"]/*' />
        [NoHeapAllocation]
        public static bool Equals(SchedulerTime t1, SchedulerTime t2) {
            return t1.ticks == t2.ticks;
        }

        // Returns the date part of this SchedulerTime. The resulting value
        // corresponds to this SchedulerTime with the time-of-day part set to
        // zero (midnight).
        //
        //| <include path='docs/doc[@for="SchedulerTime.Date"]/*' />
        public SchedulerTime Date {
            get { return new SchedulerTime(ticks - ticks % TicksPerDay); }
        }

        // Returns the hash code for this SchedulerTime.
        //
        //| <include path='docs/doc[@for="SchedulerTime.GetHashCode"]/*' />
        public override int GetHashCode() {
            return (int)ticks ^ (int)(ticks >> 32);
        }

        public long TotalDays {
            [NoHeapAllocation]
            get { return (ticks / TicksPerDay); }
        }

        // Returns the hour part of this SchedulerTime. The returned value is an
        // integer between 0 and 23.
        //
        //| <include path='docs/doc[@for="SchedulerTime.Hour"]/*' />
        public int Hour {
            [NoHeapAllocation]
            get { return (int)((ticks / TicksPerHour) % 24); }
        }

        // Returns the millisecond part of this SchedulerTime. The returned value
        // is an integer between 0 and 999.
        //
        //| <include path='docs/doc[@for="SchedulerTime.Millisecond"]/*' />
        public int Millisecond {
            [NoHeapAllocation]
            get { return (int)((ticks / TicksPerMillisecond) % 1000); }
        }

        // Returns the minute part of this SchedulerTime. The returned value is
        // an integer between 0 and 59.
        //
        //| <include path='docs/doc[@for="SchedulerTime.Minute"]/*' />
        public int Minute {
            [NoHeapAllocation]
            get { return (int)((ticks / TicksPerMinute) % 60); }
        }


        // Returns a SchedulerTime representing the current date and time. The
        // resolution of the returned value depends on the system timer. For
        // Windows NT 3.5 and later the timer resolution is approximately 10ms,
        // for Windows NT 3.1 it is approximately 16ms, and for Windows 95 and 98
        // it is approximately 55ms.
        //
        //| <include path='docs/doc[@for="SchedulerTime.Now"]/*' />
        public static SchedulerTime Now {
            [NoHeapAllocation]
#if SINGULARITY_KERNEL
            get { return new SchedulerTime(SystemClock.KernelUpTime.Ticks); }
#else
            get { return new SchedulerTime(ProcessService.GetUpTime().Ticks); }
#endif
        }

        // Returns the second part of this SchedulerTime. The returned value is
        // an integer between 0 and 59.
        //
        //| <include path='docs/doc[@for="SchedulerTime.Second"]/*' />
        public int Second {
            [NoHeapAllocation]
            get { return (int)((ticks / TicksPerSecond) % 60); }
        }

        // Returns the tick count for this SchedulerTime. The returned value is
        // the number of 100-nanosecond intervals that have elapsed since 1/1/0001
        // 12:00am.
        //
        //| <include path='docs/doc[@for="SchedulerTime.Ticks"]/*' />
        public long Ticks {
            [NoHeapAllocation]
            get { return ticks; }
        }

        // Returns the time-of-day part of this SchedulerTime. The returned value
        // is a TimeSpan that indicates the time elapsed since midnight.
        //
        //| <include path='docs/doc[@for="SchedulerTime.TimeOfDay"]/*' />
        public TimeSpan TimeOfDay {
            get { return new TimeSpan(ticks % TicksPerDay); }
        }

        //| <include path='docs/doc[@for="SchedulerTime.Subtract"]/*' />
        public TimeSpan Subtract(SchedulerTime value) {
            return new TimeSpan(ticks - value.ticks);
        }

        //| <include path='docs/doc[@for="SchedulerTime.Subtract1"]/*' />
        public SchedulerTime Subtract(TimeSpan value) {
            return new SchedulerTime(ticks - value._ticks);
        }

        //| <include path='docs/doc[@for="SchedulerTime.ToString3"]/*' />
        public override String ToString() {
            return String.Format("{0:d} days {1:d}:{2:d}:{3:d}",
                                 TotalDays, Hour, Minute, Second);
        }


        //| <include path='docs/doc[@for="SchedulerTime.operatorADD"]/*' />
        [NoHeapAllocation]
        public static SchedulerTime operator +(SchedulerTime d, TimeSpan t) {
            if (t == TimeSpan.Infinite) {
                return MaxValue;
            }
            return new SchedulerTime(d.ticks + t._ticks);
        }

        //| <include path='docs/doc[@for="SchedulerTime.operatorSUB"]/*' />
        [NoHeapAllocation]
        public static SchedulerTime operator -(SchedulerTime d, TimeSpan t) {
            return new SchedulerTime(d.ticks - t._ticks);
        }

        //| <include path='docs/doc[@for="SchedulerTime.operatorSUB1"]/*' />
        [NoHeapAllocation]
        public static TimeSpan operator -(SchedulerTime d1, SchedulerTime d2) {
            return new TimeSpan(d1.ticks - d2.ticks);
        }

        //| <include path='docs/doc[@for="SchedulerTime.operatorEQ"]/*' />
        [NoHeapAllocation]
        public static bool operator ==(SchedulerTime d1, SchedulerTime d2) {
            return d1.ticks == d2.ticks;
        }

        //| <include path='docs/doc[@for="SchedulerTime.operatorNE"]/*' />
        [NoHeapAllocation]
        public static bool operator !=(SchedulerTime d1, SchedulerTime d2) {
            return d1.ticks != d2.ticks;
        }

        //| <include path='docs/doc[@for="SchedulerTime.operatorLT"]/*' />
        [NoHeapAllocation]
        public static bool operator <(SchedulerTime t1, SchedulerTime t2) {
            return t1.ticks < t2.ticks;
        }

        //| <include path='docs/doc[@for="SchedulerTime.operatorLE"]/*' />
        [NoHeapAllocation]
        public static bool operator <=(SchedulerTime t1, SchedulerTime t2) {
            return t1.ticks <= t2.ticks;
        }

        //| <include path='docs/doc[@for="SchedulerTime.operatorGT"]/*' />
        [NoHeapAllocation]
        public static bool operator >(SchedulerTime t1, SchedulerTime t2) {
            return t1.ticks > t2.ticks;
        }

        //| <include path='docs/doc[@for="SchedulerTime.operatorGE"]/*' />
        [NoHeapAllocation]
        public static bool operator >=(SchedulerTime t1, SchedulerTime t2) {
            return t1.ticks >= t2.ticks;
        }

    }
}
