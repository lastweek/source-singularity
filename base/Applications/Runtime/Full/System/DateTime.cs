// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{

    using System;
    using System.Threading;
    using System.Globalization;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using CultureInfo = System.Globalization.CultureInfo;
    using Microsoft.Singularity.V1.Services;

    // This value type represents a date and time.  Every DateTime
    // object has a private field (Ticks) of type Int64 that stores the
    // date and time as the number of 100 nanosecond intervals since
    // 12:00 AM January 1, year 1 A.D. in the proleptic Gregorian Calendar.
    //
    // DateTime spans from 1 A.D. to ~29247 A.D.
    //
    // For a description of various calendar issues, look at
    //
    // Calendar Studies web site, at
    // http://serendipity.nofadz.com/hermetic/cal_stud.htm.
    //
    //
    // Warning about 2 digit years
    // As a temporary hack until we get new DateTime <;->; String code,
    // some systems won't be able to round trip dates less than 1930.  This
    // is because we're using OleAut's string parsing routines, which look
    // at your computer's default short date string format, which uses 2 digit
    // years on most computers.  To fix this, go to Control Panel ->; Regional
    // Settings ->; Date and change the short date style to something like
    // "M/d/yyyy" (specifying four digits for the year).
    //
    //| <include path='docs/doc[@for="DateTime"]/*' />
    [StructLayout(LayoutKind.Auto)]
    public struct DateTime : IComparable, IFormattable
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

        // Number of days from 1/1/0001 to 12/31/1600
        private const int DaysTo1601 = DaysPer400Years * 4;
        // Number of days from 1/1/0001 to 12/30/1899
        private const int DaysTo1899 = DaysPer400Years * 4 + DaysPer100Years * 3 - 367;
        // Number of days from 1/1/0001 to 12/31/9999
        private const int DaysTo10000 = DaysPer400Years * 25 - 366;

        private const long MinTicks = 0;
        private const long MaxTicks = DaysTo10000 * TicksPerDay - 1;
        private const long MaxMillis = (long)DaysTo10000 * MillisPerDay;

        private const long FileTimeOffset = DaysTo1601 * TicksPerDay;

        private const int DatePartYear = 0;
        private const int DatePartDayOfYear = 1;
        private const int DatePartMonth = 2;
        private const int DatePartDay = 3;

        private static readonly int[] DaysToMonth365 = {
            0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334, 365};
        private static readonly int[] DaysToMonth366 = {
            0, 31, 60, 91, 121, 152, 182, 213, 244, 274, 305, 335, 366};

        //| <include path='docs/doc[@for="DateTime.MinValue"]/*' />
        public static readonly DateTime MinValue = new DateTime(MinTicks);
        //| <include path='docs/doc[@for="DateTime.MaxValue"]/*' />
        public static readonly DateTime MaxValue = new DateTime(MaxTicks);

        //
        // NOTE yslin: Before the time zone is introduced, ticks is based on 1/1/0001 local time.
        //
        private long ticks;

        // Constructs a DateTime from a tick count. The ticks
        // argument specifies the date as the number of 100-nanosecond intervals
        // that have elapsed since 1/1/0001 12:00am.
        //
        //| <include path='docs/doc[@for="DateTime.DateTime"]/*' />
        public DateTime(long ticks) {
            if (ticks < MinTicks || ticks > MaxTicks)
                throw new ArgumentOutOfRangeException("ticks", "ArgumentOutOfRange_DateTimeBadTicks");
            this.ticks = ticks;
        }

        [NoHeapAllocation]
        private DateTime(long ticksFound, int ignoreMe) {
            this.ticks = ticksFound;
            if ((ulong)ticks >(ulong)MaxTicks) {
                if (ticks > MaxTicks) {
                    ticks = MaxTicks;
                }
                else {
                    ticks = MinTicks;
                }
            }
        }

        // Constructs a DateTime from a given year, month, and day. The
        // time-of-day of the resulting DateTime is always midnight.
        //
        //| <include path='docs/doc[@for="DateTime.DateTime1"]/*' />
        public DateTime(int year, int month, int day) {
            ticks = DateToTicks(year, month, day);
        }

        // Constructs a DateTime from a given year, month, day, hour,
        // minute, and second.
        //
        //| <include path='docs/doc[@for="DateTime.DateTime3"]/*' />
        public DateTime(int year, int month, int day, int hour, int minute, int second) {
            ticks = DateToTicks(year, month, day) + TimeToTicks(hour, minute, second);
        }

        // Constructs a DateTime from a given year, month, day, hour,
        // minute, and second.
        //
        //| <include path='docs/doc[@for="DateTime.DateTime5"]/*' />
        public DateTime(int year, int month, int day, int hour, int minute, int second, int millisecond) {
            ticks = DateToTicks(year, month, day) + TimeToTicks(hour, minute, second);
            if (millisecond < 0 || millisecond >= MillisPerSecond) {
                throw new ArgumentOutOfRangeException("millisecond", String.Format("ArgumentOutOfRange_Range", 0, MillisPerSecond - 1));
            }
            ticks += millisecond * TicksPerMillisecond;
            if (ticks < MinTicks || ticks > MaxTicks)
                throw new ArgumentException("Arg_DateTimeRange");
        }

        // Returns the DateTime resulting from adding the given
        // TimeSpan to this DateTime.
        //
        //| <include path='docs/doc[@for="DateTime.Add"]/*' />
        public DateTime Add(TimeSpan value) {
            return new DateTime(ticks + value._ticks);
        }

        // Returns the DateTime resulting from adding a number of
        // time units to this DateTime.
        private DateTime Add(long value, int scale) {
            long millis = value * scale;
            if (millis <= -MaxMillis || millis >= MaxMillis) {
                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_AddValue");
            }
            return new DateTime(ticks + millis * TicksPerMillisecond);
        }

        // Returns the DateTime resulting from adding a number of
        // days to this DateTime. The result is computed by rounding the
        // fractional number of days given by value to the nearest
        // millisecond, and adding that interval to this DateTime. The
        // value argument is permitted to be negative.
        //
        //| <include path='docs/doc[@for="DateTime.AddDays"]/*' />
        public DateTime AddDays(long value) {
            return Add(value, MillisPerDay);
        }

        // Returns the DateTime resulting from adding a number of
        // hours to this DateTime. The result is computed by rounding the
        // fractional number of hours given by value to the nearest
        // millisecond, and adding that interval to this DateTime. The
        // value argument is permitted to be negative.
        //
        //| <include path='docs/doc[@for="DateTime.AddHours"]/*' />
        public DateTime AddHours(long value) {
            return Add(value, MillisPerHour);
        }

        // Returns the DateTime resulting from the given number of
        // milliseconds to this DateTime. The result is computed by rounding
        // the number of milliseconds given by value to the nearest integer,
        // and adding that interval to this DateTime. The value
        // argument is permitted to be negative.
        //
        //| <include path='docs/doc[@for="DateTime.AddMilliseconds"]/*' />
        public DateTime AddMilliseconds(long value) {
            return Add(value, 1);
        }

        // Returns the DateTime resulting from adding a number of
        // minutes to this DateTime. The result is computed by rounding the
        // fractional number of minutes given by value to the nearest
        // millisecond, and adding that interval to this DateTime. The
        // value argument is permitted to be negative.
        //
        //| <include path='docs/doc[@for="DateTime.AddMinutes"]/*' />
        public DateTime AddMinutes(long value) {
            return Add(value, MillisPerMinute);
        }

        // Returns the DateTime resulting from adding the given number of
        // months to this DateTime. The result is computed by incrementing
        // (or decrementing) the year and month parts of this DateTime by
        // months months, and, if required, adjusting the day part of the
        // resulting date downwards to the last day of the resulting month in the
        // resulting year. The time-of-day part of the result is the same as the
        // time-of-day part of this DateTime.
        //
        // In more precise terms, considering this DateTime to be of the
        // form y / m / d + t, where y is the
        // year, m is the month, d is the day, and t is the
        // time-of-day, the result is y1 / m1 / d1 + t,
        // where y1 and m1 are computed by adding months months
        // to y and m, and d1 is the largest value less than
        // or equal to d that denotes a valid day in month m1 of year
        // y1.
        //
        //| <include path='docs/doc[@for="DateTime.AddMonths"]/*' />
        public DateTime AddMonths(int months) {
            if (months < -120000 || months > 120000) throw new ArgumentOutOfRangeException("months", "ArgumentOutOfRange_DateTimeBadMonths");
            int y = GetDatePart(DatePartYear);
            int m = GetDatePart(DatePartMonth);
            int d = GetDatePart(DatePartDay);
            int i = m - 1 + months;
            if (i >= 0) {
                m = i % 12 + 1;
                y = y + i / 12;
            }
            else {
                m = 12 + (i + 1) % 12;
                y = y + (i - 11) / 12;
            }
            int days = DaysInMonth(y, m);
            if (d > days) d = days;
            return new DateTime(DateToTicks(y, m, d) + ticks % TicksPerDay);
        }

        // Returns the DateTime resulting from adding a number of
        // seconds to this DateTime. The result is computed by rounding the
        // fractional number of seconds given by value to the nearest
        // millisecond, and adding that interval to this DateTime. The
        // value argument is permitted to be negative.
        //
        //| <include path='docs/doc[@for="DateTime.AddSeconds"]/*' />
        public DateTime AddSeconds(long value) {
            return Add(value, MillisPerSecond);
        }

        // Returns the DateTime resulting from adding the given number of
        // 100-nanosecond ticks to this DateTime. The value argument
        // is permitted to be negative.
        //
        //| <include path='docs/doc[@for="DateTime.AddTicks"]/*' />
        public DateTime AddTicks(long value) {
            return new DateTime(ticks + value);
        }

        // Returns the DateTime resulting from adding the given number of
        // years to this DateTime. The result is computed by incrementing
        // (or decrementing) the year part of this DateTime by value
        // years. If the month and day of this DateTime is 2/29, and if the
        // resulting year is not a leap year, the month and day of the resulting
        // DateTime becomes 2/28. Otherwise, the month, day, and time-of-day
        // parts of the result are the same as those of this DateTime.
        //
        //| <include path='docs/doc[@for="DateTime.AddYears"]/*' />
        public DateTime AddYears(int value) {
            return AddMonths(value * 12);
        }



        // Compares two DateTime values, returning an integer that indicates
        // their relationship.
        //
        //| <include path='docs/doc[@for="DateTime.Compare"]/*' />
        [NoHeapAllocation]
        public static int Compare(DateTime t1, DateTime t2) {
            if (t1.ticks > t2.ticks) return 1;
            if (t1.ticks < t2.ticks) return -1;
            return 0;
        }

        // Compares this DateTime to a given object. This method provides an
        // implementation of the IComparable interface. The object
        // argument must be another DateTime, or otherwise an exception
        // occurs.  Null is considered less than any instance.
        //
        // Returns a value less than zero if this  object
        //| <include path='docs/doc[@for="DateTime.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) return 1;
            if (!(value is DateTime)) {
                throw new ArgumentException("Arg_MustBeDateTime");
            }

            long t = ((DateTime)value).ticks;
            if (ticks > t) return 1;
            if (ticks < t) return -1;
            return 0;
        }

        // Returns the tick count corresponding to the given year, month, and day.
        // Will check the if the parameters are valid.
        private static long DateToTicks(int year, int month, int day) {
            if (year >= 1 && year <= 9999 && month >= 1 && month <= 12) {
                int[] days = IsLeapYear(year)? DaysToMonth366: DaysToMonth365;
                if (day >= 1 && day <= days[month] - days[month - 1]) {
                    int y = year - 1;
                    int n = y * 365 + y / 4 - y / 100 + y / 400 + days[month - 1] + day - 1;
                    return n * TicksPerDay;
                }
            }
            throw new ArgumentOutOfRangeException("ArgumentOutOfRange_BadYearMonthDay");
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

        // Returns the number of days in the month given by the year and
        // month arguments.
        //
        //| <include path='docs/doc[@for="DateTime.DaysInMonth"]/*' />
        public static int DaysInMonth(int year, int month) {
            if (month < 1 || month > 12) throw new ArgumentOutOfRangeException("ArgumentOutOfRange_Month");
            int[] days = IsLeapYear(year)? DaysToMonth366: DaysToMonth365;
            return days[month] - days[month - 1];
        }

        // Checks if this DateTime is equal to a given object. Returns
        // true if the given object is a boxed DateTime and its value
        // is equal to the value of this DateTime. Returns false
        // otherwise.
        //
        //| <include path='docs/doc[@for="DateTime.Equals"]/*' />
        public override bool Equals(Object value) {
            if (value is DateTime) {
                return ticks == ((DateTime)value).ticks;
            }
            return false;
        }

        // Compares two DateTime values for equality. Returns true if
        // the two DateTime values are equal, or false if they are
        // not equal.
        //
        //| <include path='docs/doc[@for="DateTime.Equals1"]/*' />
        [NoHeapAllocation]
        public static bool Equals(DateTime t1, DateTime t2) {
            return t1.ticks == t2.ticks;
        }

        //| <include path='docs/doc[@for="DateTime.FromFileTimeUtc"]/*' />
        public static DateTime FromFileTimeUtc(long fileTime) {
            if (fileTime < 0)
                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_FileTimeInvalid");

            // This is the ticks in Universal time for this fileTime.
            long universalTicks = fileTime + FileTimeOffset;
            return new DateTime(universalTicks);
        }

        // Returns the date part of this DateTime. The resulting value
        // corresponds to this DateTime with the time-of-day part set to
        // zero (midnight).
        //
        //| <include path='docs/doc[@for="DateTime.Date"]/*' />
        public DateTime Date {
            get { return new DateTime(ticks - ticks % TicksPerDay); }
        }

        // Returns a given date part of this DateTime. This method is used
        // to compute the year, day-of-year, month, or day part.
        [NoHeapAllocation]
        private int GetDatePart(int part) {
            // n = number of days since 1/1/0001
            int n = (int)(ticks / TicksPerDay);
            // y400 = number of whole 400-year periods since 1/1/0001
            int y400 = n / DaysPer400Years;
            // n = day number within 400-year period
            n -= y400 * DaysPer400Years;
            // y100 = number of whole 100-year periods within 400-year period
            int y100 = n / DaysPer100Years;
            // Last 100-year period has an extra day, so decrement result if 4
            if (y100 == 4) y100 = 3;
            // n = day number within 100-year period
            n -= y100 * DaysPer100Years;
            // y4 = number of whole 4-year periods within 100-year period
            int y4 = n / DaysPer4Years;
            // n = day number within 4-year period
            n -= y4 * DaysPer4Years;
            // y1 = number of whole years within 4-year period
            int y1 = n / DaysPerYear;
            // Last year has an extra day, so decrement result if 4
            if (y1 == 4) y1 = 3;
            // If year was requested, compute and return it
            if (part == DatePartYear) {
                return y400 * 400 + y100 * 100 + y4 * 4 + y1 + 1;
            }
            // n = day number within year
            n -= y1 * DaysPerYear;
            // If day-of-year was requested, return it
            if (part == DatePartDayOfYear) return n + 1;
            // Leap year calculation looks different from IsLeapYear since y1, y4,
            // and y100 are relative to year 1, not year 0
            bool leapYear = y1 == 3 && (y4 != 24 || y100 == 3);
            int[] days = leapYear? DaysToMonth366: DaysToMonth365;
            // All months have less than 32 days, so n >> 5 is a good conservative
            // estimate for the month
            int m = n >> 5 + 1;
            // m = 1-based month number
            while (n >= days[m]) m++;
            // If month was requested, return it
            if (part == DatePartMonth) return m;
            // Return 1-based day-of-month
            return n - days[m - 1] + 1;
        }

        // Returns the day-of-month part of this DateTime. The returned
        // value is an integer between 1 and 31.
        //
        //| <include path='docs/doc[@for="DateTime.Day"]/*' />
        public int Day {
            [NoHeapAllocation]
            get { return GetDatePart(DatePartDay); }
        }

        // Returns the day-of-week part of this DateTime. The returned value
        // is an integer between 0 and 6, where 0 indicates Sunday, 1 indicates
        // Monday, 2 indicates Tuesday, 3 indicates Wednesday, 4 indicates
        // Thursday, 5 indicates Friday, and 6 indicates Saturday.
        //
        //| <include path='docs/doc[@for="DateTime.DayOfWeek"]/*' />
        public DayOfWeek DayOfWeek {
            [NoHeapAllocation]
            get { return (DayOfWeek)((ticks / TicksPerDay + 1) % 7); }
        }

        // Returns the day-of-year part of this DateTime. The returned value
        // is an integer between 1 and 366.
        //
        //| <include path='docs/doc[@for="DateTime.DayOfYear"]/*' />
        public int DayOfYear {
            [NoHeapAllocation]
            get { return GetDatePart(DatePartDayOfYear); }
        }

        // Returns the hash code for this DateTime.
        //
        //| <include path='docs/doc[@for="DateTime.GetHashCode"]/*' />
        public override int GetHashCode() {
            return (int)ticks ^ (int)(ticks >> 32);
        }

        // Returns the hour part of this DateTime. The returned value is an
        // integer between 0 and 23.
        //
        //| <include path='docs/doc[@for="DateTime.Hour"]/*' />
        public int Hour {
            [NoHeapAllocation]
            get { return (int)((ticks / TicksPerHour) % 24); }
        }

        // Returns the millisecond part of this DateTime. The returned value
        // is an integer between 0 and 999.
        //
        //| <include path='docs/doc[@for="DateTime.Millisecond"]/*' />
        public int Millisecond {
            [NoHeapAllocation]
            get { return (int)((ticks / TicksPerMillisecond) % 1000); }
        }

        // Returns the minute part of this DateTime. The returned value is
        // an integer between 0 and 59.
        //
        //| <include path='docs/doc[@for="DateTime.Minute"]/*' />
        public int Minute {
            [NoHeapAllocation]
            get { return (int)((ticks / TicksPerMinute) % 60); }
        }

        // Returns the month part of this DateTime. The returned value is an
        // integer between 1 and 12.
        //
        //| <include path='docs/doc[@for="DateTime.Month"]/*' />
        public int Month {
            [NoHeapAllocation]
            get { return GetDatePart(DatePartMonth); }
        }

        [NoHeapAllocation]
        private static DateTime GetUtcTime()
        {
            return ProcessService.GetUtcTime();
        }

        // Returns a DateTime representing the current date and time. The
        // resolution of the returned value depends on the system timer. For
        // Windows NT 3.5 and later the timer resolution is approximately 10ms,
        // for Windows NT 3.1 it is approximately 16ms, and for Windows 95 and 98
        // it is approximately 55ms.
        //
        //| <include path='docs/doc[@for="DateTime.Now"]/*' />
        public static DateTime Now {
            [NoHeapAllocation]
            get { return GetUtcTime(); }
        }

        //| <include path='docs/doc[@for="DateTime.UtcNow"]/*' />
        public static DateTime UtcNow {
            [NoHeapAllocation]
            get { return GetUtcTime(); }
        }

        public static DateTime BootTime {
            get { return Now - ProcessService.GetUpTime(); }
        }

        // Returns the second part of this DateTime. The returned value is
        // an integer between 0 and 59.
        //
        //| <include path='docs/doc[@for="DateTime.Second"]/*' />
        public int Second {
            [NoHeapAllocation]
            get { return (int)((ticks / TicksPerSecond) % 60); }
        }

        // Returns the tick count for this DateTime. The returned value is
        // the number of 100-nanosecond intervals that have elapsed since 1/1/0001
        // 12:00am.
        //
        //| <include path='docs/doc[@for="DateTime.Ticks"]/*' />
        public long Ticks {
            [NoHeapAllocation]
            get { return ticks; }
        }

        // Returns the time-of-day part of this DateTime. The returned value
        // is a TimeSpan that indicates the time elapsed since midnight.
        //
        //| <include path='docs/doc[@for="DateTime.TimeOfDay"]/*' />
        public TimeSpan TimeOfDay {
            get { return new TimeSpan(ticks % TicksPerDay); }
        }

        // Returns a DateTime representing the current date. The date part
        // of the returned value is the current date, and the time-of-day part of
        // the returned value is zero (midnight).
        //
        //| <include path='docs/doc[@for="DateTime.Today"]/*' />
        public static DateTime Today {
            get {
                long ticks = Now.Ticks;
                return new DateTime(ticks - ticks % TicksPerDay);
            }
        }

        // Returns the year part of this DateTime. The returned value is an
        // integer between 1 and 9999.
        //
        //| <include path='docs/doc[@for="DateTime.Year"]/*' />
        public int Year {
            [NoHeapAllocation]
            get { return GetDatePart(DatePartYear); }
        }

        // Checks whether a given year is a leap year. This method returns true if
        // year is a leap year, or false if not.
        //
        //| <include path='docs/doc[@for="DateTime.IsLeapYear"]/*' />
        [NoHeapAllocation]
        public static bool IsLeapYear(int year) {
            return year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
        }

        // Constructs a DateTime from a string. The string must specify a
        // date and optionally a time in a culture-specific or universal format.
        // Leading and trailing whitespace characters are allowed.
        //
        //| <include path='docs/doc[@for="DateTime.Parse"]/*' />
        public static DateTime Parse(String s) {
            throw new Exception("Parse not supported in Bartok");
        }

        // Constructs a DateTime from a string. The string must specify a
        // date and optionally a time in a culture-specific or universal format.
        // Leading and trailing whitespace characters are allowed.
        //
        //| <include path='docs/doc[@for="DateTime.ParseExact"]/*' />
        public static DateTime ParseExact(String s, String format) {
            throw new Exception("Parse not supported in Bartok");
        }

        //| <include path='docs/doc[@for="DateTime.Subtract"]/*' />
        public TimeSpan Subtract(DateTime value) {
            return new TimeSpan(ticks - value.ticks);
        }

        //| <include path='docs/doc[@for="DateTime.Subtract1"]/*' />
        public DateTime Subtract(TimeSpan value) {
            return new DateTime(ticks - value._ticks);
        }

        //| <include path='docs/doc[@for="DateTime.ToFileTimeUtc"]/*' />
        public long ToFileTimeUtc() {
            long t = this.ticks - FileTimeOffset;
            if (t < 0) throw new ArgumentOutOfRangeException("ArgumentOutOfRange_FileTimeInvalid");
            return t;
        }

        //| <include path='docs/doc[@for="DateTime.ToLongDateString"]/*' />
        public String ToLongDateString() {
            return (ToString("D"));
        }

        //| <include path='docs/doc[@for="DateTime.ToLongTimeString"]/*' />
        public String ToLongTimeString() {
            return (ToString("T"));
        }

        //| <include path='docs/doc[@for="DateTime.ToShortDateString"]/*' />
        public String ToShortDateString() {
            return (ToString("d"));
        }

        //| <include path='docs/doc[@for="DateTime.ToShortTimeString"]/*' />
        public String ToShortTimeString() {
            return (ToString("t"));
        }

        //| <include path='docs/doc[@for="DateTime.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }

        //| <include path='docs/doc[@for="DateTime.ToString3"]/*' />
        public String ToString(String format) {
            // US-centric representation for now, until we have proper
            // globalization in Singularity.
            //
            // The only special support here is for RFC1123 ("R" / "r")
            if (format != null && (format.Equals("R") || format.Equals("r"))) {
                return String.Format("{0:s}, {1:d02} {2:s} {3:d} {4:d02}:{5:d02}:{6:d02} GMT",
                                     GetShortWeekday(), Day, GetShortMonth(), Year,
                                     Hour, Minute, Second);
            }
            else {
                return String.Format("{0:d}/{1:d}/{2:d} {3:d}:{4:d}:{5:d}",
                                     Month, Day, Year, Hour, Minute, Second);
            }
        }

        public DateTime ToLocalTime() {
            long tickCount = this.ticks;
            return new DateTime(tickCount);
        }

        //| <include path='docs/doc[@for="DateTime.ToUniversalTime"]/*' />
        public DateTime ToUniversalTime() {
            long tickCount = this.ticks;
            return new DateTime(tickCount);
        }


        //| <include path='docs/doc[@for="DateTime.operatorADD"]/*' />
        public static DateTime operator +(DateTime d, TimeSpan t) {
            return new DateTime(d.ticks + t._ticks);
        }

        //| <include path='docs/doc[@for="DateTime.operatorSUB"]/*' />
        public static DateTime operator -(DateTime d, TimeSpan t) {
            return new DateTime(d.ticks - t._ticks);
        }

        //| <include path='docs/doc[@for="DateTime.operatorSUB1"]/*' />
        public static TimeSpan operator -(DateTime d1, DateTime d2) {
            return new TimeSpan(d1.ticks - d2.ticks);
        }

        //| <include path='docs/doc[@for="DateTime.operatorEQ"]/*' />
        [NoHeapAllocation]
        public static bool operator ==(DateTime d1, DateTime d2) {
            return d1.ticks == d2.ticks;
        }

        //| <include path='docs/doc[@for="DateTime.operatorNE"]/*' />
        [NoHeapAllocation]
        public static bool operator !=(DateTime d1, DateTime d2) {
            return d1.ticks != d2.ticks;
        }

        //| <include path='docs/doc[@for="DateTime.operatorLT"]/*' />
        [NoHeapAllocation]
        public static bool operator <(DateTime t1, DateTime t2) {
            return t1.ticks < t2.ticks;
        }

        //| <include path='docs/doc[@for="DateTime.operatorLE"]/*' />
        [NoHeapAllocation]
        public static bool operator <=(DateTime t1, DateTime t2) {
            return t1.ticks <= t2.ticks;
        }

        //| <include path='docs/doc[@for="DateTime.operatorGT"]/*' />
        [NoHeapAllocation]
        public static bool operator >(DateTime t1, DateTime t2) {
            return t1.ticks > t2.ticks;
        }

        //| <include path='docs/doc[@for="DateTime.operatorGE"]/*' />
        [NoHeapAllocation]
        public static bool operator >=(DateTime t1, DateTime t2) {
            return t1.ticks >= t2.ticks;
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="DateTime.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode() {
            return TypeCode.DateTime;
        }

        private string GetShortWeekday()
        {
            // Hardcoded USA-English until we support globalization
            switch (DayOfWeek) {
                case DayOfWeek.Monday : return "Mon";
                case DayOfWeek.Tuesday : return "Tue";
                case DayOfWeek.Wednesday : return "Wed";
                case DayOfWeek.Thursday : return "Thu";
                case DayOfWeek.Friday : return "Fri";
                case DayOfWeek.Saturday : return "Sat";
                case DayOfWeek.Sunday : return "Sun";
            }

            return null;
        }

        private string GetShortMonth()
        {
            // Hardcoded USA-English until we support globalization
            switch (Month) {
                case 1 : return "Jan";
                case 2 : return "Feb";
                case 3 : return "Mar";
                case 4 : return "Apr";
                case 5 : return "May";
                case 6 : return "Jun";
                case 7 : return "Jul";
                case 8 : return "Aug";
                case 9 : return "Sep";
                case 10 : return "Oct";
                case 11 : return "Nov";
                case 12 : return "Dec";
            }

            return null;
        }
    }
}
