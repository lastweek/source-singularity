// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{
    using System.Text;
    using System.Runtime.CompilerServices;
    using System;

    // TimeSpan represents a duration of time.  A TimeSpan can be negative
    // or positive.
    //
    // TimeSpan is internally represented as a number of ticks (100ns).  While
    // this maps well into units of time such as hours and days, any
    // periods longer than that aren't representable in a nice fashion.
    // For instance, a month can be between 28 and 31 days, while a year
    // can contain 365 or 364 days.  A decade can have between 1 and 3 leap years,
    // depending on when you map the TimeSpan into the calendar.  This is why
    // we do not provide Years() or Months().
    //
    // TimeSpans are limited to approximately 14623 years.
    //
    //| <include path='docs/doc[@for="TimeSpan"]/*' />
    public struct TimeSpan : IComparable
    {
        //| <include path='docs/doc[@for="TimeSpan.TicksPerMillisecond"]/*' />
        public const long TicksPerMillisecond = 10000;
        //| <include path='docs/doc[@for="TimeSpan.TicksPerSecond"]/*' />
        public const long TicksPerSecond = TicksPerMillisecond * 1000;
        //| <include path='docs/doc[@for="TimeSpan.TicksPerMinute"]/*' />
        public const long TicksPerMinute = TicksPerSecond * 60;
        //| <include path='docs/doc[@for="TimeSpan.TicksPerHour"]/*' />
        public const long TicksPerHour = TicksPerMinute * 60;
        //| <include path='docs/doc[@for="TimeSpan.TicksPerDay"]/*' />
        public const long TicksPerDay = TicksPerHour * 24;

        private const int MillisPerSecond = 1000;
        private const int MillisPerMinute = MillisPerSecond * 60;
        private const int MillisPerHour = MillisPerMinute * 60;
        private const int MillisPerDay = MillisPerHour * 24;

        private const long MaxSeconds = Int64.MaxValue / TicksPerSecond;
        private const long MinSeconds = Int64.MinValue / TicksPerSecond;

        private const long MaxMilliSeconds = Int64.MaxValue / TicksPerMillisecond;
        private const long MinMilliSeconds = Int64.MinValue / TicksPerMillisecond;


        //| <include path='docs/doc[@for="TimeSpan.Zero"]/*' />
        public static readonly TimeSpan Zero = new TimeSpan(0);

        //| <include path='docs/doc[@for="TimeSpan.MaxValue"]/*' />
        public static readonly TimeSpan MaxValue = new TimeSpan(Int64.MaxValue);
        //| <include path='docs/doc[@for="TimeSpan.MinValue"]/*' />
        public static readonly TimeSpan MinValue = new TimeSpan(Int64.MinValue);

        public static readonly TimeSpan Infinite = new TimeSpan(Int64.MaxValue);

        // internal so that DateTime doesn't have to call an extra get
        // method for some arithmetic operations.
        internal long _ticks;

        //public TimeSpan() {
        //    _ticks = 0;
        //}

        //| <include path='docs/doc[@for="TimeSpan.TimeSpan"]/*' />
        [NoHeapAllocation]
        public TimeSpan(long ticks) {
            this._ticks = ticks;
        }

        //| <include path='docs/doc[@for="TimeSpan.TimeSpan1"]/*' />
        public TimeSpan(int hours, int minutes, int seconds) {
            _ticks = TimeToTicks(hours, minutes, seconds);
        }

        //| <include path='docs/doc[@for="TimeSpan.TimeSpan2"]/*' />
        public TimeSpan(int days, int hours, int minutes, int seconds)
            : this(days,hours,minutes,seconds,0)
        {
        }

        //| <include path='docs/doc[@for="TimeSpan.TimeSpan3"]/*' />
        public TimeSpan(int days, int hours, int minutes, int seconds, int milliseconds)
        {
            long totalMilliSeconds = ((long)days * 3600 * 24 + hours * 3600 + minutes * 60 + seconds) * 1000 + milliseconds;
            if (totalMilliSeconds > MaxMilliSeconds || totalMilliSeconds < MinMilliSeconds)
                throw new ArgumentOutOfRangeException("Overflow_TimeSpanTooLong");
            _ticks =  (long)totalMilliSeconds * TicksPerMillisecond;
        }

        //| <include path='docs/doc[@for="TimeSpan.Ticks"]/*' />
        public long Ticks {
            [NoHeapAllocation]
            get { return _ticks; }
        }

/*TODO
        //| <include path='docs/doc[@for="TimeSpan.Days"]/*' />
        public int Days {
            [NoHeapAllocation]
            get { return (int)(_ticks / TicksPerDay); }
        }

        //| <include path='docs/doc[@for="TimeSpan.Hours"]/*' />
        public int Hours
        {
            [NoHeapAllocation]
            get { return (int)((_ticks / TicksPerHour) % 24); }
        }

        //| <include path='docs/doc[@for="TimeSpan.Milliseconds"]/*' />
        public int Milliseconds
        {
            [NoHeapAllocation]
            get { return (int)((_ticks / TicksPerMillisecond) % 1000); }
        }

        //| <include path='docs/doc[@for="TimeSpan.Minutes"]/*' />
        public int Minutes
        {
            [NoHeapAllocation]
            get { return (int)((_ticks / TicksPerMinute) % 60); }
        }

        //| <include path='docs/doc[@for="TimeSpan.Seconds"]/*' />
        public int Seconds
        {
            [NoHeapAllocation]
            get { return (int)((_ticks / TicksPerSecond) % 60); }
        }

        //| <include path='docs/doc[@for="TimeSpan.TotalDays"]/*' />
        public long TotalDays
        {
            [NoHeapAllocation]
            get { return _ticks / TicksPerDay; }
        }

        //| <include path='docs/doc[@for="TimeSpan.TotalHours"]/*' />
        public long TotalHours
        {
            [NoHeapAllocation]
            get { return _ticks / TicksPerHour; }
        }

        //| <include path='docs/doc[@for="TimeSpan.TotalMilliseconds"]/*' />
        public long TotalMilliseconds
        {
            [NoHeapAllocation]
            get { return _ticks / TicksPerMillisecond; }
        }

        //| <include path='docs/doc[@for="TimeSpan.TotalMinutes"]/*' />
        public long TotalMinutes
        {
            [NoHeapAllocation]
            get { return _ticks / TicksPerMinute; }
        }

        //| <include path='docs/doc[@for="TimeSpan.TotalSeconds"]/*' />
        public long TotalSeconds
        {
            [NoHeapAllocation]
            get { return _ticks / TicksPerSecond; }
        }
*/

        //| <include path='docs/doc[@for="TimeSpan.Add"]/*' />
        public TimeSpan Add(TimeSpan ts) {
            long result = _ticks + ts._ticks;
            // Overflow if signs of operands was identical and result's
            // sign was opposite.
            // >> 63 gives the sign bit (either 64 1's or 64 0's).
            if ((_ticks >> 63 == ts._ticks >> 63) && (_ticks >> 63 != result >> 63))
                throw new OverflowException("Overflow_TimeSpanTooLong");
            return new TimeSpan(result);
        }

        [NoHeapAllocation]
        public TimeSpan AddNoAlloc(TimeSpan ts) {
            long result = _ticks + ts._ticks;
            // Overflow if signs of operands was identical and result's
            // sign was opposite.
            // >> 63 gives the sign bit (either 64 1's or 64 0's).
            if ((_ticks >> 63 == ts._ticks >> 63) && (_ticks >> 63 != result >> 63))
                return TimeSpan.Infinite;
            return new TimeSpan(result);
        }


        // Compares two TimeSpan values, returning an integer that indicates their
        // relationship.
        //
        //| <include path='docs/doc[@for="TimeSpan.Compare"]/*' />
        [NoHeapAllocation]
        public static int Compare(TimeSpan t1, TimeSpan t2)
        {
            if (t1._ticks > t2._ticks) return 1;
            if (t1._ticks < t2._ticks) return -1;
            return 0;
        }

        // Returns a value less than zero if this object
        //| <include path='docs/doc[@for="TimeSpan.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) return 1;
            if (!(value is TimeSpan))
                throw new ArgumentException("Arg_MustBeTimeSpan");
            long t = ((TimeSpan)value)._ticks;
            if (_ticks > t) return 1;
            if (_ticks < t) return -1;
            return 0;
        }

        //| <include path='docs/doc[@for="TimeSpan.FromDays"]/*' />
        public static TimeSpan FromDays(long value) {
            return Interval(value, MillisPerDay);
        }

        //| <include path='docs/doc[@for="TimeSpan.Duration"]/*' />
        public TimeSpan Duration() {
            if (_ticks == TimeSpan.MinValue._ticks)
                throw new OverflowException("Overflow_NegateTwosCompNum");
            return new TimeSpan(_ticks >= 0? _ticks: -_ticks);
        }

        //| <include path='docs/doc[@for="TimeSpan.Equals"]/*' />
        public override bool Equals(Object value) {
            if (value is TimeSpan) {
                return _ticks == ((TimeSpan)value)._ticks;
            }
            return false;
        }

        //| <include path='docs/doc[@for="TimeSpan.Equals1"]/*' />
        [NoHeapAllocation]
        public static bool Equals(TimeSpan t1, TimeSpan t2)
        {
            return t1._ticks == t2._ticks;
        }

        //| <include path='docs/doc[@for="TimeSpan.GetHashCode"]/*' />
        public override int GetHashCode()
        {
            return (int)_ticks ^ (int)(_ticks >> 32);
        }

        //| <include path='docs/doc[@for="TimeSpan.FromHours"]/*' />
        public static TimeSpan FromHours(long value) {
            return Interval(value, MillisPerHour);
        }

        private static TimeSpan Interval(long value, int scale) {
            long millis = value * scale;
            if ((millis > MaxMilliSeconds) || (millis < MinMilliSeconds)) {
                throw new OverflowException("Overflow_TimeSpanTooLong");
            }
            return new TimeSpan(millis * TicksPerMillisecond);
        }

        //| <include path='docs/doc[@for="TimeSpan.FromMilliseconds"]/*' />
        public static TimeSpan FromMilliseconds(long value) {
            return Interval(value, 1);
        }

        //| <include path='docs/doc[@for="TimeSpan.FromMinutes"]/*' />
        public static TimeSpan FromMinutes(long value) {
            return Interval(value, MillisPerMinute);
        }

        //| <include path='docs/doc[@for="TimeSpan.Negate"]/*' />
        public TimeSpan Negate() {
            if (_ticks == TimeSpan.MinValue._ticks)
                throw new OverflowException("Overflow_NegateTwosCompNum");
            return new TimeSpan(-_ticks);
        }

        // Constructs a TimeSpan from a string.  Leading and trailing white
        // space characters are allowed.
        //
        //| <include path='docs/doc[@for="TimeSpan.Parse"]/*' />
        public static TimeSpan Parse(String s) {
            return new TimeSpan(new StringParser().Parse(s, true));
        }

        //| <include path='docs/doc[@for="TimeSpan.FromSeconds"]/*' />
        public static TimeSpan FromSeconds(long value) {
            return Interval(value, MillisPerSecond);
        }

        //| <include path='docs/doc[@for="TimeSpan.Subtract"]/*' />
        public TimeSpan Subtract(TimeSpan ts) {
            long result = _ticks - ts._ticks;
            // Overflow if signs of operands was different and result's
            // sign was opposite from the first argument's sign.
            // >> 63 gives the sign bit (either 64 1's or 64 0's).
            if ((_ticks >> 63 != ts._ticks >> 63) && (_ticks >> 63 != result >> 63))
                throw new OverflowException("Overflow_TimeSpanTooLong");
            return new TimeSpan(result);
        }

        //| <include path='docs/doc[@for="TimeSpan.FromTicks"]/*' />
        [NoHeapAllocation]
        public static TimeSpan FromTicks(long value)
        {
            return new TimeSpan(value);
        }

        internal static long TimeToTicks(int hour, int minute, int second) {
            // totalSeconds is bounded by 2^31 * 2^12 + 2^31 * 2^8 + 2^31,
            // which is less than 2^44, meaning we won't overflow totalSeconds.
            long totalSeconds = (long)hour * 3600 + (long)minute * 60 + (long)second;
            if (totalSeconds > MaxSeconds || totalSeconds < MinSeconds)
                throw new ArgumentOutOfRangeException("Overflow_TimeSpanTooLong");
            return totalSeconds * TicksPerSecond;
        }

        private String IntToString(int n, int digits) {
            return ParseNumbers.IntToString(n, 10, digits, '0', 0);
        }

        //| <include path='docs/doc[@for="TimeSpan.ToString"]/*' />
        public override String ToString() {
            return Ticks.ToString();
/*TODO
            StringBuilder sb = new StringBuilder();
            int day = (int)(_ticks / TicksPerDay);
            long time = _ticks % TicksPerDay;
            if (_ticks < 0) {
                sb.Append("-");
                day = -day;
                time = -time;
            }
            if (day != 0) {
                sb.Append(day);
                sb.Append(".");
            }
            sb.Append(IntToString((int)(time / TicksPerHour % 24), 2));
            sb.Append(":");
            sb.Append(IntToString((int)(time / TicksPerMinute % 60), 2));
            sb.Append(":");
            sb.Append(IntToString((int)(time / TicksPerSecond % 60), 2));
            int t = (int)(time % TicksPerSecond);
            if (t != 0) {
                sb.Append(".");
                sb.Append(IntToString(t, 7));
            }
            return sb.ToString();
*/
        }

        //| <include path='docs/doc[@for="TimeSpan.operatorSUB1"]/*' />
        public static TimeSpan operator -(TimeSpan t) {
            if (t._ticks == TimeSpan.MinValue._ticks)
                throw new OverflowException("Overflow_NegateTwosCompNum");
            return new TimeSpan(-t._ticks);
        }

        //| <include path='docs/doc[@for="TimeSpan.operatorSUB2"]/*' />
        public static TimeSpan operator -(TimeSpan t1, TimeSpan t2) {
            return t1.Subtract(t2);
        }

        //| <include path='docs/doc[@for="TimeSpan.operatorADD1"]/*' />
        [NoHeapAllocation]
        public static TimeSpan operator +(TimeSpan t)
        {
            return t;
        }

        //| <include path='docs/doc[@for="TimeSpan.operatorADD2"]/*' />
        public static TimeSpan operator +(TimeSpan t1, TimeSpan t2) {
            return t1.Add(t2);
        }

        //| <include path='docs/doc[@for="TimeSpan.operatorEQ"]/*' />
        [NoHeapAllocation]
        public static bool operator ==(TimeSpan t1, TimeSpan t2) {
            return t1._ticks == t2._ticks;
        }

        //| <include path='docs/doc[@for="TimeSpan.operatorNE"]/*' />
        [NoHeapAllocation]
        public static bool operator !=(TimeSpan t1, TimeSpan t2)
        {
            return t1._ticks != t2._ticks;
        }

        //| <include path='docs/doc[@for="TimeSpan.operatorLT"]/*' />
        [NoHeapAllocation]
        public static bool operator <(TimeSpan t1, TimeSpan t2)
        {
            return t1._ticks < t2._ticks;
        }

        //| <include path='docs/doc[@for="TimeSpan.operatorLE"]/*' />
        [NoHeapAllocation]
        public static bool operator <=(TimeSpan t1, TimeSpan t2)
        {
            return t1._ticks <= t2._ticks;
        }

        //| <include path='docs/doc[@for="TimeSpan.operatorGT"]/*' />
        [NoHeapAllocation]
        public static bool operator >(TimeSpan t1, TimeSpan t2)
        {
            return t1._ticks > t2._ticks;
        }

        //| <include path='docs/doc[@for="TimeSpan.operatorGE"]/*' />
        [NoHeapAllocation]
        public static bool operator >=(TimeSpan t1, TimeSpan t2) {
            return t1._ticks >= t2._ticks;
        }

        private class StringParser
        {
            private String str;
            private char ch;
            private int pos;
            private int len;

            internal static void Error() {
                throw new FormatException("Format_InvalidString");
            }

            internal static void OverflowError() {
                throw new OverflowException("Overflow_TimeSpanTooLong");
            }

            internal void NextChar() {
                if (pos < len) pos++;
                ch = pos < len? str[pos]: (char) 0;
            }

            internal char NextNonDigit() {
                int i = pos;
                while (i < len) {
                    char ch = str[i];
                    if (ch < '0' || ch > '9') return ch;
                    i++;
                }
                return (char) 0;
            }

            internal long Parse(String s, bool allowWhiteSpace) {
                if (s == null) throw new ArgumentNullException("s");
                str = s;
                len = s.Length;
                pos = -1;
                NextChar();
                if (allowWhiteSpace)
                    SkipBlanks();
                bool negative = false;
                if (ch == '-') {
                    negative = true;
                    NextChar();
                }
                long time;
                if (NextNonDigit() == ':') {
                    time = ParseTime();
                }
                else {
                    time = ParseInt((int)(0x7FFFFFFFFFFFFFFFL / TicksPerDay)) * TicksPerDay;
                    if (ch == '.') {
                        NextChar();
                        time += ParseTime();
                    }
                }
                if (negative) {
                    time = -time;
                    // Allow -0 as well
                    if (time > 0) OverflowError();
                }
                else {
                    if (time < 0) OverflowError();
                }
                if (allowWhiteSpace)
                    SkipBlanks();
                if (pos < len) Error();
                return time;
            }

            internal int ParseInt(int max) {
                int i = 0;
                int p = pos;
                while (ch >= '0' && ch <= '9') {
                    if ((i & 0xF0000000) != 0) OverflowError();
                    i = i * 10 + ch - '0';
                    if (i < 0) OverflowError();
                    NextChar();
                }
                if (p == pos) Error();
                if (i > max) OverflowError();
                return i;
            }

            internal long ParseTime() {
                long time = ParseInt(23) * TicksPerHour;
                if (ch != ':') Error();
                NextChar();
                time += ParseInt(59) * TicksPerMinute;
                if (ch == ':') {
                    NextChar();
                    time += ParseInt(59) * TicksPerSecond;
                    if (ch == '.') {
                        NextChar();
                        int f = (int)TicksPerSecond;
                        while (f > 1 && ch >= '0' && ch <= '9') {
                            f /= 10;
                            time += (ch - '0') * f;
                            NextChar();
                        }
                    }
                }
                return time;
            }

            internal void SkipBlanks() {
                while (ch == ' ' || ch == '\t') NextChar();
            }
        }
    }
}
