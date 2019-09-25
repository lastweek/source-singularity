// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

using System;

namespace RJBlack
{
    public class Timer : IComparable
    {
        // Fundamental field is the time
        private ulong _time;
        public ulong time
        {
            get { return _time; }
            set // Only if not in a wheel
            {
#if SINGULARITY
                if (this.wheel != null)
                    throw new System.Exception("Field Access");
#else
                if (this.wheel != null)
                    throw new FieldAccessException();
#endif // SINGULARITY
                _time = value;
            }
        }
        // Methods
        public Timer(ulong time)
        {
            this._time = time;
        }
        public int CompareTo(object obj)
        {
            Timer a = this;
            Timer b = obj as Timer;
            if (b == null) return 1;
            return a.time.CompareTo(b.time);
        }

        // Stuff for usage of a TimerWheel
        // followed by the TimerWheel itself
        private TimerWheel wheel;
        private Timer next;
        private Timer prev;

        public class TimerWheel
        {
            // The state we need to implement the wheel
            private readonly ulong resolution;
            private readonly uint clicks;
            private readonly Timer[] wheel;
            private uint numtimers = 0;
            private ulong now;

            public int Count
            {
                get { return (int)numtimers; }
            }

            public ulong Now
            {
                get { return now; }
            }

            public void Add(Timer! t)
            {
                if ((t.time < this.now) || (t.wheel != null))
                    throw new ArgumentException();

                uint click = (uint)((t.time / resolution) % clicks);

                Timer prev = null;
                Timer here = wheel[click];
                while (here != null && here.time < t.time) {
                    prev = here;
                    here = here.next;
                }

                t.next = here;
                t.prev = prev;
                if (prev != null) prev.next = t; else wheel[click] = t;
                if (here != null) here.prev = t;

                t.wheel = this;
                numtimers++;
            }

            public bool Remove(Timer! t)
            {
                if (t.wheel != this)
                    return false;

                uint click = (uint)((t.time / resolution) % clicks);

                if (wheel[click] == t) {
                    wheel[click] = t.next;
                    if (t.next != null)
                        t.next.prev = null;
                }
                else {

                    t.prev.next = t.next;
                    if (t.next != null)
                        t.next.prev = t.prev;
                }

                t.next = t.prev = null;
                t.wheel = null;
                numtimers--;
                return true;
            }

            public Timer GetSoonest()
            {
                if (numtimers == 0) {
                    return null;
                }

                uint click = (uint)((now / resolution) % clicks);
                // If we find anything less than bound then it IS the lowest
                ulong bound = now - now%resolution + resolution*clicks;
                Timer lowest = null;
                uint i = click;

                do
                {
                    Timer wi = wheel[i];

                    if (wi != null) {
                        if (wi.time < bound) {
                            return wi;
                        }
                        else if (lowest == null) {
                            lowest = wi;
                        }
                        else if (lowest.time > wi.time) {
                            lowest = wi;
                        }
                    }

                    i = (i+1) % clicks;

                } while (i != click);

                return lowest;
            }

            public Timer Advance()
            {
                Timer t = GetSoonest();
                if (t != null) {
                    Remove(t);
                    now = t.time;
                }
                return t;
            }
            /// <summary>
            /// Either advance to time, or return the first event before then
            /// </summary>
            public Timer Advance(ulong time)
            {
                Timer t = GetSoonest();
                if ((t == null) || (time < t.time)) {
                    now = time;
                    return null;
                }

                Remove(t);
                now = t.time;
                return t;
            }

            public TimerWheel(ulong resolution, uint clicks, ulong now)
            {
                this.wheel = new Timer[clicks];
                this.resolution = resolution;
                this.clicks = clicks;
                this.now = now;
            }
        } // TimerWheel
    } // Timer
}
// End
