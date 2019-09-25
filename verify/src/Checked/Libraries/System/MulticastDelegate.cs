// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{
    using System;
    using System.Reflection;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="MulticastDelegate"]/*' />
    public abstract partial class MulticastDelegate : Delegate
    {
/*
        internal MulticastDelegate Previous
        {
            get{return _prev;}
            set{_prev = value;}
        }

        // equals returns true IIF the delegate is not null and has the
        //  same target, method and invocation list as this object
        //| <include path='docs/doc[@for="MulticastDelegate.Equals"]/*' />
        public override sealed bool Equals(Object obj)
        {
            if (!base.Equals(obj))
                return false;
            if (_prev != null)
                return _prev.InvocationListEquals(((MulticastDelegate) obj)._prev);
            else {
                // if we got here, "this" is a Multicast with only one listener.
                if (obj is MulticastDelegate)
                    return ((MulticastDelegate)obj)._prev == null;
                else if (obj is Delegate)
                    return true;
                else
                    return false;
            }
        }

        // Recursive function which will check for equality of the invocation list.
        private bool InvocationListEquals(MulticastDelegate d)
        {
            if (!base.Equals(d))
                return false;
            if (_prev == d._prev)
                return true;
            if (_prev == null)
                return (d._prev == null) ? true : false;
            return _prev.InvocationListEquals(d._prev);
        }

        // This method will combine this delegate with the passed delegate
        //  to form a new delegate.
        //| <include path='docs/doc[@for="MulticastDelegate.CombineImpl"]/*' />
        protected override sealed Delegate CombineImpl(Delegate follow)
        {
                    // Verify that the types are the same...
            if (this.GetType() != follow.GetType())
                throw new ArgumentException("Arg_DlgtTypeMis");

            // We always clone the delegate because this delegate is
            //  not changed by combine and remove.  We can safely tack
            //  the follow delegate onto the end of the copy.
            MulticastDelegate d = (MulticastDelegate) ((MulticastDelegate) follow).MemberwiseClone();
            MulticastDelegate root = d;
            while (d._prev != null) {
                d._prev = (MulticastDelegate) d._prev.MemberwiseClone();
                d = d._prev;
            }
            d._prev = (MulticastDelegate) this;
            return root;
        }

        // This method currently looks backward on the invocation list
        //  for an element that has Delegate based equality with value.  (Doesn't
        //  look at the invocation list.)  If this is found we remove it from
        //  this list and return a new delegate.  If its not found a copy of the
        //  current list is returned.
        //| <include path='docs/doc[@for="MulticastDelegate.RemoveImpl"]/*' />
        protected override sealed Delegate RemoveImpl(Delegate value)
        {
            // There is a special case were we are removing using a delegate as
            //  the value we need to check for this case
            //
            if (!(value is MulticastDelegate)) {
                if (base.Equals(value))
                    return _prev;
                return this;
            }

            // Look for the delegate...
            MulticastDelegate v = (MulticastDelegate) value;
            if (InternalEquals(v)) {
                int size = v.DelSize();
                MulticastDelegate p = _prev;
                while (--size != 0)
                    p = p._prev;
                return p;
            }

            MulticastDelegate d = (MulticastDelegate) this.MemberwiseClone();
            MulticastDelegate root = d;
            while (d._prev != null && d._prev.InternalEquals(v) != true) {
                d._prev = (MulticastDelegate) d._prev.MemberwiseClone();
                d = d._prev;
            }

            if (d._prev != null) {
                int size = v.DelSize();
                MulticastDelegate p = d._prev._prev;
                while (--size != 0)
                    p = p._prev;
                d._prev = p;
            }
            return root;
        }
        private int DelSize()
        {
            int i=0;
            MulticastDelegate d = this;
            while (d != null) {
                i++;
                d = d._prev;
            }
            return i;
        }


        // Stupid helper function to check equality based upon the super class.
        private bool InternalEquals(Delegate d)
        {
            if (!base.Equals(d))
                return false;
            if (((MulticastDelegate) d)._prev != null) {
                if (_prev == null)
                    return false;
                return _prev.InternalEquals(((MulticastDelegate) d)._prev);
            }
            return true;
        }


        // This method returns the Invocation list of this multicast delegate.
        //| <include path='docs/doc[@for="MulticastDelegate.GetInvocationList"]/*' />
        public override sealed Delegate[] GetInvocationList() {
            int i = 0;
            MulticastDelegate p;

            // How big is the invocation list?
            for (p = this; p != null; p = p._prev)
                i++;

            // Create an array of delegate copies and each
            //  element into the array (Need to reverse the order and make sure
            //  we set the _prev to null.
            Delegate[] del = new Delegate[i];
            for (p = this; p != null; p = p._prev) {
                del[--i] = (Delegate) p.MemberwiseClone();
                ((MulticastDelegate) del[i])._prev = null;
            }
            return del;
        }

    //  private static bool operator equals(MulticastDelegate d1, MulticastDelegate d2) {
    //      if ((Object)d1 == null)
    //          return (Object)d2 == null;
    //      return d1.Equals(d2);
    //  }  

        //| <include path='docs/doc[@for="MulticastDelegate.operatorEQ"]/*' />
        public static bool operator ==(MulticastDelegate d1, MulticastDelegate d2) {
            if ((Object)d1 == null)
                return (Object)d2 == null;
            return d1.Equals(d2);
        }

        //| <include path='docs/doc[@for="MulticastDelegate.operatorNE"]/*' />
        public static bool operator !=(MulticastDelegate d1, MulticastDelegate d2) {
            if ((Object)d1 == null)
                return (Object)d2 != null;
            return !d1.Equals(d2);
        }

        //| <include path='docs/doc[@for="MulticastDelegate.GetHashCode"]/*' />
        public override sealed int GetHashCode() {
            return base.GetHashCode();
        }

*/
    }
}
