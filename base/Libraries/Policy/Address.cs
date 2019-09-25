// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;

namespace Microsoft.Singularity.Policy.Engine
{
    // An Address is an index into an Area.
    internal class Address {
        readonly uint _at;
        readonly Area _in;
        internal Address(Area @in, uint @at) { _in = @in; _at = @at; }
        internal uint At { get { return _at; } }
        internal uint Order { get { return _in._order; } }
        internal object this[int i] {
            get { return _in[(uint)(_at + i)]; }
            set { _in[(uint)(_at + i)] = value; }
        }
        internal object this[
            uint i
        ] { get { return _in[_at + i]; } set { _in[_at + i] = value; } }
        internal object _object {
            get { return this[0]; }
            set { this[0] = value; }
        }
        internal Address _address {
            get { return (Address)this[0]; }
            set { this[0] = value; }
        }
        internal Cell _cell {
            get { return (Cell)this[0]; }
            set { this[0] = value; }
        }
        internal Instruction _instruction {
            get { return (Instruction)this[0]; }
            set { this[0] = value; }
        }
        public static Address operator +(Address a, int i) {
            return new Address(a._in, (uint)(a._at + i));
        }
        public static Address operator +(Address a, uint i) {
            return new Address(a._in, (uint)(a._at + i));
        }
        public static Address operator -(Address a, int i) {
            return new Address(a._in, (uint)(a._at - i));
        }
        public static Address operator -(Address a, uint i) {
            return new Address(a._in, (uint)(a._at - i));
        }
        public static bool operator ==(Address a0, Address a1) {
            if ((object)a0 == null) {
                return (object)a1 == null;
            }
            if ((object)a1 == null) {
                return false;
            }
            return a0._at == a1._at && a0._in == a1._in;
        }
        public static bool operator !=(Address a0, Address a1) {
            return !(a0 == a1);
        }
        public override bool Equals(object obj) {
            if (obj == null) {
                return false;
            }
            Address that = obj as Address;
            if (that == null) {
                return false;
            }
            return this == that;
        }
        public override int GetHashCode() {
            return _at.GetHashCode() ^ unchecked((int)_in._order);
        }
        public override string ToString() {
            return _in.ToString()
                 + "@"
                 + _at.ToString()
                 + " => "
                 + this._object.ToString();
        }
    }
}
