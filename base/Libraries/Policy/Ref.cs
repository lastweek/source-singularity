// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace Microsoft.Singularity.Policy.Engine
{
    // A Ref is a Cell containing an Address. A new
    // <REF addr> is represented by a new Ref(addr).
    internal class Ref : Cell {
        Address _value;
        internal Address Value { get { return _value; } set { _value = value; } }
        internal Ref(Address value) { _value = value; }
        public override string ToString() {
            if (_value._cell == this) {
                return "<REF>";
            }
            else {
                return "<REF " + _value.ToString() + ">";
            }
        }
    }
}
