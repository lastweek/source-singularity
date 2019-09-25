// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace Microsoft.Singularity.Policy.Engine
{
    // A Str is a Cell containing the Address of a functor cell.
    // A new <STR addr> is represented by a new Str(addr).
    class Str : Cell
    {
        readonly Address _value;
        internal Address Value { get { return _value; } }
        internal Str(Address value) { _value = value; }
        public override string ToString() {
            return "<STR " + _value.ToString() + ">";
        }
    }
}
