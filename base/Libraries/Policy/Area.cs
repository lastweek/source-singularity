// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System.Collections;

namespace Microsoft.Singularity.Policy.Engine
{
    // An Area is a contiguous region of objects, indexed by uints.

    // The contents of an Area are held in a Hashtable.
    // An optimization would use an object[] array.
    internal class Area {
        Hashtable _contents;
        string _name;
        internal readonly uint _order;
        internal object this[
            uint i
        ] { get { return _contents[i]; } set { _contents[i] = value; } }
        internal Area(string name, uint order) {
            _contents = new Hashtable();
            _name = name;
            _order = order;
        }
        internal Area(string name, Area area) {
            _contents = area._contents;
            _name = name;
            _order = area._order;
        }
        public override string ToString() { return _name; }
    }
}
