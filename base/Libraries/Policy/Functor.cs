// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace Microsoft.Singularity.Policy.Engine
{
    // A Functor contains a symbol and an arity. The
    // functor f/3 is represented by new Functor("f", 3).
    internal class Functor : Cell {
        readonly string _name;
        readonly uint _arity;
        internal Functor(string name, uint arity) {
            _name = name;
            _arity = arity;
        }
        internal uint Arity { get { return _arity; } }
        public static bool operator ==(Functor f0, Functor f1) {
            return f0._name == f1._name && f0._arity == f1._arity;
        }
        public static bool operator !=(Functor f0, Functor f1) {
            return !(f0 == f1);
        }
        public override bool Equals(object obj) {
            if (obj == null) {
                return false;
            }
            Functor that = obj as Functor;
            if ((object)that == null) {
                return false;
            }
            return this == that;
        }
        public override int GetHashCode() {
            return _name.GetHashCode() ^ _arity.GetHashCode();
        }
        public override string ToString() {
            return _name + "/" + _arity.ToString();
        }
    }
}
