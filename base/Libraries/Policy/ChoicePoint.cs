// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

﻿
namespace Microsoft.Singularity.Policy.Engine
{
    // A ChoicePoint is a single Cell containing a choice point. This replaces
    // the multiple cells used in the WAM in a more strongly typed way. The
    // ChoicePoint is followed on the stack by copies of the arguments.
    internal class ChoicePoint : Cell {
        internal readonly uint _n;
        internal readonly Address _ce;
        internal readonly Address _cp;
        internal readonly Address _b;
        internal /* not readonly */ Address _bp;
        internal readonly Address _tr;
        internal readonly Address _h;
        internal readonly Address _hb;
        internal ChoicePoint(
            uint n
          , Address ce
          , Address cp
          , Address b
          , Address bp
          , Address tr
          , Address h
          , Address hb
        ) {
            _n = n;
            _ce = ce;
            _cp = cp;
            _b = b;
            _bp = bp;
            _tr = tr;
            _h = h;
            _hb = hb;
        }
        public override string ToString() {
            return "<CHOICEPOINT "
                 + _n.ToString()
                 + " "
                 + _ce.ToString()
                 + " "
                 + _cp.ToString()
                 + " "
                 + _b.ToString()
                 + " "
                 + _bp.ToString()
                 + " "
                 + _tr.ToString()
                 + " "
                 + _h.ToString()
                 + " "
                 + _hb.ToString()
                 + ">";
        }
    }
}
