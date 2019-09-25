// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

﻿using System;
using System.Collections;

namespace Microsoft.Singularity.Policy.Engine
{
    // The Wam class implements a restricted version of the Warren
    // Abstract Machine, as described in "Warren's Abstract
    // Machine: A Tutorial Reconstruction" by Hassan Ait-Kaci
    // (February 18, 1999, reprinted from the MIT Press version).

    // All variables are treated as permanent,
    // so there are no temporary Xn registers.

    // The code area is an Area of Instructions.

    // The heap is an Area of Cells, where a
    // Cell can be a Ref, a Str, or a Functor.

    // The stack is an Area of Cells, where a Cell can also be an Environment
    // or a ChoicePoint. These are stored as single cells with a strongly
    // typed internal structure. The cells for permanent variables follow an
    // Environment; the cells for copies of arguments follow a ChoicePoint.

    // Argument registers are stored in a separate Area of Cells.

    // The trail is an Area of Addresses of Cells
    // that must be unbound upon backtracking.

    // The PDL is local to the Unify procedure, and is a .NET Stack.

    // There are no anonymous variables: set_void and unify_void are
    // unimplemented. Anonymous variables can be added as an optimization.

    // There is no environment trimming: the WAM instruction
    // "call P, N" is replaced by the simpler "call P".
    // Environment trimming can be added as an optimization.

    // There is no TCO: execute, put_unsafe_value,
    // set_local_value, and unify_local_value are
    // unimplemented. TCO can be added as an optimization.

    // There are no list instructions: put_list and get_list are
    // unimplemented. List instructions can be added as an optimization.

    // There are no constant instructions: put_constant, set_constant,
    // get_constant, and unify-constant are unimplemented.
    // Constant instructions can be added as an optimization.

    // There are no indexing instructions: switch_on_term, switch_on_constant,
    // switch_on_structure, try, retry, and trust are unimplemented.
    // Indexing instructions can be added as an optimization.
    internal class Wam {
        Area _heap = new Area("HEAP", 1);
        Address _h, _s;
        Area _a;
        // _code really shouldn't be visible
        internal Area _code = new Area("CODE", 0);
        Address _p, _cp;
        // _label really shouldn't be visible
        internal Hashtable _label = new Hashtable();
        Area _stack = new Area("STACK", 2);
        // _e really shouldn't be visible
        internal Address _e;
        enum Mode { None, Read, Write };
        Mode _mode = Mode.None;
        internal Area A { get { return _a; } }
        // BACKTRACKING
        Address _b, _hb;
        // CUT
        Address _b0;
        // TRAIL
        Area _trail = new Area("TRAIL", 3);
        Address _tr;
        // failure
        bool _fail = false;

        // Put instructions. There is no TCO, so put_unsafe_value
        // is unimplemented. There are no list instructions,
        // so put_list is unimplemented. There are no constant
        // instructions, so put_constant is unimplemented.

        // PutVariable always allocates a heap cell.
        internal void PutVariable(Address yn, Address ai) {
            ai._cell = yn._cell = _h._cell = new Ref(_h);
            _h = _h + 1;
        }
        internal void PutValue(Address yn, Address ai) { ai._cell = yn._cell; }
        // PutStructure always allocates a STR cell on the heap.
        internal void PutStructure(Functor fn, Address yn) {
            _h[0] = new Str(_h);
            _h[1] = fn;
            yn._cell = _h._cell;
            _h = _h + 2;
        }

        // Get instructions. There are no list instructions,
        // so get_list is unimplemented. There are no constant
        // instructions, so get_constant is unimplemented.
        internal void GetVariable(Address yn, Address ai) {
            yn._cell = ai._cell;
        }
        internal void GetValue(Address yn, Address ai) {
            Unify(yn, ai);
            if (_fail) {
                Backtrack();
            }
        }
        internal void GetStructure(Functor fn, Address ai) {
            Address addr = Deref(ai);
            if (addr._cell is Ref) {
                _h[0] = new Str(_h + 1);
                _h[1] = fn;
                Bind(addr, _h);
                _h = _h + 2;
                // Is this right? It conflicts with the errata.
                _s = null;
                _mode = Mode.Write;
            }
            else if (addr._cell is Str) {
                Address a = ((Str)addr._cell).Value;
                if (a._cell.Equals(fn)) {
                    _s = a + 1;
                    _mode = Mode.Read;
                }
                else {
                    _fail = true;
                }
            }
            else {
                _fail = true;
            }
            if (_fail) {
                Backtrack();
            }
        }

        // Set instructions. There is no TCO, so set_local_value
        // is unimplemented. There are no constant instructions,
        // so set_constant is unimplemented. There are no
        // anonymous variables, so set_void is unimplemented.
        internal void SetVariable(Address yn) {
            yn._cell = _h._cell = new Ref(_h);
            _h = _h + 1;
        }
        internal void SetValue(Address yn) { _h[0] = yn._cell; _h = _h + 1; }

        // Unify instructions. There is no TCO, so unify_local_value
        // is unimplemented. There are no constant instructions,
        // so unify-constant is unimplemented. There are no
        // anonymous variables, so unify_void is unimplemented.
        internal void UnifyVariable(Address yn) {
            switch (_mode) {
            case Mode.Read:
                yn._cell = _s._cell;
                break;
            case Mode.Write:
                yn._cell = _h._cell = new Ref(_h);
                _h = _h + 1;
                break;
            default:
                throw new Exception();
            }
            _s = _s + 1;
        }
        internal void UnifyValue(Address yn) {
            switch (_mode) {
            case Mode.Read:
                Unify(yn, _s);
                break;
            case Mode.Write:
                _h[0] = yn._cell;
                _h = _h + 1;
                break;
            default:
                throw new Exception();
            }
            _s = _s + 1;
            if (_fail) {
                Backtrack();
            }
        }

        // Control instructions. There is no environment trimming,
        // so the WAM instruction "call P, N" is replaced with
        // "call P". There is no TCO, so execute is unimplemented.
        internal void Allocate(uint n) {
            Address e;
            if (Greater(_e, _b)) {
                e = _e + 1 + ((Environment)_e._cell)._n;
            }
            else {
                e = _b + 1 + ((ChoicePoint)_b._cell)._n;
            }
            e._cell = new Environment(n, _e, _cp);
            _e = e;
        }
        internal void Deallocate() {
            _cp = ((Environment)_e._cell)._cp;
            _e = ((Environment)_e._cell)._ce;
        }
        internal void Call(Functor P) {
            if (_label.ContainsKey(P)) {
                _cp = _p;
                _p = (Address)_label[P];
            }
            else {
                Backtrack();
            }
        }
        internal void Proceed() { _p = _cp; }

        // Choice instructions. There are no indexing instructions,
        // so try, retry, and trust are unimplemented.
        internal void TryMeElse(Address L, uint n) {
            Address b;
            if (Greater(_e, _b)) {
                b = _e + 1 + ((Environment)_e._cell)._n;
            }
            else {
                b = _b + 1 + ((ChoicePoint)_b._cell)._n;
            }
            ChoicePoint b_ = new ChoicePoint(n, _e, _cp, _b, L, _tr, _h, _hb);
            b._cell = b_;
            for (uint i = 1; i <= n; i++) {
                b[i] = _a[i];
            }
            _b = b;
            _hb = _h;
        }
        internal void RetryMeElse(Address L) {
            ChoicePoint b_ = (ChoicePoint)_b._cell;
            uint n = b_._n;
            for (uint i = 1; i <= n; i++) {
                _a[i] = _b[i];
            }
            _e = b_._ce;
            _cp = b_._cp;
            b_._bp = L;
            UnwindTrail(b_._tr._address, _tr._address);
            _tr = b_._tr;
            _h = b_._h;
            _hb = _h;
        }
        internal void TrustMe() {
            ChoicePoint b_ = (ChoicePoint)_b._cell;
            uint n = b_._n;
            for (uint i = 1; i <= n; i++) {
                _a[i] = _b[i];
            }
            _e = b_._ce;
            _cp = b_._cp;
            UnwindTrail(b_._tr._address, _tr._address);
            _tr = b_._tr;
            _h = b_._h;
            _b = b_._b;
            _hb = ((ChoicePoint)_b._cell)._hb;
        }

        // Cut instructions.
        void NeckCut() { if (Greater(_b, _b0)) { _b = _b0; TidyTrail(); } }
        void GetLevel(Address yn) { yn._address = _b0; }
        void Cut(Address yn) {
            if (Greater(_b, yn._address)) {
                _b0 = yn._address; TidyTrail();
            }
        }

        // Ancillary functions.
        internal void Backtrack() {
            _fail = false;
            if (_b == null) {
                throw new Exception("fail and exit program");
            }
            else {
                _p = ((ChoicePoint)_b._cell)._bp;
            }
        }
        Address Deref(Address a) {
            if (a._cell is Ref) {
                Address value = (a._cell as Ref).Value;
                if (value != a) {
                    return Deref(value);
                }
            }
            return a;
        }
        void Bind(Address a1, Address a2) {
            // should add an occurs-check
            if (a1._cell is Ref && (!(a2._cell is Ref) || Less(a2, a1))) {
                a1._cell = a2._cell;
                Trail(a1);
            }
            else {
                a2._cell = a1._cell;
                Trail(a2);
            }
        }
        void Trail(Address a) {
            if (Less(a, _hb) || Less(_h, a) && Less(a, _b)) {
                _tr._address = a;
                _tr = _tr + 1;
            }
        }
        void UnwindTrail(Address a1, Address a2) {
            Address a = a1;
            while (Less(a, a2)) {
                a._cell = new Ref(a); a = a + 1;
            }
        }
        void TidyTrail() {
            Address i = ((ChoicePoint)_b._cell)._tr;
            while (Less(i, _tr)) {
                if (
                    Less(i._address, _hb)
                 || Less(_h, i._address) && Less(i._address, _b)
                ) {
                    i = i + 1;
                }
                else {
                    _tr = _tr - 1;
                    i._cell = _tr._cell;
                }
            }
        }
        void Unify(Address a1, Address a2) {
            Stack pdl = new Stack();
            pdl.Push(a1);
            pdl.Push(a2);
            _fail = false;
            while (!(pdl.Count == 0 || _fail)) {
                Address d1 = Deref((Address)pdl.Pop());
                Address d2 = Deref((Address)pdl.Pop());
                if (d1 != d2) {
                    Cell cell1 = d1._cell;
                    Cell cell2 = d2._cell;
                    if (cell1 is Ref) {
                        Bind(d1, d2);
                    }
                    else {
                        if (cell2 is Ref) {
                            Bind(d1, d2);
                        }
                        else if (cell2 is Str) {
                            if (!(cell1 is Str)) {
                                _fail = true;
                            }
                            else {
                                Address v1 = ((Str)cell1).Value;
                                Address v2 = ((Str)cell2).Value;
                                Functor f1 = (Functor)v1._cell;
                                Functor f2 = (Functor)v2._cell;
                                if (f1 != f2) {
                                    _fail = true;
                                }
                                else {
                                    for (int i = 1; i <= f1.Arity; i++) {
                                        pdl.Push(v1 + i);
                                        pdl.Push(v2 + i);
                                    }
                                }
                            }
                        }
                        else {
                            _fail = true;
                        }
                    }
                }
            }
        }

        // Other functions
        bool Less(Address a, Address b) {
            return a.Order < b.Order || a.Order == b.Order && a.At < b.At;
        }
        bool Greater(Address a, Address b) { return Less(b, a); }

        // Run starts execution of the WAM at _p (the current instruction).
        internal void Run() {
            while (_p != null) {
                Instruction instr = _p._instruction;
                _p = _p + 1;
                instr._execute();
            }
        }

        // The constructor.
        internal Wam() {
            _h = _hb = new Address(_heap, 0);
            _a = new Area("A", 9);
            _p = new Address(_code, 0);
            _b = new Address(_stack, 0);
            _b[0]
          = new ChoicePoint(0, null, null, null, null, null, null, null);
            _e = _b + 1;
            _e[0] = new Environment(0, null, null);
            _tr = new Address(_trail, 0);
        }
    }
}
