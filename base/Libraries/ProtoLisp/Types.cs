// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;

//
// This file defines the family of objects that are used to
// represent basic Proto-Lisp objects. They exist in order
// to make it easy to replace their implementation with
// more efficient versions if necessary, and to enable
// somewhat stronger type-checking for the Interpreter
// code.
//
namespace ProtoLisp
{
    // This is the common base class of ProtoLisp objects
    class PLObject
    {
        // empty
    }

    // This is the common base class of ProtoLisp atoms
    class PLAtom : PLObject
    {
        // empty
    }

    // A string atom is a non-number atom. It's a pass-through
    // container for a String.
    class PLStringAtom : PLAtom
    {
        public PLStringAtom(string s)
        {
            myval = s;
        }

        public override bool Equals(Object other)
        {
            if (other is PLStringAtom) {
                return myval.Equals(((PLStringAtom)other).myval);
            }
            else {
                return myval.Equals(other);
            }
        }

        public override int GetHashCode()
        {
            return myval.GetHashCode();
        }

        public override string ToString()
        {
            return myval;
        }

        private string myval;
    }

    // A numeric atom. Currently implemented with a plain int,
    // which means floating-point isn't supported.
    class PLNumberAtom : PLAtom
    {
        public PLNumberAtom(string s)
        {
            myval = Int32.Parse(s);
        }

        private PLNumberAtom(int val)
        {
            myval = val;
        }

        public override bool Equals(Object other)
        {
            if (other is PLNumberAtom) {
                return myval.Equals(((PLNumberAtom)other).myval);
            }
            else {
                return myval.Equals(other);
            }
        }

        public override int GetHashCode()
        {
            return myval.GetHashCode();
        }

        public override string ToString()
        {
            return myval.ToString();
        }

        public static PLNumberAtom operator+ (PLNumberAtom a, PLNumberAtom b)
        {
            return new PLNumberAtom(a.myval + b.myval);
        }

        public static PLNumberAtom operator- (PLNumberAtom a, PLNumberAtom b)
        {
            return new PLNumberAtom(a.myval - b.myval);
        }

        public static PLNumberAtom operator* (PLNumberAtom a, PLNumberAtom b)
        {
            return new PLNumberAtom(a.myval * b.myval);
        }

        public static PLNumberAtom operator/ (PLNumberAtom a, PLNumberAtom b)
        {
            return new PLNumberAtom(a.myval / b.myval);
        }

        private int myval;
    }

    // The internal representation of lists.
    class PLList : PLObject
    {
        public PLList()
        {
            myval = new ArrayList();
        }

        public void Add(PLObject o)
        {
            myval.Add(o);
        }

        public PLObject this[int index]
        {
            get { return (PLObject)myval[index]; }
            set { myval[index] = value; }
        }

        public int Count
        {
            get { return myval.Count; }
        }

        public override int GetHashCode()
        {
            return myval.GetHashCode();
        }

        private ArrayList myval;
    }

    // Our internal representation of an "environment" (a binding of
    // symbolic names to values)
    class PLEnvironment : ICloneable
    {
        public PLEnvironment()
        {
            table = new Hashtable();
        }

        private PLEnvironment(PLEnvironment other)
        {
            // Snapshot the other
            table = (Hashtable)other.table.Clone();
        }

        public void Put(string name, PLObject val)
        {
            table[name] = val;
        }

        public PLObject Lookup(string name)
        {
            return (PLObject)table[name];
        }

        public object Clone()
        {
            return new PLEnvironment(this);
        }

        private Hashtable table;
    }

    // The internal representation of function closures
    // (function arg list, body expression, plus environment for free variables)
    class PLClosure : PLObject
    {
        // The constructor clones the environment to capture the closure
        public PLClosure(PLList funArgs, PLObject funBody, PLEnvironment environment)
        {
            // Check argument names
            for (int i = 0; i < funArgs.Count; ++i) {
                if (!(funArgs[i] is PLStringAtom)) {
                    throw new Exception("Attempt to define a procedure with arguments that are not string atoms");
                }
            }

            argNames = funArgs;
            body = funBody;

            // Snapshot the environment
            if (environment != null) {
                env = (PLEnvironment)environment.Clone();
            }
        }

        public readonly PLList argNames;
        public readonly PLObject body;
        public readonly PLEnvironment env;
    }
}
