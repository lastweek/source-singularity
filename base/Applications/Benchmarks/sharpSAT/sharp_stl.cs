// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Diagnostics;
//using Microsoft.Zap;
namespace SharpSAT
{
    public class IntVector : SATCommon
    {
        private int [] elements;
        private int numElements;

        [Microsoft.Contracts.NotDelayed]
        public IntVector(int sz)
        {
            numElements = 0;
            elements = new int[sz];
        }

        [Microsoft.Contracts.NotDelayed]
        public IntVector (IntVector cp)
        {
            numElements = cp.numElements;
            elements = new int[cp.elements.Length];
            Array.Copy(cp.elements, elements, numElements);
        }

        public void sort ()
        {
            Array.Sort(elements, null, 0, numElements);
        }
        public int binary_search(int v)
        {
            return Array.BinarySearch(elements,0,numElements,v);
        }

        public void push_back(int v)
        {
            if (numElements == elements.Length) {
                int [] old = elements;
                elements = new int [numElements + numElements];
                Array.Copy (old, elements, numElements);
            }
            elements[numElements] = v;
            ++ numElements;
        }

        public int[] ToArray()
        {
            int [] result = new int [numElements];
            Array.Copy(elements, result, numElements);
            return result;
        }

        public int this [int idx]
        {
            get {sharp_assert (idx < numElements); return elements[idx];}
            set {sharp_assert (idx < numElements); elements[idx] = value;}
        }

        public void clear()     { numElements = 0; }
        public void pop_back()  { --numElements; }
        public int size()       { return numElements; }
        public void resize (int k )
        {
            int l = elements.Length;
            while (k > l)
                l += l;
            if (l > elements.Length) {
                int [] old = elements;
                elements = new int [l];
                Array.Copy (old, elements, numElements);
            }
            numElements = k;
            return;
        }

        public int back
        {
            get { return elements[numElements - 1];   }
            set { elements[numElements - 1] = value; }
        }
        public bool empty()     { return numElements == 0; }
    }


    public class ObjVector
    {
        private object [] elements;
        private int numElements;

        public ObjVector(int n)
        {
            numElements = 0;
            elements = new object [n];
        }

        public void push_back(object v)
        {
            if (numElements == elements.Length) {
                object [] old = elements;
                elements = new object [numElements + numElements];
                Array.Copy (old, elements, numElements);
            }
            elements[numElements] = v;
            ++ numElements;
        }

        public object this [int idx]
        {
            get {return elements[idx];}
            set {elements[idx] = value;}
        }

        public void clear()
        {
            for (int i = 0; i < numElements; ++i)
                elements[i] = null;
            numElements = 0;
        }
        public void pop_back()  { elements[--numElements] = null; }
        public int size()       { return numElements; }
        public object back
        {
            get {return elements[numElements - 1];   }
            set { elements[numElements - 1] = value; }
        }
        public bool empty()     { return numElements == 0; }
    }

    public class ClsVector
    {
        private Clause [] elements;
        private int numElements;

        public ClsVector(int n)
        {
            numElements = 0;
            elements = new Clause [n];
        }

        public void push_back(Clause v)
        {
            if (numElements == elements.Length) {
                Clause [] old = elements;
                elements = new Clause [numElements + numElements];
                Array.Copy (old, elements, numElements);
            }
            elements[numElements] = v;
            ++ numElements;
        }

        public Clause this [int idx]
        {
            get {return elements[idx];}
            set {elements[idx] = value;}
        }

        public void clear()
        {
            for (int i = 0; i < numElements; ++i)
                elements[i] = null;
            numElements = 0;
        }
        public void pop_back()  { elements[--numElements] = null; }
        public int size()       { return numElements; }
        public Clause back
        {
            get {return elements[numElements - 1];   }
            set { elements[numElements - 1] = value; }
        }
        public bool empty()     { return numElements == 0; }
    }

    public class VarVector
    {
        private Variable [] elements;
        private int numElements;

        public VarVector(int n)
        {
            numElements = 0;
            elements = new Variable [n];
        }

        public void push_back(Variable v)
        {
            if (numElements == elements.Length) {
                Variable [] old = elements;
                elements = new Variable [numElements + numElements];
                Array.Copy (old, elements, numElements);
            }
            elements[numElements] = v;
            ++ numElements;
        }

        public Variable this [int idx]
        {
            get {return elements[idx];}
            set {elements[idx] = value;}
        }

        public void clear()
        {
            for (int i = 0; i < numElements; ++i)
                elements[i] = null;
            numElements = 0;
        }
        public void pop_back()  { elements[--numElements] = null; }
        public int size()       { return numElements; }
        public Variable back
        {
            get {return elements[numElements - 1];   }
            set { elements[numElements - 1] = value; }
        }
        public bool empty()     { return numElements == 0; }
    }
}
