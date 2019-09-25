// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class: CharEnumerator
//
// Purpose: Enumerates the characters on a string.  skips range
//          checks.
//
//============================================================  
namespace System
{

    using System.Collections;

    //| <include path='docs/doc[@for="CharEnumerator"]/*' />
    public sealed class CharEnumerator : IEnumerator, ICloneable {
        private String str;
        private int index;
        private char currentElement;

        internal CharEnumerator(String str) {
            this.str = str;
            this.index = -1;
        }

        //| <include path='docs/doc[@for="CharEnumerator.Clone"]/*' />
        public Object Clone() {
            return MemberwiseClone();
        }

        //| <include path='docs/doc[@for="CharEnumerator.MoveNext"]/*' />
        public bool MoveNext() {
            if (index < (str.Length - 1)) {
                index++;
                currentElement = str[index];
                return true;
            }
            else
                index = str.Length;
            return false;

        }

        //| <include path='docs/doc[@for="CharEnumerator.IEnumerator.Current"]/*' />
        /// <internalonly/>
        Object IEnumerator.Current {
            get {
                if (index == -1)
                    throw new InvalidOperationException("InvalidOperation_EnumNotStarted");
                if (index >= str.Length)
                    throw new InvalidOperationException("InvalidOperation_EnumEnded");

                return currentElement;
            }
        }

        //| <include path='docs/doc[@for="CharEnumerator.Current"]/*' />
        public char Current {
            get {
                if (index == -1)
                    throw new InvalidOperationException("InvalidOperation_EnumNotStarted");
                if (index >= str.Length)
                    throw new InvalidOperationException("InvalidOperation_EnumEnded");
                return currentElement;
            }
        }

        //| <include path='docs/doc[@for="CharEnumerator.Reset"]/*' />
        public void Reset() {
            currentElement = (char)0;
            index = -1;
        }
    }
}
