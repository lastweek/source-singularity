// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  StringBuilder
//
// Purpose: A prototype implementation of the StringBuilder
// class.
//
//===========================================================  
namespace System.Text
{
    using System.Text;
    using System.Threading;
    using System;
    using System.Diagnostics;
    using System.Runtime.CompilerServices;

    // This class represents a mutable string.  It is convenient for situations in
    // which it is desirable to modify a string, perhaps by removing, replacing, or
    // inserting characters, without creating a new String subsequent to
    // each modification.
    //
    // The methods contained within this class do not return a new StringBuilder
    // object unless specified otherwise.  This class may be used in conjunction with the String
    // class to carry out modifications upon strings.
    //
    // When passing null into a constructor in VJ and VC, the null
    // should be explicitly type cast.
    // For Example:
    // StringBuilder sb1 = new StringBuilder((StringBuilder)null);
    // StringBuilder sb2 = new StringBuilder((String)null);
    //
    //| <include path='docs/doc[@for="StringBuilder"]/*' />
    public sealed partial class StringBuilder {

        //
        //
        //  CLASS VARIABLES
        //
        //
        [RequiredByBartok]
        internal String m_StringValue = null;

        internal int m_currentThread = InternalGetCurrentThread();
        internal int m_MaxCapacity = 0;


        //
        //
        // STATIC CONSTANTS
        //
        //
        private const int DEFAULT_CAPACITY = 16;
        private const int DEFAULT_MAX_CAPACITY = 0x7FFFFFFF;

        //
        //
        //CONSTRUCTORS
        //
        //

        // Creates a new empty string builder (i.e., it represents String.Empty)
        // with the default capacity (16 characters).
        //| <include path='docs/doc[@for="StringBuilder.StringBuilder"]/*' />
        public StringBuilder()
            : this(DEFAULT_CAPACITY) {
        }

        // Create a new empty string builder (i.e., it represents String.Empty)
        // with the specified capacity.
        //| <include path='docs/doc[@for="StringBuilder.StringBuilder1"]/*' />
        public StringBuilder(int capacity) {
            if (capacity < 0) {
                throw new ArgumentOutOfRangeException("capacity");
            }

            if (capacity == 0) { // MakeFromString enforces this
                capacity = DEFAULT_CAPACITY;
            }

            m_StringValue = String.GetStringForStringBuilder(String.Empty, capacity);
            m_MaxCapacity = Int32.MaxValue;
        }

        //=======================CalculateCapacity===============================
        // Calculates the new capacity of our buffer.  If the size of the
        // buffer is less than a fixed number (10000 in this case), we just
        // double the buffer until we have enough space.  Once we get larger
        // than 10000, we use a series of heuristics to determine the most
        // appropriate size.
        //======================================================================  
        private int CalculateCapacity(int currentCapacity, int neededCapacity)
        {
            // See also Lightning\Src\VM\COMStringBuffer.cpp::CalculateCapaity
            int newCapacity = neededCapacity;
            if (newCapacity == 0) {
                newCapacity = DEFAULT_CAPACITY;
            }
            if (neededCapacity > this.m_MaxCapacity) {
                throw new ArgumentOutOfRangeException("exceeding max capacity");
            }
            while (newCapacity < neededCapacity && newCapacity > 0) {
                newCapacity <<= 1;
            }
            // Check for overflow
            if (newCapacity <= 0) {
                // The C++ code throws on overflow, but it really should not
                newCapacity = this.m_MaxCapacity;
            }
            else if (newCapacity > this.m_MaxCapacity) {
                // We doubled past the max capacity, so back down a bit
                newCapacity = this.m_MaxCapacity;
            }
            return newCapacity;
        }

        // Creates a new string builder from the specified string.  If value
        // is a null String (i.e., if it represents String.NullString)
        // then the new string builder will also be null (i.e., it will also represent
        //  String.NullString).
        //
        //| <include path='docs/doc[@for="StringBuilder.StringBuilder2"]/*' />
        public StringBuilder(String value){
            MakeFromString(value, 0, -1, -1);
        }

        // Creates a new string builder from the specified string with the specified
        // capacity.  If value is a null String (i.e., if it represents
        // String.NullString) then the new string builder will also be null
        // (i.e., it will also represent String.NullString).
        // The maximum number of characters this string may contain is set by capacity.
        //
        //| <include path='docs/doc[@for="StringBuilder.StringBuilder3"]/*' />
        public StringBuilder(String value, int capacity) {
            if (capacity < 0) {
                throw new ArgumentOutOfRangeException("capacity",
                                                      String.Format("ArgumentOutOfRange_MustBePositive", "capacity"));
            }

            MakeFromString(value, 0, -1, capacity);
        }
        // Creates a new string builder from the specified substring with the specified
        // capacity.  The maximum number of characters is set by capacity.
        //

        //| <include path='docs/doc[@for="StringBuilder.StringBuilder4"]/*' />
        public StringBuilder(String value, int startIndex, int length, int capacity) {
            if (capacity < 0) {
                throw new ArgumentOutOfRangeException("capacity",
                                                      String.Format("ArgumentOutOfRange_MustBePositive", "capacity"));
            }
            if (length < 0) {
                throw new ArgumentOutOfRangeException("length",
                                                      String.Format("ArgumentOutOfRange_MustBeNonNegNum", "length"));
            }

            MakeFromString(value, startIndex, length, capacity);
        }

        // Creates an empty StringBuilder with a minimum capacity of capacity
        // and a maximum capacity of maxCapacity.
        //| <include path='docs/doc[@for="StringBuilder.StringBuilder5"]/*' />
        public StringBuilder(int capacity, int maxCapacity) {
            if (capacity > maxCapacity) {
                throw new ArgumentOutOfRangeException("capacity", "ArgumentOutOfRange_Capacity");
            }
            if (maxCapacity < 1) {
                throw new ArgumentOutOfRangeException("maxCapacity", "ArgumentOutOfRange_SmallMaxCapacity");
            }

            if (capacity < 0) {
                throw new ArgumentOutOfRangeException("capacity",
                                                      String.Format("ArgumentOutOfRange_MustBePositive", "capacity"));
            }
            if (capacity == 0) {
                capacity = DEFAULT_CAPACITY;
            }

            m_StringValue = String.GetStringForStringBuilder(String.Empty, capacity);
            m_MaxCapacity = maxCapacity;

        }

        private String GetThreadSafeString(out int tid) {
             String temp = m_StringValue;
             tid = InternalGetCurrentThread();
             if (m_currentThread == tid)
                return temp;
             return String.GetStringForStringBuilder(temp, temp.Capacity);
        }

        private static int InternalGetCurrentThread()
        {
            //TODO: return Thread.CurrentThread.GetThreadId();
            return (int)Kernel.CurrentThread;
        }

        //
        // Private native functions
        //
        //=========================MakeFromString================================
        // If value is null, we simply create an empty string with a default
        // length.  If it does contain data, we allocate space for twice this
        // amount of data, copy the data, associate it with the StringBuffer
        // and clear the CopyOnWrite bit.
        //=======================================================================  
        private void MakeFromString(String value, int startIndex, int length, int capacity)
        {
            // See also Lightning\Src\VM\COMStringBuffer.cpp::MakeFromString
            if (capacity <= 0) {
                capacity = DEFAULT_CAPACITY;
            }
            this.m_MaxCapacity = DEFAULT_MAX_CAPACITY;
            if (value != null) {
                if (startIndex < 0) {
                    throw new ArgumentOutOfRangeException("negative startIndex");
                }
                int stringLength = value.Length;
                if (length == -1) {
                    length = stringLength - startIndex;
                }
                else if (length + startIndex > stringLength) {
                    throw new ArgumentOutOfRangeException("exceeding string length");
                }
                int newCapacity = this.CalculateCapacity(capacity, length);
                String newString =
                    String.GetStringForStringBuilder(String.Empty, newCapacity);
                newString.AppendInPlace(value, startIndex, length, 0);
                this.m_StringValue = newString;
            }
            else if (capacity == 0) {
                this.m_StringValue = String.Empty;
            }
            else {
                this.m_StringValue =
                    String.GetStringForStringBuilder(String.Empty, capacity);
            }
        }

         //| <include path='docs/doc[@for="StringBuilder.Capacity"]/*' />
         public int Capacity {
             get {return m_StringValue.Capacity;} //-1 to account for terminating null.
             set {InternalSetCapacity(value);}
        }


        //| <include path='docs/doc[@for="StringBuilder.MaxCapacity"]/*' />
        public int MaxCapacity {
            get { return m_MaxCapacity; }

        }

        // Read-Only Property
        // Ensures that the capacity of this string builder is at least the specified value.
        // If capacity is greater than the capacity of this string builder, then the capacity
        // is set to capacity; otherwise the capacity is unchanged.
        //
        //| <include path='docs/doc[@for="StringBuilder.EnsureCapacity"]/*' />
        public int EnsureCapacity(int capacity) {
            if (capacity < 0) {
                throw new ArgumentOutOfRangeException("capacity", "ArgumentOutOfRange_NeedPosCapacity");
            }

            int tid;
            String currentString = GetThreadSafeString(out tid);

            //If we need more space or the COW bit is set, copy the buffer.
            if (!NeedsAllocation(currentString,capacity)) {
                return currentString.Capacity;
            }

            String newString = GetNewString(currentString,capacity);
            ReplaceString(tid,newString);
            return newString.Capacity;
        }

        //Sets the capacity to be capacity.  If capacity is less than the current
        //instance an ArgumentException is thrown.  If capacity is greater than the current
        //instance, memory is allocated to allow the StringBuilder to grow.
        //
        internal int InternalSetCapacity(int capacity)
        {
            // See also Lighting\Src\VM\COMStringBuffer.cpp::SetCapacity
            // The return value of the native code is a pointer to 'this', but
            // since it isn't ever used, we return 0;

            int tid;
            String thisString = GetThreadSafeString(out tid);
            if (capacity < 0) {
                throw new ArgumentOutOfRangeException("capacity is negative");
            }
            if (capacity < thisString.Length) {
                throw new ArgumentOutOfRangeException("capacity lesser than size");
            }
            if (capacity > this.m_MaxCapacity) {
                throw new ArgumentOutOfRangeException("exceeds max capacity");
            }
            if (capacity != this.m_StringValue.ArrayLength - 1) {
                this.m_StringValue = CopyString(this,thisString,capacity);
                this.m_currentThread = tid;
            }
            return 0;
        }

        private String CopyString(StringBuilder thisRef,String CurrString,
                                  int newCapacity)
        {
            int CurrLen = CurrString.Length;
            int copyLength;
            if (newCapacity >= CurrLen) {
                copyLength = CurrLen;
            }
            else {
                copyLength = newCapacity;
            }
            return String.NewString(CurrString,0,copyLength,newCapacity);
        }

        //| <include path='docs/doc[@for="StringBuilder.ToString"]/*' />
        public override String ToString() {
            String currentString = m_StringValue;
            int currentThread = m_currentThread;
            if (currentThread != 0 && currentThread != InternalGetCurrentThread()) {
                return String.InternalCopy(currentString);
            }

            if ((2 * currentString.Length) < currentString.ArrayLength) {
                return String.InternalCopy(currentString);
            }

            currentString.ClearPostNullChar();
            m_currentThread = 0;
            return  currentString;
        }

        // Converts a substring of this string builder to a String.
        //| <include path='docs/doc[@for="StringBuilder.ToString1"]/*' />
        public String ToString(int startIndex, int length) {
            return  m_StringValue.Substring(startIndex, length);
        }

        // Sets the length of the String in this buffer.  If length is less than the current
        // instance, the StringBuilder is truncated.  If length is greater than the current
        // instance, nulls are appended.  The capacity is adjusted to be the same as the length.

        //| <include path='docs/doc[@for="StringBuilder.Length"]/*' />
        public int Length {
            get {
               return  m_StringValue.Length;
            }
            set {
                int tid;
                String currentString = GetThreadSafeString(out tid);

                if (value == 0) { //the user is trying to clear the string
                     currentString.SetLength(0);
                     ReplaceString(tid,currentString);
                     return;
                }

                int currentLength = currentString.Length;
                int newlength = value;
                //If our length is less than 0 or greater than our Maximum capacity, bail.
                if (newlength < 0) {
                    throw new ArgumentOutOfRangeException("newlength", "ArgumentOutOfRange_NegativeLength");
                }

                if (newlength > MaxCapacity) {
                    throw new ArgumentOutOfRangeException("capacity", "ArgumentOutOfRange_SmallCapacity");
                }

                //Jump out early if our requested length our currentlength.
                //This will be a pretty rare branch.
                if (newlength == currentLength) {
                    return;
                }


                //If the StringBuilder has never been converted to a string, simply set the length
                //without allocating a new string.
                if (newlength <= currentString.Capacity) {
                        if (newlength > currentLength) {
                            for (int i = currentLength; i < newlength; i++) // This is a rare case anyway.
                                currentString.InternalSetCharNoBoundsCheck(i,'\0');
                        }

                        currentString.InternalSetCharNoBoundsCheck(newlength,'\0'); //Null terminate.
                        currentString.SetLength(newlength);
                        ReplaceString(tid,currentString);

                        return;
                }

                // CopyOnWrite set we need to allocate a String
                int newCapacity = (newlength>currentString.Capacity)?newlength:currentString.Capacity;
                String newString = String.GetStringForStringBuilder(currentString, newCapacity);

                //We know exactly how many characters we need, so embed that knowledge in the String.
                newString.SetLength(newlength);
                ReplaceString(tid,newString);
            }
        }

        //| <include path='docs/doc[@for="StringBuilder.this"]/*' />
        public char this[int index] {
            get {
                return  m_StringValue[index];
            }
            set {
                int tid;
                String currentString = GetThreadSafeString(out tid);
                currentString.SetChar(index, value);
                ReplaceString(tid,currentString);
            }
        }

        // Appends a character at the end of this string builder. The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append"]/*' />
        public StringBuilder Append(char value, int repeatCount) {
            if (repeatCount == 0) {
                return this;
            }
            if (repeatCount < 0) {
                throw new ArgumentOutOfRangeException("repeatCount", "ArgumentOutOfRange_NegativeCount");
            }


            int tid;
            String currentString = GetThreadSafeString(out tid);

            int currentLength = currentString.Length;
            int requiredLength = currentLength + repeatCount;

            if (requiredLength < 0)
                throw new OutOfMemoryException();

            if (!NeedsAllocation(currentString,requiredLength)) {
                currentString.AppendInPlace(value, repeatCount,currentLength);
                ReplaceString(tid,currentString);
                return this;
            }

            String newString = GetNewString(currentString,requiredLength);
            newString.AppendInPlace(value, repeatCount,currentLength);
            ReplaceString(tid,newString);
            return this;
        }

        // Appends an array of characters at the end of this string builder. The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append1"]/*' />
        public StringBuilder Append(char[] value, int startIndex, int charCount) {
            int requiredLength;

            if (value == null) {
                if (startIndex == 0 && charCount == 0) {
                    return this;
                }
                throw new ArgumentNullException("value");
            }

            if (charCount == 0) {
                return this;
            }

            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex", "ArgumentOutOfRange_GenericPositive");
            }
            if (charCount < 0) {
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_GenericPositive");
            }
            if (charCount > value.Length - startIndex) {
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_Index");
            }

            int tid;
            String currentString = GetThreadSafeString(out tid);

            int currentLength = currentString.Length;
            requiredLength = currentLength + charCount;
            if (NeedsAllocation(currentString,requiredLength)) {
                String newString = GetNewString(currentString,requiredLength);
                newString.AppendInPlace(value, startIndex, charCount,currentLength);
                ReplaceString(tid,newString);
            }
            else {
                currentString.AppendInPlace(value, startIndex, charCount,currentLength);
                ReplaceString(tid,currentString);
            }

            return this;
        }

        // Appends a copy of this string at the end of this string builder.
        //| <include path='docs/doc[@for="StringBuilder.Append2"]/*' />
        public StringBuilder Append(String value) {
            //If the value being added is null, eat the null
            //and return.
            if (value == null) {
                return this;
            }

            int tid;
            // hand inlining of GetThreadSafeString
            String currentString = m_StringValue;
            tid = InternalGetCurrentThread();
            if (m_currentThread != tid)
                currentString = String.GetStringForStringBuilder(currentString, currentString.Capacity);

            int currentLength = currentString.Length;

            int requiredLength = currentLength + value.Length;

            if (NeedsAllocation(currentString,requiredLength)) {
                String newString = GetNewString(currentString,requiredLength);
                newString.AppendInPlace(value,currentLength);
                ReplaceString(tid,newString);
            }
            else {
                currentString.AppendInPlace(value,currentLength);
                ReplaceString(tid,currentString);
            }

            return this;
        }

/*
        internal unsafe StringBuilder Append(char *value, int count) {
            //If the value being added is null, eat the null
            //and return.
            if (value == null) {
                return this;
            }


            int tid;
            String currentString = GetThreadSafeString(out tid);
            int currentLength = currentString.Length;

            int requiredLength = currentLength + count;

            if (NeedsAllocation(currentString,requiredLength)) {
                String newString = GetNewString(currentString,requiredLength);
                newString.AppendInPlace(value, count,currentLength);
                ReplaceString(tid,newString);
            }
            else {
                currentString.AppendInPlace(value,count,currentLength);
                ReplaceString(tid,currentString);
            }

            return this;
        }
*/

        private bool NeedsAllocation(String currentString,int requiredLength) {
            //<= accounts for the terminating 0 which we require on strings.
            return (currentString.ArrayLength<=requiredLength);
        }

        private String GetNewString(String currentString, int requiredLength) {
            int newCapacity;

            requiredLength++; //Include the terminating null.

            if (requiredLength < 0) {
                throw new OutOfMemoryException();
            }

            if (requiredLength > m_MaxCapacity) {
                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_NegativeCapacity",
                                                      "requiredLength");
            }

            newCapacity = ( currentString.Capacity)*2; // To force a predictable growth of 160,320 etc. for testing purposes

            if (newCapacity < requiredLength) {
                newCapacity = requiredLength;
            }

            if (newCapacity > m_MaxCapacity) {
                newCapacity = m_MaxCapacity;
            }

            if (newCapacity <= 0) {
                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_NegativeCapacity");
            }

            return String.GetStringForStringBuilder( currentString, newCapacity);
        }

        private void ReplaceString(int tid, String value) {
            Debug.Assert(value!=null, "[StringBuilder.ReplaceString]value!=null");

            m_currentThread = tid; // new owner
            m_StringValue = value;
        }

        // Appends a copy of the characters in value from startIndex to startIndex +
        // count at the end of this string builder.
        //| <include path='docs/doc[@for="StringBuilder.Append3"]/*' />
        public StringBuilder Append(String value, int startIndex, int count) {
            //If the value being added is null, eat the null
            //and return.
            if (value == null) {
                if (startIndex == 0 && count == 0) {
                    return this;
                }
                throw new ArgumentNullException("value");
            }

            if (count <= 0) {
                if (count == 0) {
                    return this;
                }
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_GenericPositive");
            }

            if (startIndex < 0 || (startIndex > value.Length - count)) {
                throw new ArgumentOutOfRangeException("startIndex", "ArgumentOutOfRange_Index");
            }

            int tid;
            String currentString = GetThreadSafeString(out tid);
            int currentLength = currentString.Length;

            int requiredLength = currentLength + count;

            if (NeedsAllocation(currentString,requiredLength)) {
                String newString = GetNewString(currentString,requiredLength);
                newString.AppendInPlace(value, startIndex, count, currentLength);
                ReplaceString(tid,newString);
            }
            else {
                currentString.AppendInPlace(value, startIndex, count, currentLength);
                ReplaceString(tid,currentString);
            }

            return this;
        }

        // Inserts multiple copies of a string into this string builder at the specified position.
        // Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, this
        // string builder is not changed. Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert"]/*' />
        public StringBuilder Insert(int index, String value, int count) {
              int tid;
              String currentString = GetThreadSafeString(out tid);
              int currentLength = currentString.Length;

              //If value isn't null, get all of our required values.
              if (value == null) {
                    if (index == 0 && count == 0) {
                         return this;
                    }
                    throw new ArgumentNullException("ArgumentNull_String");
              }

              //Range check the index.
              if (index < 0 || index > currentLength) {
                  throw new ArgumentOutOfRangeException("index","ArgumentOutOfRange_Index");
              }

              if (count < 1) {
                  throw new ArgumentOutOfRangeException("count","ArgumentOutOfRange_GenericPositive");
              }

               //Calculate the new length, ensure that we have the space and set the space variable for this buffer
               int requiredLength;
                try {
                   requiredLength = checked(currentLength + (value.Length * count));
                }
                catch (Exception) {
                   throw new OutOfMemoryException();
                }

               if (NeedsAllocation(currentString,requiredLength)) {
                    String newString = GetNewString(currentString,requiredLength);
                    newString.InsertInPlace(index, value, count, currentLength, requiredLength);
                    ReplaceString(tid,newString);
               }
               else {
                    currentString.InsertInPlace(index, value, count, currentLength, requiredLength);
                    ReplaceString(tid,currentString);
               }
               return this;
         }



        // Property.
        // Removes the specified characters from this string builder.
        // The length of this string builder is reduced by
        // length, but the capacity is unaffected.
        //
        //| <include path='docs/doc[@for="StringBuilder.Remove"]/*' />
        public StringBuilder Remove(int startIndex, int length)
        {
            // See also Lightning\Src\VM\COMStringBuffer.cpp::Remove
            int tid;
            String thisString = GetThreadSafeString(out tid);
            int thisLength = thisString.ArrayLength-1;
            if (length < 0) {
                throw new ArgumentOutOfRangeException("Negative length");
            }
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("Negative start index");
            }
            if (startIndex + length > thisLength) {
                throw new ArgumentOutOfRangeException("Exceeding string length");
            }
            thisString.RemoveRange(startIndex, length);
            this.m_StringValue = thisString;
            this.m_currentThread = tid;
            return this;
        }

        //
        //
        // PUBLIC INSTANCE FUNCTIONS
        //
        //

        //====================================Append====================================
        //
        //==============================================================================  
        // Appends a boolean to the end of this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append4"]/*' />
        public StringBuilder Append(bool value) {
            return Append(value.ToString());
        }

        // Appends an sbyte to this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append5"]/*' />
        [CLSCompliant(false)]
        public StringBuilder Append(sbyte value) {
            return Append(value.ToString());
        }

        // Appends a ubyte to this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append6"]/*' />
        public StringBuilder Append(byte value) {
            return Append(value.ToString());
        }

        // Appends a character at the end of this string builder. The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append7"]/*' />
        public StringBuilder Append(char value) {
            int tid;

            // hand inlining of GetThreadSafeString
            String currentString = m_StringValue;
            tid = InternalGetCurrentThread();
            if (m_currentThread != tid)
                currentString = String.GetStringForStringBuilder(currentString, currentString.Capacity);

            int currentLength = currentString.Length;
            if (!NeedsAllocation(currentString,currentLength + 1)) {
                currentString.AppendInPlace(value,currentLength);
                ReplaceString(tid,currentString);
                return this;
            }

            String newString = GetNewString(currentString,currentLength+1);
            newString.AppendInPlace(value,currentLength);
            ReplaceString(tid,newString);
            return this;
        }

        // Appends a short to this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append8"]/*' />
        public StringBuilder Append(short value) {
            return Append(value.ToString());
        }

        // Appends an int to this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append9"]/*' />
        public StringBuilder Append(int value) {
            return Append(value.ToString());
        }

        // Appends a long to this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append10"]/*' />
        public StringBuilder Append(long value) {
            return Append(value.ToString());
        }

        // Appends a float to this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append11"]/*' />
        public StringBuilder Append(float value) {
            return Append(value.ToString());
        }

        // Appends a double to this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append12"]/*' />
        public StringBuilder Append(double value) {
            return Append(value.ToString());
        }

        //| <include path='docs/doc[@for="StringBuilder.Append13"]/*' />
        public StringBuilder Append(decimal value) {
            return Append(value.ToString());
        }

        // Appends an ushort to this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append14"]/*' />
        [CLSCompliant(false)]
        public StringBuilder Append(ushort value) {
            return Append(value.ToString());
        }

        // Appends an uint to this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append15"]/*' />
        [CLSCompliant(false)]
        public StringBuilder Append(uint value) {
            return Append(value.ToString());
        }

        // Appends an unsigned long to this string builder.
        // The capacity is adjusted as needed.

        //| <include path='docs/doc[@for="StringBuilder.Append16"]/*' />
        [CLSCompliant(false)]
        public StringBuilder Append(ulong value) {
            return Append(value.ToString());
        }

        // Appends an Object to this string builder.
        // The capacity is adjusted as needed.
        //| <include path='docs/doc[@for="StringBuilder.Append17"]/*' />
        public StringBuilder Append(Object value) {
            if (null == value) {
                //Appending null is now a no-op.
                return this;
            }
            return Append(value.ToString());
        }

        // Appends all of the characters in value to the current instance.
        //| <include path='docs/doc[@for="StringBuilder.Append18"]/*' />
        public StringBuilder Append(char[] value) {
            if (null == value) {
                return this;
            }

            int valueLength = value.Length;

            int tid;
            String currentString = GetThreadSafeString(out tid);

            int currentLength = currentString.Length;
            int requiredLength = currentLength + value.Length;
            if (NeedsAllocation(currentString,requiredLength)) {
                String newString = GetNewString(currentString,requiredLength);
                newString.AppendInPlace(value, 0, valueLength,currentLength);
                ReplaceString(tid,newString);
            }
            else {
                currentString.AppendInPlace(value, 0, valueLength, currentLength);
                ReplaceString(tid,currentString);
            }
            return this;
        }

        //====================================Insert====================================
        //
        //==============================================================================  

        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert1"]/*' />
        public StringBuilder Insert(int index, String value) {
            if (value == null) // This is to do the index validation
                return Insert(index,value,0);
            else
                return Insert(index,value,1);
        }

        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert2"]/*' />
        public StringBuilder Insert( int index, bool value) {
            return Insert(index,value.ToString(),1);
        }

        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert3"]/*' />
        [CLSCompliant(false)]
        public StringBuilder Insert(int index, sbyte value) {
            return Insert(index,value.ToString(),1);
        }

        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert4"]/*' />
        public StringBuilder Insert(int index, byte value) {
            return Insert(index,value.ToString(),1);
        }

        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert5"]/*' />
        public StringBuilder Insert(int index, short value) {
            return Insert(index,value.ToString(),1);
        }

        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert6"]/*' />
        public StringBuilder Insert(int index, char value) {
            return Insert(index,Char.ToString(value),1);
        }

        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert7"]/*' />
        public StringBuilder Insert(int index, char[] value) {
            if (null == value) {
                return Insert(index, value, 0, 0);
            }
            return Insert(index, value, 0, value.Length);
        }

        // Returns a reference to the StringBuilder with charCount characters from
        // value inserted into the buffer at index.  Existing characters are shifted
        // to make room for the new text and capacity is adjusted as required.  If value is null, the StringBuilder
        // is unchanged.  Characters are taken from value starting at position startIndex.
        //| <include path='docs/doc[@for="StringBuilder.Insert8"]/*' />
        public StringBuilder Insert(int index, char []value, int startIndex, int charCount)
        {
            throw new Exception("System.Text.StringBuilder.Insert not implemented in Bartok");
        }

        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert9"]/*' />
        public StringBuilder Insert(int index, int value){
            return Insert(index,value.ToString(),1);
        }

        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert10"]/*' />
        public StringBuilder Insert(int index, long value) {
            return Insert(index,value.ToString(),1);
        }

        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert11"]/*' />
        public StringBuilder Insert(int index, float value) {
            return Insert(index,value.ToString(),1);
        }


        // Returns a reference to the StringBuilder with ; value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. ; Inserts ";<;no object>;"; if value
        // is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert12"]/*' />
        public StringBuilder Insert(int index, double value) {
            return Insert(index,value.ToString(),1);
        }

        //| <include path='docs/doc[@for="StringBuilder.Insert13"]/*' />
        public StringBuilder Insert(int index, decimal value) {
            return Insert(index,value.ToString(),1);
        }

        // Returns a reference to the StringBuilder with value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert14"]/*' />
        [CLSCompliant(false)]
        public StringBuilder Insert(int index, ushort value) {
            return Insert(index, value.ToString(),1);
        }


        // Returns a reference to the StringBuilder with value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert15"]/*' />
        [CLSCompliant(false)]
        public StringBuilder Insert(int index, uint value) {
            return Insert(index, value.ToString(), 1);
        }

        // Returns a reference to the StringBuilder with value inserted into
        // the buffer at index. Existing characters are shifted to make room for the new text.
        // The capacity is adjusted as needed.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert16"]/*' />
        [CLSCompliant(false)]
        public StringBuilder Insert(int index, ulong value) {
            return Insert(index, value.ToString(), 1);
        }

        // Returns a reference to this string builder with value inserted into
        // the buffer at index. Existing characters are shifted to make room for the
        // new text.  The capacity is adjusted as needed. If value equals String.Empty, the
        // StringBuilder is not changed. No changes are made if value is null.
        //
        //| <include path='docs/doc[@for="StringBuilder.Insert17"]/*' />
        public StringBuilder Insert(int index, Object value) {
            //If we get a null
            if (null == value) {
                return this;
            }
            return Insert(index,value.ToString(),1);
        }

        //| <include path='docs/doc[@for="StringBuilder.AppendFormat"]/*' />
        public StringBuilder AppendFormat(String format, Object arg0) {
            return AppendFormat(format, new Object[] {arg0});
        }

        //| <include path='docs/doc[@for="StringBuilder.AppendFormat1"]/*' />
        public StringBuilder AppendFormat(String format, Object arg0, Object arg1) {
            return AppendFormat(format, new Object[] {arg0, arg1});
        }

        //| <include path='docs/doc[@for="StringBuilder.AppendFormat2"]/*' />
        public StringBuilder AppendFormat(String format, Object arg0, Object arg1, Object arg2) {
            return AppendFormat(format, new Object[] {arg0, arg1, arg2});
        }

        private static void FormatError() {
            throw new FormatException("Format_InvalidString");
        }

        //| <include path='docs/doc[@for="StringBuilder.AppendFormat4"]/*' />
        public StringBuilder AppendFormat(String format, params Object[] args) {
            if (format == null || args == null) {
                throw new ArgumentNullException((format==null)?"format":"args");
            }
            char[] chars = format.ToCharArray(0, format.Length);
            int pos = 0;
            int len = chars.Length;
            char ch = '\x0';

            while (true) {
                int p = pos;
                int i = pos;
                while (pos < len) {
                    ch = chars[pos];

                    pos++;
                    if (ch == '}') {
                        if (pos < len && chars[pos] =='}') // Treat as escape character for }}
                            pos++;
                        else
                            FormatError();
                    }

                    if (ch == '{') {
                        if (pos < len && chars[pos] =='{') // Treat as escape character for {{
                            pos++;
                        else {
                            pos--;
                            break;
                        }
                    }

                    chars[i++] = ch;
                }
                if (i > p) Append(chars, p, i - p);
                if (pos == len) break;
                pos++;
                if (pos == len || (ch = chars[pos]) < '0' || ch > '9') FormatError();
                int index = 0;
                do {
                    index = index * 10 + ch - '0';
                    pos++;
                    if (pos == len) FormatError();
                    ch = chars[pos];
                } while (ch >= '0' && ch <= '9' && index < 1000000);
                if (index >= args.Length) throw new FormatException("Format_IndexOutOfRange");
                while (pos < len && (ch = chars[pos]) == ' ') pos++;
                bool leftJustify = false;
                int width = 0;
                if (ch == ',') {
                    pos++;
                    while (pos < len && chars[pos] == ' ') pos++;

                    if (pos == len) FormatError();
                    ch = chars[pos];
                    if (ch == '-') {
                        leftJustify = true;
                        pos++;
                        if (pos == len) FormatError();
                        ch = chars[pos];
                    }
                    if (ch < '0' || ch > '9') FormatError();
                    do {
                        width = width * 10 + ch - '0';
                        pos++;
                        if (pos == len) FormatError();
                        ch = chars[pos];
                    } while (ch >= '0' && ch <= '9' && width < 1000000);
                }

                while (pos < len && (ch = chars[pos]) == ' ') pos++;
                Object arg = args[index];
                String fmt = null;
                if (ch == ':') {
                    pos++;
                    p = pos;
                    i = pos;
                    while (true) {
                        if (pos == len) FormatError();
                        ch = chars[pos];
                        pos++;
                        if (ch == '{') {
                            if (pos < len && chars[pos] =='{') // Treat as escape character for {{
                                pos++;
                            else
                                FormatError();
                        }
                        else if (ch == '}') {
                            if (pos < len && chars[pos] =='}') // Treat as escape character for }}
                                pos++;
                            else {
                                pos--;
                                break;
                            }
                        }

                        chars[i++] = ch;
                    }
                    if (i > p) fmt = new String(chars, p, i - p);
                }
                if (ch != '}') FormatError();
                pos++;
                String s = null;

                if (s == null) {
                    if (arg is IFormattable) {
                        s = ((IFormattable)arg).ToString(fmt);
                    }
                    else if (arg != null) {
                        s = arg.ToString();
                    }
                }

                if (s == null) s = String.Empty;
                int pad = width - s.Length;
                if (!leftJustify && pad > 0) Append(' ', pad);
                Append(s);
                if (leftJustify && pad > 0) Append(' ', pad);
            }
            return this;
        }

        // Returns a reference to the current StringBuilder with all instances of oldString
        // replaced with newString.  If startIndex and count are specified,
        // we only replace strings completely contained in the range of startIndex to startIndex +
        // count.  The strings to be replaced are checked on an ordinal basis (e.g. not culture aware).  If
        // newValue is null, instances of oldValue are removed (e.g. replaced with nothing.).
        //
        //| <include path='docs/doc[@for="StringBuilder.Replace"]/*' />
        public StringBuilder Replace(String oldValue, String newValue) {
            return Replace(oldValue, newValue, 0, Length);
        }

        //| <include path='docs/doc[@for="StringBuilder.Replace1"]/*' />
        public StringBuilder Replace(String oldValue, String newValue, int startIndex, int count)
        {
            throw new Exception("System.Text.StringBuilder.Replace not implemented in Bartok");
        }

        //| <include path='docs/doc[@for="StringBuilder.Equals"]/*' />
        public bool Equals(StringBuilder sb)
        {
            if (sb == null)
                return false;
            return ((this.Capacity == sb.Capacity) && (this.MaxCapacity == sb.MaxCapacity) && (this. m_StringValue.Equals(sb. m_StringValue)));
        }

        // Returns a StringBuilder with all instances of oldChar replaced with
        // newChar.  The size of the StringBuilder is unchanged because we're only
        // replacing characters.  If startIndex and count are specified, we
        // only replace characters in the range from startIndex to startIndex+count
        //
        //| <include path='docs/doc[@for="StringBuilder.Replace2"]/*' />
        public StringBuilder Replace(char oldChar, char newChar) {
            return Replace(oldChar, newChar, 0, Length);
        }
        //| <include path='docs/doc[@for="StringBuilder.Replace3"]/*' />
        public StringBuilder Replace(char oldChar, char newChar, int startIndex, int count) {
            int tid;
            String currentString = GetThreadSafeString(out tid);
            int currentLength = currentString.Length;

            if ((uint)startIndex > (uint)currentLength) {
                throw new ArgumentOutOfRangeException("startIndex", "ArgumentOutOfRange_Index");
            }

            if (count < 0 || startIndex > currentLength - count) {
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_Index");
            }

            if (!NeedsAllocation(currentString,currentLength)) {
                currentString.ReplaceCharInPlace(oldChar, newChar, startIndex, count, currentLength);
                ReplaceString(tid,currentString);
                return this;
            }

            String newString = GetNewString(currentString,currentLength);
            newString.ReplaceCharInPlace(oldChar, newChar, startIndex, count, currentLength);
            ReplaceString(tid,newString);
            return this;
        }
    }
}



