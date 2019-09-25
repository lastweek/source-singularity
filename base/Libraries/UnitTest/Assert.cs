///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Assert.cs
//
//  Note:
//

using System;
using System.Threading;
using System.Collections;

namespace Microsoft.Singularity.UnitTest
{
    public sealed class Assert
    {
        private static int passes   = 0;
        private static int failures = 0;

        /// <summary>
        /// Accessor for the number of assertions passed.
        /// </summary>
        public static int Passes { get { return passes; } }

        /// <summary>
        /// Accessor for the number of assertions failed.
        /// </summary>
        public static int Failures { get { return failures; } }

        private static void True(bool condition,
                                 string userMessage,
                                 string /*!*/ conditionMessage)
        {
            if (!condition) {
                Interlocked.Increment(ref failures);
                UnitTest.Throw(new FailedAssertionException(userMessage,
                                                          conditionMessage));
            }
            Interlocked.Increment(ref passes);
        }

        public static void True(bool condition, string userMessage)
        {
            if (!condition) {
                Interlocked.Increment(ref failures);
                UnitTest.Throw(new FailedAssertionException(userMessage));
            }
            Interlocked.Increment(ref passes);
        }

        public static void IsTrue(bool condition, string userMessage)
        {
            True(condition, userMessage);
        }

        public static void False(bool condition, string message)
        {
            Assert.True(!condition, message);
        }

        public static void Null(object obj, string message)
        {
            Assert.True(obj == null, message);
        }

        public static void NonNull(object obj, string message)
        {
            Assert.True(obj != null, message);
        }

        public static void SameObject(object object1,
                                      object object2,
                                      string message)
        {
            Assert.True(Object.ReferenceEquals(object1, object2),
                        message,
                        "Expected references to the same object.");
        }

        public static void NotSameObject(object object1,
                                         object object2,
                                         string message)
        {
            Assert.True(!Object.ReferenceEquals(object1, object2),
                        message,
                        "Expected references to the different objects.");
        }

        public static void Equal(object object1,
                                 object object2,
                                 string message)
        {
            Assert.True(Object.Equals(object1, object2),
                        message,
                        "Expected objects to be equal.");
        }

        public static void NotEqual(object object1,
                                    object object2,
                                    string message)
        {
            Assert.True(!Object.Equals(object1, object2),
                        message,
                        "Expected objects to be different.");
        }

#region script generated region

        private static void FailEqual(IComparable /*!*/ u,
                                      IComparable /*!*/ v,
                                      string message)
        {
            Assert.True(false, message,
                        string.Format("Failed equality test: {0} == {1} is false.", u, v));
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(sbyte u, sbyte v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(byte u, byte v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(short u, short v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(ushort u, ushort v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(int u, int v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(uint u, uint v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(long u, long v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(ulong u, ulong v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(char u, char v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(float u, float v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(double u, double v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(decimal u, decimal v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(IComparable /*!*/ u, IComparable /*!*/ v, string message)
        {
            if (!(u.CompareTo(v) == 0)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Equal(bool u, bool v, string message)
        {
            if (!(u == v)) FailEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        private static void FailGreater(IComparable /*!*/ u,
                                        IComparable /*!*/ v,
                                        string message)
        {
            Assert.True(false, message,
                        string.Format("Failed greater than test: {0} > {1} is false.", u, v));
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(sbyte u, sbyte v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(byte u, byte v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(short u, short v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(ushort u, ushort v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(int u, int v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(uint u, uint v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(long u, long v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(ulong u, ulong v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(char u, char v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(float u, float v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(double u, double v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(decimal u, decimal v, string message)
        {
            if (!(u > v)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Greater(IComparable /*!*/ u, IComparable /*!*/ v, string message)
        {
            if (!(u.CompareTo(v) > 0)) FailGreater(u, v, message);
            Interlocked.Increment(ref passes);
        }

        private static void FailGreaterOrEqual(IComparable /*!*/ u,
                                               IComparable /*!*/ v,
                                               string message)
        {
            Assert.True(false, message,
                        string.Format("Failed greater than or equal to test: {0} >= {1} is false.", u, v));
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(sbyte u, sbyte v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(byte u, byte v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(short u, short v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(ushort u, ushort v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(int u, int v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(uint u, uint v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(long u, long v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(ulong u, ulong v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(char u, char v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(float u, float v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(double u, double v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(decimal u, decimal v, string message)
        {
            if (!(u >= v)) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is greater than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void GreaterOrEqual(IComparable /*!*/ u, IComparable /*!*/ v, string message)
        {
            if (u.CompareTo(v) < 0) FailGreaterOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        private static void FailLess(IComparable /*!*/ u,
                                     IComparable /*!*/ v,
                                     string message)
        {
            Assert.True(false, message,
                        string.Format("Failed less than test: {0} < {1} is false.", u, v));
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(sbyte u, sbyte v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(byte u, byte v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(short u, short v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(ushort u, ushort v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(int u, int v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(uint u, uint v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(long u, long v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(ulong u, ulong v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(char u, char v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(float u, float v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(double u, double v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(decimal u, decimal v, string message)
        {
            if (!(u < v)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void Less(IComparable /*!*/ u, IComparable /*!*/ v, string message)
        {
            if (!(u.CompareTo(v) < 0)) FailLess(u, v, message);
            Interlocked.Increment(ref passes);
        }

        private static void FailLessOrEqual(IComparable /*!*/ u,
                                            IComparable /*!*/ v,
                                            string message)
        {
            Assert.True(false, message,
                        string.Format("Failed less than or equal to test: {0} <= {1} is false.", u, v));
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(sbyte u, sbyte v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(byte u, byte v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(short u, short v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(ushort u, ushort v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(int u, int v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(uint u, uint v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(long u, long v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(ulong u, ulong v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(char u, char v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(float u, float v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(double u, double v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(decimal u, decimal v, string message)
        {
            if (!(u <= v)) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

        ///<summary>
        /// Asserts the first argument is less than or equal to the
        /// second argument.
        /// <para>
        /// If the assertion fails, the method adds the
        /// values and comparison to the error message so
        /// the user does not have to supply this
        /// information in the <paramref name="message"/>
        /// argument.
        /// </para>
        ///</summary>
        /// <param name = "u">The first argument. </param>
        /// <param name = "v">The second argument. </param>
        /// <param name = "message">The message displayed
        /// on failure. </param>
        public static void LessOrEqual(IComparable /*!*/ u, IComparable /*!*/ v, string message)
        {
            if (u.CompareTo(v) > 0) FailLessOrEqual(u, v, message);
            Interlocked.Increment(ref passes);
        }

#endregion script generated region
    }
}
