///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

using System;
using Microsoft.Contracts;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Test.Contracts;

namespace Microsoft.Singularity.UnitTest
{
    public class TestLog
    {
        private bool m_logSuccess;

        // CREATION ///////////////////////////////////////////////

        public TestLog(bool logSuccess)
        {
            m_logSuccess = logSuccess;
        }

        // QUERIES ///////////////////////////////////////////////

        public bool LogSuccess
        {
            get { return m_logSuccess; }
        }


        // OPERATIONS ////////////////////////////////////////////
        // Diplay for user convenience that some progress is happening.  This is for
        // interactive use only, and might not be recorded in any logs.
        public void ShowProgress()
        {
            Console.Write(".");
        }

        public void Pass(string/*!*/ message)
        {
            if (m_logSuccess) {
                Info(message);
            }
        }

        virtual public void Info(string/*!*/ message)
        {
            Console.WriteLine("INFO {0}", message);
        }

        virtual public void Fail(string/*!*/ message)
        {
            Console.WriteLine("FAIL {0}", message);
        }

        public void True(bool condition, string/*!*/ userMessage)
        {
            if (condition) {
                Pass(userMessage);
            }
            else {
                Fail(userMessage);
            }
        }

        // Skip out of this test if the condition is not true.
        public void Continue(bool condition, string/*!*/ reason)
        {
            if (!condition) {
                throw new TestSkippedException(reason);
            }
        }

        public void False(bool condition, string/*!*/ message)
        {
            True(!condition, message);
        }

        public void Null(object obj, string/*!*/ message)
        {
            True(obj == null, message);
        }

        public void NotNull(object obj, string/*!*/ message)
        {
            True(obj != null, message);
        }

        public void SameObject(object a, object b, string/*!*/ message)
        {
            True(ReferenceEquals(a, b),
                 message,
                 "references to the same object");
        }

        public void NotSameObject(object a, object b, string/*!*/ message)
        {
            True(!ReferenceEquals(a, b),
                 message,
                 "references to different objects");
        }

        /// <summary>
        ///     Asserts that the actual type 'is a' type equal to or derived
        ///     from the expected type.
        /// </summary>
        public void IsA(Type/*!*/ actual, Type/*!*/ expected, string/*!*/ message)
        {
            True(expected.IsAssignableFrom(actual),
                 message,
                 String.Format("Type {0} is not a {1}", actual.Name, expected.Name));
        }

        /// <summary>
        ///     Asserts that the object 'is a' instance of the expected type
        ///     using the same semantics as the C# 'is' operator.
        /// </summary>
        public void IsA(object actual, Type/*!*/ expected, string/*!*/ message)
        {
            if (actual == null) {
                True(false,
                     message,
                     "Null values fail type comparisons");
            } else {
                IsA(actual.GetType(), expected, message);
            }
        }

        public void Equal(object a, object b, string/*!*/ message)
        {
            True(Equals(a, b), message, "objects are equal");
        }

        public void NotEqual(object a, object b, string/*!*/ message)
        {
            True(!Equals(a, b), message, "objects are not equal.");
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
        public void Equal(sbyte u, sbyte v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(byte u, byte v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(short u, short v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(ushort u, ushort v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(int u, int v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(uint u, uint v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(long u, long v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(ulong u, ulong v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(char u, char v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(float u, float v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(double u, double v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(decimal u, decimal v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(IComparable /*!*/ u, IComparable /*!*/ v, string/*!*/ message)
        {
            if (u.CompareTo(v) == 0) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Equal(bool u, bool v, string/*!*/ message)
        {
            if (u == v) {
                Pass(message);
            }
            else {
                FailOperator("==", u, v, message);
            }
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
        public void Greater(sbyte u, sbyte v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(byte u, byte v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(short u, short v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(ushort u, ushort v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(int u, int v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(uint u, uint v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(long u, long v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(ulong u, ulong v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(char u, char v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(float u, float v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(double u, double v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(decimal u, decimal v, string/*!*/ message)
        {
            if (u > v) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void Greater(IComparable /*!*/ u, IComparable /*!*/ v, string/*!*/ message)
        {
            if (u.CompareTo(v) > 0) {
                Pass(message);
            }
            else {
                FailOperator(">", u, v, message);
            }
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
        public void GreaterOrEqual(sbyte u, sbyte v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(byte u, byte v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(short u, short v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(ushort u, ushort v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(int u, int v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(uint u, uint v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(long u, long v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(ulong u, ulong v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(char u, char v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(float u, float v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(double u, double v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(decimal u, decimal v, string/*!*/ message)
        {
            if (u >= v) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void GreaterOrEqual(IComparable /*!*/ u, IComparable /*!*/ v, string/*!*/ message)
        {
            if (u.CompareTo(v) >= 0) {
                Pass(message);
            }
            else {
                FailOperator(">=", u, v, message);
            }
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
        public void Less(sbyte u, sbyte v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(byte u, byte v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(short u, short v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(ushort u, ushort v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(int u, int v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(uint u, uint v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(long u, long v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(ulong u, ulong v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(char u, char v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(float u, float v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(double u, double v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(decimal u, decimal v, string/*!*/ message)
        {
            if (u < v) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void Less(IComparable /*!*/ u, IComparable /*!*/ v, string/*!*/ message)
        {
            if (u.CompareTo(v) < 0) {
                Pass(message);
            }
            else {
                FailOperator("<", u, v, message);
            }
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
        public void LessOrEqual(sbyte u, sbyte v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(byte u, byte v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(short u, short v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(ushort u, ushort v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(int u, int v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(uint u, uint v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(long u, long v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(ulong u, ulong v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(char u, char v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(float u, float v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(double u, double v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(decimal u, decimal v, string/*!*/ message)
        {
            if (u <= v) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
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
        public void LessOrEqual(IComparable /*!*/ u, IComparable /*!*/ v, string/*!*/ message)
        {
            if (u.CompareTo(v) <= 0) {
                Pass(message);
            }
            else {
                FailOperator("<=", u, v, message);
            }
        }

        private void FailOperator(string /*!*/ op,
                                  IComparable /*!*/ u,
                                  IComparable /*!*/ v,
                                  string /*!*/ message)
        {
            True(false,
                 message,
                 string.Format("{0} {1} {2} is false.", u, op, v));
        }

        private void True(bool condition,
                          string /*!*/ userMessage,
                          string /*!*/ detail)
        {
            if (condition) {
                Pass(userMessage);
            }
            else {
                Fail(string.Format("EXPECTED: \"{0}\"; Detail: {1}", userMessage, detail));
            }
        }
    }

    internal class RemoteTestLog : TestLog
    {
        private ModuleTester/*!*/ m_jig;

        // CREATION ///////////////////////////////////////////////

        public RemoteTestLog([Delayed] ModuleTester/*!*/ jig, bool logSuccess)
            : base(logSuccess)
        {
            m_jig = jig;
        }

        // OPERATIONS /////////////////////////////////////////////
        override public void Info(string/*!*/ message)
        {
            m_jig.Log(message);
        }

        override public void Fail(string/*!*/ message)
        {
            m_jig.Fail(message);
        }
    }
}
