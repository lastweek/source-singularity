////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    This file was ported, from the Coriolis codebase to Singularity.
//

namespace System.Web.Util
{
    using System.Text;
    using System.Globalization;

    //
    // Various string handling utilities
    // 
    internal class StringUtil {
        internal static string CheckAndTrimString(string paramValue, string paramName) {
            return CheckAndTrimString(paramValue, paramName, true);
        }

        internal static string CheckAndTrimString(string paramValue, string paramName, bool throwIfNull) {
            return CheckAndTrimString(paramValue, paramName, throwIfNull, -1);
        }

        internal static string CheckAndTrimString(string paramValue, string paramName,
                                                  bool throwIfNull, int lengthToCheck) {
            if (paramValue == null) {
                if (throwIfNull) {
                    throw new ArgumentNullException(paramName);
                }
                return null;
            }
            string trimmedValue = paramValue.Trim();
            if (trimmedValue.Length == 0) {
                throw new ArgumentException("Tried to trim an empty string");
            }
            if (lengthToCheck > - 1 && trimmedValue.Length > lengthToCheck) {
                throw new ArgumentException("Tried to trim a string that exceeded the maximum length");
            }
            return trimmedValue;
        }

        internal static bool Equals(string s1, string s2) {
            if (s1 == s2) {
                return true;
            }

            if (IsEmpty(s1) && IsEmpty(s2)) {
                return true;
            }

            return false;
        }

        internal static bool EqualsIgnoreCase(string s1, string s2) {
            if (IsEmpty(s1) && IsEmpty(s2)) {
                return true;
            }
            if (IsEmpty(s1) || IsEmpty(s2)) {
                return false;
            }
            if (s2.Length != s1.Length) {
                return false;
            }
            return 0 == string.Compare(s1, 0, s2, 0, s2.Length, true);
        }

        internal static bool IsEmpty(string s) {
            return s == null || s.Length == 0;
        }

        //
        // Determines if the string ends with the specified character.
        // Fast, non-culture aware.
        // 
        internal static bool StringEndsWith(string s, char c) {
            int len = s.Length;
            return len != 0 && s[len - 1] == c;
        }

        //
        // Determines if the first string ends with the second string.
        // Fast, non-culture aware.
        // 
        internal static bool StringEndsWith(string s1, string s2) {
            int offset = s1.Length - s2.Length;
            if (offset < 0) {
                return false;
            }

            return 0 == string.Compare(s1, offset, s2, 0, s2.Length);
        }

        //
        // Determines if the first string ends with the second string, ignoring case.
        // Fast, non-culture aware.
        // 
        internal static bool StringEndsWithIgnoreCase(string s1, string s2) {
            int offset = s1.Length - s2.Length;
            if (offset < 0) {
                return false;
            }

            return 0 == string.Compare(s1, offset, s2, 0, s2.Length, true);
        }

        //
        // Determines if the string starts with the specified character.
        // Fast, non-culture aware.
        // 
        internal static bool StringStartsWith(string s, char c) {
            return s.Length != 0 && (s[0] == c);
        }

        //
        // Determines if the first string starts with the second string.
        // Fast, non-culture aware.
        // 
        internal static bool StringStartsWith(string s1, string s2) {
            if (s2.Length > s1.Length) {
                return false;
            }

            return 0 == string.Compare(s1, 0, s2, 0, s2.Length);
        }

        //
        // Determines if the first string starts with the second string, ignoring case.
        // Fast, non-culture aware.
        // 
        internal static bool StringStartsWithIgnoreCase(string s1, string s2) {
            if (s2.Length > s1.Length) {
                return false;
            }

            return 0 == string.Compare(s1, 0, s2, 0, s2.Length, true);
        }

        internal static bool StringArrayEquals(string[] a, string [] b) {
            if ((a == null) != (b == null)) {
                return false;
            }

            if (a == null) {
                return true;
            }

            int n = a.Length;
            if (n != b.Length) {
                return false;
            }

            for (int i = 0; i < n; i++) {
                if (a[i] != b[i]) {
                    return false;
                }
            }

            return true;
        }
    }
}
