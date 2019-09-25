////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    This file was ported from the Coriolis codebase to Singularity.
//

namespace System.Net
{
    //
    // support class for Validation related stuff.
    //
    internal class ValidationHelper {

        public static string [] EmptyArray = new string[0];

        internal static readonly char[]  InvalidMethodChars =
                new char[]{
                ' ',
                '\r',
                '\n',
                '\t'
                };

        // invalid characters that cannot be found in a valid method-verb or http header
        internal static readonly char[]  InvalidParamChars =
                new char[]{
                '(',
                ')',
                '<',
                '>',
                '@',
                ',',
                ';',
                ':',
                '\\',
                '"',
                '\'',
                '/',
                '[',
                ']',
                '?',
                '=',
                '{',
                '}',
                ' ',
                '\t',
                '\r',
                '\n'};

        public static string [] MakeEmptyArrayNull(string [] stringArray) {
            if (stringArray == null || stringArray.Length == 0) {
                return null;
            }
            else {
                return stringArray;
            }
        }

        public static string MakeStringNull(string stringValue) {
            if (stringValue == null || stringValue.Length == 0) {
                return null;
            }
            else {
                return stringValue;
            }
        }

        public static string MakeStringEmpty(string stringValue) {
            if (stringValue == null || stringValue.Length == 0) {
                return String.Empty;
            }
            else {
                return stringValue;
            }
        }

        public static int HashCode(object objectValue) {
            if (objectValue == null) {
                return -1;
            }
            else {
                return objectValue.GetHashCode();
            }
        }
        public static string ExceptionMessage(Exception exception) {
            if (exception == null) {
                return string.Empty;
            }
            if (exception.InnerException == null) {
                return exception.Message;
            }
            return exception.Message + " (" + ExceptionMessage(exception.InnerException) + ")";
        }

        public static string ToString(object objectValue) {
            if (objectValue == null) {
                return "(null)";
            }
            else if (objectValue is string && ((string)objectValue).Length == 0) {
                return "(string.empty)";
            }
            else if (objectValue is Exception) {
                return ExceptionMessage(objectValue as Exception);
            }
            else if (objectValue is IntPtr) {
                return "0x" + String.Format("{0x}", ((IntPtr)objectValue));
            }
            else {
                return objectValue.ToString();
            }
        }
        public static string HashString(object objectValue) {
            if (objectValue == null) {
                return "(null)";
            }
            else if (objectValue is string && ((string)objectValue).Length == 0) {
                return "(string.empty)";
            }
            else {
                return objectValue.GetHashCode().ToString();
            }
        }

        public static bool IsInvalidHttpString(string stringValue) {
            return stringValue.IndexOfAny(InvalidParamChars)!=-1;
        }

        public static bool IsBlankString(string stringValue) {
            return stringValue==null || stringValue.Length==0;
        }

        public static bool ValidateUInt32(long address) {
            // on false, API should throw new ArgumentOutOfRangeException("address");
            return address>=0x00000000 && address<=0xFFFFFFFF;
        }

        public static bool ValidateTcpPort(int port) {
            // on false, API should throw new ArgumentOutOfRangeException("port");
            return port>=IPEndPoint.MinPort && port<=IPEndPoint.MaxPort;
        }

        public static bool ValidateRange(int actual, int fromAllowed, int toAllowed) {
            // on false, API should throw new ArgumentOutOfRangeException("argument");
            return actual>=fromAllowed && actual<=toAllowed;
        }

        public static bool ValidateRange(long actual, long fromAllowed, long toAllowed) {
            // on false, API should throw new ArgumentOutOfRangeException("argument");
            return actual>=fromAllowed && actual<=toAllowed;
        }
    }
}
