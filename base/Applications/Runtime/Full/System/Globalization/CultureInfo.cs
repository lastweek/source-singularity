// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
////////////////////////////////////////////////////////////////////////////
//
//  Class:    CultureInfo
//
//  Purpose:  This class represents the software preferences of a particular
//            culture or community.  It includes information such as the
//            language, writing system, and a calendar used by the culture
//            as well as methods for common operations such as printing
//            dates and sorting strings.
//
////////////////////////////////////////////////////////////////////////////

namespace System.Globalization
{
    using System;
    using System.Threading;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using Microsoft.Singularity;

    //| <include path='docs/doc[@for="CultureInfo"]/*' />
    public class CultureInfo {
        // singleton to simplify porting of parsing code
        private static CultureInfo currentCulture;

        static CultureInfo()
        {
            currentCulture = new CultureInfo();
        }

        private CultureInfo() {}   // Prevent from being created

        public static String Name {
            get { return sName; }
        }

        public static String DisplayName {
            get { return sName; }
        }

        public static String NativeName {
            get { return sNativeDisplayName; }
        }

        public static String EnglishName {
            get { return sEngDisplayName; }
        }

        public static String TwoLetterISOLanguageName {
            get { return sIso639LangName; }
        }

        public static String ThreeLetterISOLanguageName {
            get { return sIso639LangName2; }
        }

        public static String ThreeLetterWindowsLanguageName {
            get { return sAbbrevLangName; }
        }

        internal static ushort iDigits              = 2;     // iDigits
        internal static ushort iNegNumber           = 1;     // iNegNumber
        internal static ushort iCalendarType        = 1;     // iCalendarType
        internal static ushort iFirstDayOfWeek      = 0;     // iFirstDayOfWeek
        internal static ushort iFirstWeekOfYear     = 0;     // iFirstWeekOfYear
        internal static ushort iLanguage            = 127;   // iLanguage
        internal static ushort NativeLangId         = 127;   // NativeLangId
        internal static ushort iNegativePercent     = 0;     // iNegativePercent
        internal static ushort iPositivePercent     = 0;     // iPositivePercent

        internal static string sList                = ",";
        internal static string sDecimal             = ".";
        internal static string sThousand            = ",";
        internal static int[]  nGrouping            = new int[] {3};
        internal static string sMonDecimalSep       = ".";
        internal static string sMonThousandSep      = ",";
        internal static int[]  nMonGrouping         = new int[] {3};
        internal static string sPositiveSign        = "+";
        internal static string sNegativeSign        = "-";
        internal static string[] sTimeFormat        = new string[] {
            "HH:mm:ss" };
        internal static string sTime                = ":";
        internal static string s1159                = "AM";
        internal static string s2359                = "PM";
        internal static string[] sShortDate         = new string[] {
            "MM/dd/yyyy" };
        internal static string sDate                = "/";
        internal static string[] sLongDate          = new string[] {
            "dddd, dd MMMM yyyy", };
        internal static string sName                = "";
        internal static string sEngDisplayName      = "Invariant Language (Invariant Country)";
        internal static string sAbbrevLangName      = "IVL";
        internal static string sIso639LangName      = "iv";
        internal static string sIso639LangName2     = "IVL";
        internal static string sNativeDisplayName   = "Invariant Language (Invariant Country)";
        internal static string sPercent             = "%";
        internal static string sNan                 = "NaN";
        internal static string sPosInfinity         = "Infinity";
        internal static string sNegInfinity         = "-Infinity";
        internal static string[] sShortTime         = new string[] {
            "HH:mm", "hh:mm tt", "H:mm", "h:mm tt", };
        internal static string sYearMonth           = "yyyy MMMM";
        internal static string sMonthDay            = "MMMM dd";
        internal static string[] sDayNames          = new string[7] {
            "Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday" };
        internal static string[] sAbbrevDayName     = new string[7] {
            "Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat" };
        internal static string[] sMonthNames        = new string[13] {
            "January", "February", "March", "April",
            "May", "June", "July", "August", "September",
            "October", "November", "December",
            "" };
        internal static string[] sAbbrevMonthNames  = new string[13] {
            "Jan", "Feb", "Mar", "Apr",
            "May", "Jun", "Jul", "Aug",
            "Sep", "Oct", "Nov", "Dec",
            "" };
        internal static string sADEra               = "A.D.";
        internal static string[] sDateWords         = new string[] {};
        internal static string sAbbevADEra          = "AD";
        internal static string[] sMonthGenitiveName = new string[] {};
        internal static string[] sAbbrevMonthGenitiveName   = new string[] {};

        // E.g. "1;6"
        // 0:sTimeFormat
        // 1:sShortDate
        // 2:sLongDate
        // 3:sShortTime
        // 4:sDateWords

        // added to support System.Text.RegularExpressions

        public static CultureInfo CurrentCulture
        {
            get
            {
                return currentCulture;
            }
        }

        public static CultureInfo InvariantCulture
        {
            get
            {
                return currentCulture;
            }
        }
    }
}
