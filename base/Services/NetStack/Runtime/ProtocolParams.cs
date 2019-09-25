// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

using System;
using System.Collections.Specialized;

using System.Net.IP;
using Drivers.Net;

namespace NetStack.Runtime
{
    /// <summary>
    /// This class encapsulated the modules parameters
    /// as given in the configuration file.
    /// The interpretation of each parameter is module specific.
    /// </summary>
    public class ProtocolParams : StringDictionary
    {
        /// <summary>
        /// Read a named integer parameter from a <c>ProtocolParams</c>
        /// instance.
        /// </summary>
        /// <returns><paramref name="defaultValue"/> if <paramref name="parameters"/> 
        /// is <c>null</c> or <paramref name="parameterName"/> 
        /// cannot be found.  Otherwise it
        /// returns the named parameter as an integer.</returns>
        public static int LookupInt32(ProtocolParams parameters,
                                      string         parameterName,
                                      int            defaultValue)
        {
            if (parameters == null) {
                return defaultValue;
            }
            else if (parameterName == null) {
                throw new ArgumentNullException();
            }

            string sValue = parameters[parameterName];
            if (sValue == null) {
                return defaultValue;
            }

            try {
                return Int32.Parse(sValue);
            }
            catch {
                Core.Log("Failed on parameter \"{0}\" value \"{1}\"\n",
                         parameterName, sValue);
                return defaultValue;
            }
        }

        /// <summary>
        /// Read a named unsigned integer parameter from a
        /// <c>ProtocolParams</c> instance.
        /// </summary>
        /// <returns><paramref name="defaultValue"/> if <paramref name="parameters"/>
        /// is <c>null</c> or <paramref name="parameterName"/> cannot be found.
        /// Otherwise it returns the named parameter as an unsigned
        /// integer.</returns>
        public static uint LookupUInt32(ProtocolParams parameters,
                                        string         parameterName,
                                        uint           defaultValue)
        {
            if (parameters == null) {
                return defaultValue;
            }
            else if (parameterName == null) {
                throw new ArgumentNullException();
            }

            string sValue = parameters[parameterName];
            if (sValue == null) {
                return defaultValue;
            }

            try {
                return UInt32.Parse(sValue);
            }
            catch {
                Core.Log("Failed on parameter \"{0}\" value \"{1}\"\n",
                         parameterName, sValue);
                return defaultValue;
            }
        }

        /// <summary>
        /// Read a named IPv4 parameter from a <c>ProtocolParams</c>
        /// instance.
        /// </summary>
        /// <returns><paramref name="defaultValue"/> if <paramref name="parameters"/> 
        /// is <c>null</c> or <paramref name="parameterName"/> cannot be found. 
        /// Otherwise it returns the named parameter as an IPv4 address.</returns>
        public static IPv4 LookupIPv4(ProtocolParams parameters,
                                      string       parameterName,
                                      IPv4         defaultValue)
        {
            if (parameters == null) {
                return defaultValue;
            }
            else if (parameterName == null) {
                throw new ArgumentNullException();
            }

            string sValue = parameters[parameterName];
            if (sValue == null) {
                return defaultValue;
            }

            try {
                return IPv4.Parse(sValue);
            }
            catch (FormatException) {
                Core.Log("Failed on parameter \"{0}\" value \"{1}\"\n",
                         parameterName, sValue);
            }
            return defaultValue;
        }

        /// <summary>
        /// Read a named string parameter from a <c>ProtocolParams</c>
        /// instance.
        /// </summary>
        /// <returns><paramref name="defaultValue"/> if <paramref name="parameters"/> 
        /// is <c>null</c> or <paramref name="parameterName"/> cannot be found.
        /// Otherwise it returns the named parameter as a string.</returns>
        public static string LookupString(ProtocolParams parameters,
                                          string         parameterName,
                                          string         defaultValue)
        {
            if (parameters == null) {
                return defaultValue;
            }
            else if (parameterName == null) {
                throw new ArgumentNullException();
            }

            string sValue = parameters[parameterName];
            if (sValue == null) {
                return defaultValue;
            }
            return sValue;
        }

        /// <summary>
        /// Read a named boolean parameter from a <c>ProtocolParams</c>
        /// instance.
        /// </summary>
        /// <returns><paramref name="defaultValue"/> if <paramref name="parameters"/>
        /// is <c>null</c> or <paramref name="parameterName"/> cannot be found.
        /// Otherwise it returns the named parameter as a boolean.</returns>
        public static bool LookupBoolean(ProtocolParams parameters,
                                         string         parameterName,
                                         bool           defaultValue)
        {
            if (parameters == null) {
                return defaultValue;
            }
            else if (parameterName == null) {
                throw new ArgumentNullException();
            }

            string sValue = parameters[parameterName];
            if (sValue == null) {
                return defaultValue;
            }

            try {
                return Boolean.Parse(sValue);
            }
            catch (FormatException) {
                Core.Log("Failed on parameter \"{0}\" value \"{1}\"\n",
                         parameterName, sValue);
                return defaultValue;
            }
        }
    }
}
