using System;

///
/// general classes used in transforms
///

namespace Microsoft.Singularity.Transform
{
    /// flags classes & methods used as patterns
    public class PatternAttribute : Attribute
    {
    }

    /// flags classes used as templates for generating new code
    public class TemplateAttribute : Attribute
    {
    }
  
    /// flags parameters used as alternate type matches
    public class CaseAttribute : Attribute
    {
    }

    /// flags final parameter of case list
    public class DefaultAttribute : Attribute
    {
    }

    /// flags parameters used as type matches
    public class ParameterAttribute : Attribute
    {
    }

    /// flags parameters that match any data type (array, scalar, struct)
    public class DataAttribute : Attribute
    {
    }

    /// flags where transformed class references are expected to be defined
    public class DefinedAttribute : Attribute
    {
        public DefinedAttribute(string s)
        {
        }
    }

    /// used to invoke processing instructions inside code
    public class Transform
    {
        /// begin an iteration block
        public static void For(string x)
        {
        }
        /// end an iteration block
        /// todo: rename to EndFor()
        public static void EndFor()
        {
        }
        /// switch on type of a parameter
        public static void Switch(string x)
        {
        }
        /// conditionally generate if types match
        public static void Case(string x)
        {
        }
        /// last case if not present
        public static void Default()
        {
        }
        /// end conditional block
        public static void EndSwitch()
        {
        }
        /// flag compile time error
        public static void Error(string x)
        {
        }
        /// compile if strings are equal
        public static void IfEqual(string a, string b)
        {
        }
        /// compile if strings are not equal
        public static void IfNotEqual(string a, string b)
        {
        }
        /// end if block
        public static void EndIf()
        {
        }
    }
}

