// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  AttributeUsageAttribute
//
// Purpose: The class denotes how to specify the usage of an attribute
//
//===========================================================  
namespace System
{

    using System.Reflection;
    // By default, attributes are inherited and multiple attributes are not allowed   
    //| <include path='docs/doc[@for="AttributeUsageAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Class, Inherited = true)]
    public sealed class AttributeUsageAttribute : Attribute
    {
        internal AttributeTargets m_attributeTarget = AttributeTargets.All; // Defaults to all
        internal bool m_allowMultiple = false; // Defaults to false
        internal bool m_inherited = true; // Defaults to true

        internal static AttributeUsageAttribute Default = new AttributeUsageAttribute(AttributeTargets.All);

       //Constructors
        //| <include path='docs/doc[@for="AttributeUsageAttribute.AttributeUsageAttribute"]/*' />
        public AttributeUsageAttribute(AttributeTargets validOn) {
            m_attributeTarget = validOn;
        }


       //Properties
        //| <include path='docs/doc[@for="AttributeUsageAttribute.ValidOn"]/*' />
        public AttributeTargets ValidOn
        {
           get{ return m_attributeTarget; }
        }

        //| <include path='docs/doc[@for="AttributeUsageAttribute.AllowMultiple"]/*' />
        public bool AllowMultiple
        {
            get { return m_allowMultiple; }
            set { m_allowMultiple = value; }
        }

        //| <include path='docs/doc[@for="AttributeUsageAttribute.Inherited"]/*' />
        public bool Inherited
        {
            get { return m_inherited; }
            set { m_inherited = value; }
        }
    }
}
