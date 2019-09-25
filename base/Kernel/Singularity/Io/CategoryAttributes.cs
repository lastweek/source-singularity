///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   CategoryAttributes.cs
//
//  Warning:  This file is compiled into the kernel, and into the runtime.
//            In order to get the visibility correct in all cases, some #ifs
//            are needed
//
//  New Design:
//          This now conforms with the ideas presented in the Genesis papers,
//          chapter 3.  In particular, a device driver is simply a Category,
//          and anything that is in an app manifest is either intrinsic to
//          apps/installations (and hence not a decoration), or else a
//          PropertySet or Category.

using System;

namespace Microsoft.Singularity.Configuration
{
    //
    // The master Category declaration
    //
    // Configuration are optional.  If none are specified, then the app should
    // be thought of as only having one (default) Category.
    //
    // A class that declares a Category must descend from this class
    //
    public class CategoryDeclaration
    {

    }

    //////////////////////////////////////////////////////////////////////////
    //
    // CategoryAttribute
    //
    // Purpose: Decorates a class derived from CategoryDeclaration to
    //          indicate that the metadata parser should declare a category
    //          from the fields in this class
    //
    // Usage:   Must decorate a class derived from CategoryDeclaration
    //
    [AttributeUsage(AttributeTargets.Class, AllowMultiple = false)]
    public class CategoryAttribute : System.Attribute
    {
        // <<name>> is the name for this category, to distinguish between
        // multiple categories in the manifest
        private string name;

        public CategoryAttribute(string name)
        {
            this.name = name;
        }

    }

    //
    //  The Console Category
    //

    // Console apps  are apps that run in a special Category.  We will designate this
    // by deriving a new class from CategoryDeclaration to represent this
    // special Category, and then creating special field annotations that only
    // apply to this Category.
    //
    public abstract class ConsoleCategoryDeclaration : CategoryDeclaration
    {
        internal abstract int AppMain();
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // ConsoleCategoryAttribute
    //
    // Purpose: Top-level metadata indicating that an assembly implements the
    //          Console Category
    //
    // Usage:   Must be applied to a class derived from
    //          ConsoleCategoryDeclaration
    //
    [AttributeUsage(AttributeTargets.Class, AllowMultiple = false)]
    public class ConsoleCategoryAttribute : System.Attribute
    {
        public ConsoleCategoryAttribute()
        {

        }
        private string action;
        private string helpMessage;
        private bool defaultAction;

        public string HelpMessage
        {
            get  {return helpMessage;}
            set  {helpMessage = value;}
        }

        public string Action
        {
            get  {return action;}
            set  {action  = value;}
        }

        public bool DefaultAction
        {
            get  {return defaultAction;}
            set  {defaultAction  = value;}
        }
}


    //////////////////////////////////////////////////////////////////////////
    //
    // InputEndpointAttribute
    //
    // Purpose: Console Input Unicode Pipe declaration
    //          kinds are "data" and "control".  Control is used for a 2nd
    //          input pipe such as in More and replaces the "keyboard"
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public class InputEndpointAttribute : EndpointAttribute {
        private string kind;

        public InputEndpointAttribute(string kind) {
            this.kind = kind;
        }

        public string Kind {
            get {return kind;}
            set {kind = value;}
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // OutputEndpointAttribute
    //
    // Purpose: Console Input Unicode Pipe declaration
    //          kinds are "data" and "control".  Control is used for a 2nd
    //          input pipe such as in More and replaces the "keyboard"
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public class OutputEndpointAttribute : EndpointAttribute {
        private string kind;

        public OutputEndpointAttribute(string kind) {
            this.kind = kind;
        }

        public string Kind {
            get {return kind;}
            set {kind = value;}
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // EndpointAttribute
    //
    // Purpose: Any non-ServiceProvider that is a requirement ought to be
    //          declared with this attribute.  This will tell CTR to pre-bind
    //          the endpoint and will tell the config the type of the channel
    //          so that names can be resolved without the assembly declaring
    //          them
    //
    // Usage:   Decorates a field within a class decorated with
    //          [DriverCategory].  The field should be an endpoint.
    //
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public class EndpointAttribute : System.Attribute {
        public string bindPath;

        public EndpointAttribute() {
        }

        public string Path {
            get {return bindPath;}
            set {bindPath = value;}
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // CustomEndpointAttribute
    //
    // Purpose: Any endpoint that an app does not want the Binder.LoadManifest
    //          to fill in should be declared with this attribute.
    //          This will tell CTR to pre-bind
    //          the endpoint and will tell the config the type of the channel
    //          so that names can be resolved without the assembly declaring
    //          them
    //
    // Usage:   Decorates a field within a class decorated with
    //          [DriverCategory].  The field should be an endpoint.
    //
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public class CustomEndpointAttribute : EndpointAttribute
    {

        public CustomEndpointAttribute() {
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // ExtensionEndpointAttribute
    //
    // Purpose: Decorate an extension endpoint and indicate that CTR should bind
    //          the endpoint before client code is invoked.
    //
    // Usage:   Decorates an ExtensionEndpoint field within a class
    //          decorated with [DriverCategory]
    //
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public class ExtensionEndpointAttribute : EndpointAttribute
    {
        public ExtensionEndpointAttribute()
        {
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // ServiceEndpointAttribute
    //
    // Purpose: Decorate a ServiceProvider endpoint.  This indicates that the
    //          endpoint will be pre-bound, so that the kernel can determine
    //          names and drivers cannot.  The parameter indicates the type of
    //          channel that is created (second order) from this
    //          ServiceProvider.
    //
    // Usage:   Decorates a ServiceProvider field within a class decorated
    //          with [DriverCategory]
    //
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public class ServiceEndpointAttribute : EndpointAttribute
    {
        // <<serviceContractType>> is a required parameter.  It gives the type
        // of the contract that is served over this ServiceProvider
        // The Exp is implicit, that is, we can just specify the contract type
        //
        private System.Type serviceContractType;
        //private string bindPath;

        public ServiceEndpointAttribute(System.Type epType)
        {
            serviceContractType = epType;
        }

       // public string Path
       // {
       //     get {return bindPath;}
       //     set {bindPath = value;}
       // }

#if SINGULARITY_KERNEL
        // <<customname>> is a kernel-only hack to let the Hal console set a
        // special name for itself.
        private string customName;

        public string CustomName
        {
            get { return customName; }
            set { customName = value; }
        }
#endif
    }

    //////////////////////////////////////////////////////////////////////////
    ///
    /// Parameter Attributes
    ///
    //////////////////////////////////////////////////////////////////////////


    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public sealed class StringParameterAttribute : ParameterAttribute
    {
        private string defaultValue;

        //[NotDelayed]
        public StringParameterAttribute(string ArgumentName)
                :base(ArgumentName)
        {
        }
        public string Default
        {
            get { return defaultValue; }
            set { defaultValue = value; }
        }
    }

    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public sealed class StringArrayParameterAttribute : ParameterAttribute
    {
        private string[] defaultValue;

        //[NotDelayed]
        public StringArrayParameterAttribute(string ArgumentName)
                :base(ArgumentName)
        {
        }
        public string[] Default
        {
            get { return defaultValue; }
            set { defaultValue = value; }
        }
    }

    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public sealed class LongParameterAttribute : ParameterAttribute
    {
        private long defaultValue;

        public LongParameterAttribute(string ArgumentName)
                :base(ArgumentName)
        {
            defaultValue = -1;
            Position = -1;
        }

        public long Default
        {
            get { return defaultValue; }
            set { defaultValue = value; }
        }
}

    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public sealed class BoolParameterAttribute : ParameterAttribute
    {
        private bool    defaultValue;

        public BoolParameterAttribute(string name)
                :base(name)
        {
            defaultValue = false;
            Position = -1;
        }

        public bool Default
        {
            get { return defaultValue; }
            set { defaultValue = value; }
        }
    }


    [AttributeUsage(AttributeTargets.Field, AllowMultiple = true)]
    public class ParameterAttribute : System.Attribute
    {
        private int     position;
        private string  helpMessage;
        private bool    mandatory;
        private string  name;

        public ParameterAttribute(string Name)
        {
            this.name = Name;
        }

        public bool Mandatory
        {
            get { return mandatory; }
            set { mandatory = value; }
        }

        public string Name
        {
            get { return name; }
            set { name = value; }
        }

        public int Position
        {
            get { return position; }
            set { position = value; }
        }

        public string HelpMessage
        {
            get { return helpMessage; }
            set { helpMessage = value; }
        }
    }
}
