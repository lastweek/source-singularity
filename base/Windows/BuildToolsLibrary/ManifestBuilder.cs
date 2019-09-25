////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MetaDataParser.cs
//
//  TODO: fix comments in this file
//
//  Note:   This is a best-approximation of statically determinable metadata.
//          We can create a few general properties of an application, and we
//          can read the ConsoleCategory, Category, and DriverCategory attributes
//
using System;
using System.Collections;
using System.IO;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Text;
using System.Xml;
using Bartok.MSIL;

public class ManifestBuilder
{
    //
    // Note - This is a rather crude recursive descent parser
    //

    // This parser only deals in relatively flat xml, and as such we can use
    // a very straightforward parse methodology:
    //  for a class decorated with a tag that is in the "triggers" list
    //  - start a new xml tag
    //  - check every decoration on that class according to the classAttributes
    //    rules, and for each match add a child
    //  - check every field in the class according to the fieldAttributes
    //    rules, and for each match add a child
    private class ParseRules
    {
        public TriggerDefinition[] triggers;
        public ClassDefinition[] classAttributes;
        public FieldDefinition[] fieldAttributes;

        public ParseRules(ParseRules inheritFrom,
                          TriggerDefinition[] triggers,
                          ClassDefinition[] classAttributes,
                          FieldDefinition[] fieldAttributes)
        {
            this.triggers = triggers;

            if (inheritFrom != null) {
                this.classAttributes = Inherit(inheritFrom.classAttributes,
                                               classAttributes);
                this.fieldAttributes = Inherit(inheritFrom.fieldAttributes,
                                               fieldAttributes);
            }
            else {
                this.classAttributes = classAttributes;
                this.fieldAttributes = fieldAttributes;
            }
        }

        private static ClassDefinition[] Inherit(ClassDefinition[] root,
                                                 ClassDefinition[] grow)
        {
            ClassDefinition[] target = new ClassDefinition[root.Length + grow.Length];
            int j = 0;
            for (int i = 0; i < root.Length; i++, j++) {
                target[j] = root[i];
            }
            for (int i = 0; i < grow.Length; i++, j++) {
                target[j] = grow[i];
            }
            return target;
        }

        private static FieldDefinition[] Inherit(FieldDefinition[] root,
                                                 FieldDefinition[] grow)
        {
            FieldDefinition[] target = new FieldDefinition[root.Length + grow.Length];
            int j = 0;
            for (int i = 0; i < root.Length; i++, j++) {
                target[j] = root[i];
            }
            for (int i = 0; i < grow.Length; i++, j++) {
                target[j] = grow[i];
            }
            return target;
        }
    }

    // Construct the parsing tables.
    private static readonly ParseRules[] rules;

    static ManifestBuilder()
    {
        ParseRules categoryRules = new ParseRules(
            null,

            // "triggers"
            new TriggerDefinition[] {
                new TriggerDefinition("category",
                                      null,
                                      "Microsoft.Singularity.Configuration.CategoryAttribute",
                                      "Microsoft.Singularity.Configuration.CategoryDeclaration",
                                      new string [] {"name"}),
            },

            // "class" attributes
            new ClassDefinition[] {},

            // "field" attributes
            new FieldDefinition[] {
                // NB: the constructor fields on these are handled specially, unlike
                // everything else in this tool.  This is indicated by the "true"
                // value for the last parameter to the constructor

                // TODO: is this correct?  Should Endpoint declarations in
                // ConsoleCategories and Configuration be given names so that they are more
                // human-configurable?  Will an app ever declare multiple Endpoints of
                // the same type and require the kernel to user to patch those identical
                // endpoints to different (and conflicting) apps?  Could this problem be
                // addressed via stronger typing?

                new EndpointDefinition("endpoints",
                                       "extension",
                                       "Microsoft.Singularity.Configuration.ExtensionEndpointAttribute",
                                       "Microsoft.Singularity.Channels.TRef_2"
                                       + "<Microsoft.Singularity.Extending."
                                       + "ExtensionContract+Exp,Microsoft.Singularity"
                                       + ".Extending.ExtensionContract+Start>"),
                new ServiceEndpointDefinition("endpoints",
                                       "serviceProvider",
                                       "Microsoft.Singularity.Configuration.ServiceEndpointAttribute",
                                       "Microsoft.Singularity.Channels.TRef_2"
                                       + "<Microsoft.Singularity.Directory."
                                       + "ServiceProviderContract+Exp,Microsoft."
                                       + "Singularity.Directory.ServiceProviderContract"
                                       + "+Start>"),
                // TODO: - the inheritance on this is not correct
                new EndpointDefinition("endpoints",
                                       "endpoint",
                                       "Microsoft.Singularity.Configuration.EndpointAttribute",
                                       null),
                new EndpointDefinition("endpoints",
                                       "customEndpoint",
                                       "Microsoft.Singularity.Configuration.CustomEndpointAttribute",
                                       null),

                new EndpointDefinition("endpoints",
                                       "inputPipe",
                                       "Microsoft.Singularity.Configuration.InputEndpointAttribute",
                                       null,
                                       new string [] {"Kind"}),
                new EndpointDefinition("endpoints",
                                      "outputPipe",
                                      "Microsoft.Singularity.Configuration.OutputEndpointAttribute",
                                      null,
                                      new string [] {"Kind"}),
                new ParameterDefinition("StringParameters",
                                    "StringParameter",
                                    "Microsoft.Singularity.Configuration.StringParameterAttribute",
                                    "STRING",
                                    new string [] {"Name"}),
                new ParameterDefinition("LongParameters",
                                    "LongParameter",
                                    "Microsoft.Singularity.Configuration.LongParameterAttribute",
                                    "I8",
                                    new string [] {"Name"}),
                new ParameterDefinition("BoolParameters",
                                    "BoolParameter",
                                    "Microsoft.Singularity.Configuration.BoolParameterAttribute",
                                    "BOOLEAN",
                                    new string [] {"Name"}),
                new ParameterDefinition("StringArrayParameters",
                                    "StringArrayParameter",
                                    "Microsoft.Singularity.Configuration.StringArrayParameterAttribute",
                                    "SZARRAY",
                                    new string [] {"Name"}),
            }
            );

        ParseRules driverCategoryRules = new ParseRules(
            categoryRules, // inherit "class" and "field" rules from category.

            // "triggers"
            new TriggerDefinition[] {
                new TriggerDefinition("category",
                                      "driver",
                                      "Microsoft.Singularity.Io.DriverCategoryAttribute",
                                      "Microsoft.Singularity.Io.DriverCategoryDeclaration"),
            },

            // "class" attributes
            new ClassDefinition[] {
                new ClassDefinition("device",
                                    "Microsoft.Singularity.Io.SignatureAttribute",
                                    new string [] {"signature"}),
                new ClassDefinition("enumerates",
                                    "Microsoft.Singularity.Io.EnumeratesDeviceAttribute",
                                    new string [] {"signature"}),
            },

            // "field" attributes
            new FieldDefinition[] {
                new FieldDefinition("dynamicHardware",
                                    "ioPortRange",
                                    "Microsoft.Singularity.Io.IoPortRangeAttribute",
                                    "Microsoft.Singularity.Io.IoPortRange",
                                    new string [] {"id"},
                                    new string [] {"Default","baseAddress",
                                                   "Length","rangeLength",
                                                   "Shared", "shared"}),
                new FieldDefinition("fixedHardware",
                                    "ioPortRange",
                                    "Microsoft.Singularity.Io.IoFixedPortRangeAttribute",
                                    "Microsoft.Singularity.Io.IoPortRange",
                                    new string [] {"id"},
                                    new string [] {"Base","baseAddress",
                                                   "Length","rangeLength",
                                                   "Shared", "shared"},
                                    new string [] {"fixed", "true"}),
                new FieldDefinition("dynamicHardware",
                                    "ioIrqRange",
                                    "Microsoft.Singularity.Io.IoIrqRangeAttribute",
                                    "Microsoft.Singularity.Io.IoIrqRange",
                                    new string [] {"id"},
                                    new string [] {"Default","baseAddress",
                                                   "Length","rangeLength",
                                                   "Shared", "shared"},
                                    new string [] {"rangeLength", "1"}),
                new FieldDefinition("fixedHardware",
                                    "ioIrqRange",
                                    "Microsoft.Singularity.Io.IoFixedIrqRangeAttribute",
                                    "Microsoft.Singularity.Io.IoIrqRange",
                                    new string [] {"id"},
                                    new string [] {"Base","baseAddress",
                                                   "Length","rangeLength",
                                                   "Shared", "shared"},
                                    new string [] {"fixed", "true",
                                                   "rangeLength", "1"}),
                new FieldDefinition("dynamicHardware",
                                    "ioDmaRange",
                                    "Microsoft.Singularity.Io.IoDmaRangeAttribute",
                                    "Microsoft.Singularity.Io.IoDmaRange",
                                    new string [] {"id"},
                                    new string [] {"Default","baseAddress",
                                                   "Length","rangeLength",
                                                   "Shared", "shared"},
                                    new string [] {"rangeLength", "1"}),
                new FieldDefinition("dynamicHardware",
                                    "ioMemoryRange",
                                    "Microsoft.Singularity.Io.IoMemoryRangeAttribute",
                                    "Microsoft.Singularity.Io.IoMemoryRange",
                                    new string [] {"id"},
                                    new string [] {"Default","baseAddress",
                                                   "Length","rangeLength",
                                                   "Shared", "shared"}),
                new FieldDefinition("fixedHardware",
                                    "ioMemoryRange",
                                    "Microsoft.Singularity.Io.IoFixedMemoryRangeAttribute",
                                    "Microsoft.Singularity.Io.IoMemoryRange",
                                    new string [] {"id"},
                                    new string [] {"Base","baseAddress",
                                                   "Length","rangeLength",
                                                   "Shared", "shared",
                                                   "AddressBits", "addressBits",
                                                   "Alignment", "alignment"},
                                    new string [] {"fixed", "true"}),
            }
            );

        ParseRules consoleCategoryRules = new ParseRules(
            categoryRules, // inherit "class" and "field" rules from category.

            // "triggers"
            new TriggerDefinition[] {
                new TriggerDefinition("category",
                                      "console",
                                      "Microsoft.Singularity.Configuration.ConsoleCategoryAttribute",
                                      "Microsoft.Singularity.Configuration.ConsoleCategoryDeclaration"),
            },

            // "class" attributes
            new ClassDefinition[] {
            },

            // "field" attributes
            new FieldDefinition[] {
            }
            );

        rules = new ParseRules[3] {
            driverCategoryRules,
            categoryRules,
            consoleCategoryRules,
        };
    }

    //////////////////////////////////////////////////////////////////////////
    //

    // the base path of the file cache
    private String cache;
    // the list of assembly files
    private ArrayList assemblies;
    // The metadata resolver
    private MetaDataResolver resolver;
    // the output file
    private XmlDocument manifest;
    // the process node
    private XmlNode process;
    // the Bartok/code generation parameters.
    private XmlNode codegen;
    // the linker parameters.
    private XmlNode linker;

    private int warningCount;
    private int errorCount;

    public ManifestBuilder(String cache, ArrayList assemblies)
    {
        this.cache = cache.ToLower();
        this.assemblies = assemblies;

        // create a blank manifest without an <?xml> header:
        manifest = new XmlDocument();
    }

    // create a manifest for an app, without looking at any assemblies
    // this creates the stub manifest into which each assembly's info will
    // go
    public bool CreateNewManifest(string appname, string x86filename)
    {
        warningCount = 0;
        errorCount = 0;

        // Create this.resolver using this.assemblyfilename
        InitializeResolver();

        // Create the basic XML tree.
        XmlNode application = AddElement(manifest, "application");
        AddAttribute(application, "name", appname);

        process = AddElement(application, "process");
        AddAttribute(process, "id", "0");
        AddAttribute(process, "main", "true");
        AddAttribute(process, "path", StripPathFromPath(x86filename));
        AddAttribute(process, "cache", StripCacheFromPath(x86filename));

        bool seenPublisher = false;
        XmlNode privileges = null;
        // here we assume that the first assembly is the app assembly
        // extract the publisher name from there
        MetaData md0 = (MetaData)resolver.MetaDataList[0];
        MetaDataAssembly mda0 = (MetaDataAssembly)md0.Assemblies[0];
        if (mda0.CustomAttributes != null) {
            foreach (MetaDataCustomAttribute ca in mda0.CustomAttributes) {
                if (ca.Name == "Microsoft.Singularity.Security.ApplicationPublisherAttribute") {
                    if (!seenPublisher && ca.FixedArgs != null && ca.FixedArgs[0] != null) {
                        AddAttribute(application, "publisher", (string)ca.FixedArgs[0]);
                        seenPublisher = true;
                    }
                }
                else if (ca.Name == "Microsoft.Singularity.Security.AssertPrivilegeAttribute") {
                    if (ca.FixedArgs != null && ca.FixedArgs[0] != null) {
                        if (privileges == null)
                            privileges = AddElement(application, "privileges");
                        XmlNode privilege = AddElement(privileges, "privilege");
                        AddAttribute(privilege, "name", (string)ca.FixedArgs[0]);
                    }
                }
            }
        }

        // Create the list of assemblies.
        XmlNode assemblies = AddElement(process, "assemblies");
        foreach (MetaData md in resolver.MetaDataList) {
            MetaDataAssembly mda = (MetaDataAssembly)md.Assemblies[0];

            string file = md.Name;
            string assemblyname = StripPathFromPath(file);

            XmlNode assembly = AddElement(assemblies, "assembly");
            AddAttribute(assembly, "name", assemblyname);
            if (mda.MajorVersion != 0 || mda.MinorVersion != 0 ||
                mda.BuildNumber != 0 || mda.RevisionNumber != 0) {
                AddAttribute(assembly, "version", String.Format("{0}.{1}.{2}.{3}",
                                                                mda.MajorVersion,
                                                                mda.MinorVersion,
                                                                mda.BuildNumber,
                                                                mda.RevisionNumber));
            }
            if (mda.PublicKey != null & mda.PublicKey.Length > 0) {
                AddAttribute(assembly, "publickey",
                             String.Format("{0}", KeyToString(mda.PublicKey)));
            }
            if (mda.Locale != null && mda.Locale != "") {
                AddAttribute(assembly, "locale", mda.Locale);
            }
            AddAttribute(assembly, "cache", StripCacheFromPath(file));
        }

        // Create a placeholder for

        // now go through every class in the assembly to locate ConsoleCategory,
        // Category, and DriverCategory attributes
        int categoryIndex = 0;
        XmlNode categories = null;
        foreach (MetaData md in resolver.MetaDataList) {
            // NB: md.TypeDefs is a flat list of all classes in this assembly,
            //     regardless of nesting
            foreach (MetaDataTypeDefinition type in md.TypeDefs) {
                for (int i = 0; i < rules.Length; i++) {
                    if (ProcessType(type, rules[i], process, ref categoryIndex, ref categories)) {
                        break;
                    }
                }
            }
        }

        if (errorCount != 0) {
            return false;
        }
        return true;
    }

    public bool AddCodegenParameter(string param)
    {
        if (codegen == null) {
            codegen = AddElement(process, "codegen");
        }
        XmlNode node = AddElement(codegen, "parameter");
        AddAttribute(node, "value", param);
        return true;
    }

    public bool AddLinkerParameter(string param)
    {
        if (linker == null) {
            linker = AddElement(process, "linker");
        }
        XmlNode node = AddElement(linker, "parameter");
        AddAttribute(node, "value", param);
        return true;
    }

    public void Save(XmlTextWriter writer)
    {
        manifest.Save(writer);
    }

    ///////////////////////////////////////////// Methods to help with errors.
    //
    private static string LastName(string value)
    {
        if (value != null) {
            int period = value.LastIndexOf('.');

            if (period > 0 && period < value.Length) {
                return value.Substring(period + 1);
            }
        }
        return value;
    }

    public void Error(string message, params object[] args)
    {
        Console.Write("mkmani: Error: ");
        Console.WriteLine(message, args);
        errorCount++;
    }

    private void Warning(string message, params object[] args)
    {
        Console.Write("mkmani: Warning: ");
        Console.WriteLine(message, args);
        warningCount++;
    }

    //////////////////////////////////////////////// Methods to help with XML.
    //
    private XmlNode AddElement(XmlNode parent, string name)
    {
        XmlNode element = manifest.CreateNode(XmlNodeType.Element, name, "");
        if (parent != null) {
            parent.AppendChild(element);
        }
        return element;
    }

    public void AddAttribute(XmlNode node, string name, string value)
    {
        XmlAttribute attr = manifest.CreateAttribute(name);
        attr.Value = value;
        node.Attributes.Append(attr);
    }

    // this method creates a MetaData resolver and loads all the assemblies into
    // it
    private void InitializeResolver()
    {
        resolver = new MetaDataResolver(assemblies, new ArrayList(), new DateTime(),
                                        false, false);

        MetaDataResolver.ResolveCustomAttributes(
            new MetaDataResolver[] {resolver});
    }

    // parse utility function to ensure that a type's inheritance matches the
    // inheritance specified in the TokenDefinition
    public bool MatchInheritance(string derivesFromClass,
                                 MetaDataTypeDefinition type)
    {
        //Console.WriteLine("derives=({0}), type = {1}",
        //    derivesFromClass,
        //    type.Extends == null ? null: ((MetaDataTypeReference)type.Extends).FullName);
//
//      if (derivesFromClass != null) {
//          if (type.Extends == null ||
//              ((MetaDataTypeReference)type.Extends).FullName !=
//              derivesFromClass) {
//              return false;
//          }
//      }
//
      return true;
    }

    // parse utility function to ensure that the class of a field matches the
    // class name specified in a TokenDefinition
    public bool MatchFieldType(FieldDefinition rule,
                               MetaDataField field)
    {
        if (rule.matchClassType != null) {
            MetaDataObject classobj = field.Signature.FieldType.ClassObject;
            string classtype = "";

            // Since we can pass in different objects as field, we need to be
            // careful here about how we get the class type
            if (classobj is MetaDataTypeDefinition) {
                classtype = ((MetaDataTypeDefinition) classobj).FullName;
            }
            else if (classobj is MetaDataTypeReference) {
                classtype = ((MetaDataTypeReference) classobj).FullName;
            }
            else if (classobj == null) {
                classtype = field.Signature.FieldType.ElementType.ToString();
            }

            if (classtype != rule.matchClassType) {
                Error("{0} can't be applied to {1}",
                      LastName(rule.attribute), field.FullName);
                Error("{0}does not match {1}",
                      classtype, rule.matchClassType);
                return false;
            }
        }
        return true;
    }

    // This is the only way we create XML tags (except for Endpoints)
    public XmlNode CreateNode(MetaDataCustomAttribute data,
                              TokenDefinition rule)
    {
        XmlNode node = AddElement(null, rule.xmlTagName);

        // make an attribute for each constructor argument
        if (data.FixedArgs.Length != 0) {
            for (int i = 0; i < data.FixedArgs.Length; i++) {
                string name = rule.constructorFields[i];
                if (data.FixedArgs[i] == null) {
                    AddAttribute(node, name, "");
                }
                else {
                    string value = data.FixedArgs[i].ToString();
                    AddAttribute(node, name, value);
                }
            }
        }

        // make an attribute for each constructor-time property
        for (int i = 0; i < data.NamedArgs.Length; i++) {
            string name = rule.FindPropertyReplacement(data.NamedArgs[i].Name);
            object arg = data.NamedArgs[i].Value;
            string value;
            if (arg == null) {
                // REVIEW: do we want "" or null here?
                value = null;
            }
            else {
                value = data.NamedArgs[i].Value.ToString();
                if (arg is System.UInt32) {
                    // We output unsigned types as 0x because they are generally
                    // hardware-related numbers which are documented in hexadecimal.
                    value = String.Format("0x{0:x}", arg);
                }
            }
            AddAttribute(node, name, value);
        }

        // make an attribute for each default field
        for (int i = 0; i < rule.defaultFields.Length; i += 2) {
            string name = rule.defaultFields[i];
            AddAttribute(node, name, rule.defaultFields[i+1]);
        }
        return node;
    }

    private XmlNode GetEndpointHierarchy(string nodeName, string endpointType)
    {
        XmlNode node = AddElement(null, nodeName);
        MetaDataTypeDefinition epType = resolver.ResolveName(endpointType);

        XmlNode oldChild = null;
        XmlNode newChild = null;

        while (epType.FullName != "Microsoft.Singularity.Channels.Endpoint") {
            newChild = manifest.CreateNode(XmlNodeType.Element, "inherit", "");

            AddAttribute(newChild, "name", epType.FullName);

            if (oldChild == null) {
                node.AppendChild(newChild);
            }
            else {
                node.InsertBefore(newChild, oldChild);
            }
            oldChild = newChild;

            string nextName;
            if (epType.Extends is MetaDataTypeReference) {
                nextName = ((MetaDataTypeReference) epType.Extends).FullName;
                if (nextName == "Exp" || nextName == "Imp") {
                    MetaDataTypeReference mdtr =
                        (MetaDataTypeReference) epType.Extends;
                    nextName =
                        ((MetaDataTypeReference)mdtr.ResolutionScope).FullName
                        + "." + nextName;
                }

            }
            else if (epType.Extends is MetaDataTypeDefinition) {
                nextName = ((MetaDataTypeDefinition) epType.Extends).FullName;
            }
            else {
                return node;
            }

            epType = resolver.ResolveName(nextName);
        }

        newChild = manifest.CreateNode(XmlNodeType.Element, "inherit", "");
        AddAttribute(newChild, "name", epType.FullName);

        if (oldChild == null) {
            node.AppendChild(newChild);
        }
        else {
            node.InsertBefore(newChild, oldChild);
            oldChild = newChild;
        }

        return node;
    }


    public XmlNode CreateNodeIndexed(MetaDataCustomAttribute data,
                              TokenDefinition rule,
                              int index
                              )
    {
        XmlNode node = CreateNode(data, rule);
        AddAttribute(node, "id", index.ToString());
        return node;
    }

    // Endpoints are special in a lot of ways, and require a special method
    public XmlNode CreateEndpointNode(MetaDataCustomAttribute data,
                                      EndpointDefinition rule,
                                      int index)
    {
        // assume that the constructor to an endpoint always takes one argument,
        // and that the argument looks like this:
        // "<discard*> contractname+Exp*,AssemblyName, Version=foo,
        //  Culture=bar, PublicKeyToken=fbar"

        // we'll parse this to get all the attributes of the top-level tag, and
        // then parse field that is being decorated to get the rest of the
        // information we need.

        // get the type of the field that is decorated:
        MetaDataObject t = (MetaDataObject)
            ((MetaDataField)data.Parent).Signature.FieldType.ClassObject;

        // split the field to get the parts we need
        string typeName = t.FullName;
        typeName = typeName.Replace("<", ",");
        typeName = typeName.Replace(">", "");
        typeName = typeName.Replace("+", ",");

        string [] nameParts = typeName.Split(',');

        string contractName = nameParts[1];
        string impName = contractName + ".Imp";
        string expName = contractName + ".Exp";
        string stateName = contractName + "." + nameParts[4];


        XmlNode impNode = GetEndpointHierarchy("imp", impName);
        XmlNode expNode = GetEndpointHierarchy("exp", expName);

        MetaDataTypeDefinition r1 = resolver.ResolveName(impName);
        MetaDataTypeDefinition r2 = resolver.ResolveName(expName);
        MetaDataTypeDefinition r3 = resolver.ResolveName(stateName);

        string startState = "";
        for (int i = 0; i < r3.Fields.Length; i++) {
            if (r3.Fields[i].Name == "Value") {
                startState = r3.Fields[0].DefaultValue.ToString();
                break;
            }
        }

        XmlNode node = manifest.CreateNode(XmlNodeType.Element,
                                           rule.xmlTagName, "");

        node.AppendChild(impNode);
        node.AppendChild(expNode);
        AddAttribute(node, "id", index.ToString());
        if (startState != "") {
            AddAttribute(node, "startStateId", startState);
        }

        // Contract name comes from either the attribute argument
        // or the TRef type depending on the endpoint kind
        rule.AddContractNameAttribute(this, node, data, contractName);

        // add an attribute for each constructor argument if there is one
        // This should only be true for input/ouput pipes
        if (rule.constructorFields != null && rule.constructorFields.Length != 0) {
            if (data.FixedArgs.Length != 0) {
                for (int i = 0; i < data.FixedArgs.Length; i++) {
                    if (rule.constructorFields[i] != null) {
                        string name = rule.constructorFields[i];
                        if (data.FixedArgs[i] == null) {
                            AddAttribute(node, name, "");
                        }
                        else {
                            string value = data.FixedArgs[i].ToString();
                            AddAttribute(node, name, value);
                        }
                    }
                    else {
                        Console.WriteLine(" fixed=({0}), no matching constructor?",
                            data.FixedArgs[i] == null? null : data.FixedArgs[i].ToString() );
                    }
                }
            }
        }

        return node;
    }

    // this does the processing of each field-level decoration on a type,
    // according to rules.fieldAttributes
    private void ProcessFieldAttributes(MetaDataTypeDefinition type,
                                        FieldDefinition[] rules,
                                        XmlNode parent)
    {
        int endpointIndex = 0;
        int intParameterIndex = 0;
        int stringParameterIndex = 0;
        int stringArrayParameterIndex = 0;
        int boolParameterIndex = 0;
        foreach (MetaDataField field in type.Fields) {
            if (field.CustomAttributes == null) {
                continue;
            }

            foreach (MetaDataCustomAttribute attrib in field.CustomAttributes) {
                foreach (FieldDefinition rule in rules) {
                    if (attrib.Name == rule.attribute) {

                        // type check it
                        if (MatchFieldType(rule, field)) {
                            // custom step if Endpoint:
                            XmlNode node;

                            EndpointDefinition edrule = rule as EndpointDefinition;
                            if (edrule != null) {
                                node = CreateEndpointNode(attrib, edrule, endpointIndex++);
                            }
                            else if (rule is ParameterDefinition) {
                                int index;
                                if (rule.matchClassType == "I8") {
                                    index = intParameterIndex++;
                                }
                                else if (rule.matchClassType == "STRING") {
                                    index = stringParameterIndex++;
                                }
                                else if (rule.matchClassType == "BOOLEAN") {
                                    index = boolParameterIndex++;
                                }
                                else if (rule.matchClassType == "SZARRAY") {
                                    index = stringArrayParameterIndex++;
                                }
                                else {
                                    index =999;
                                }
                                node = CreateNodeIndexed(attrib, rule, index);
                            }
                            else {
                                node = CreateNode(attrib, rule);
                            }

                            if (node != null) {
                                XmlNode group = parent[rule.xmlGroup];
                                if (group == null) {
                                    group = AddElement(parent, rule.xmlGroup);
                                }
                                group.AppendChild(node);
                            }
                        }
                    }
                }
            }
        }
    }

    // this does the processing of each class-level decoration on a type, as
    // described in rules.classAttributes
    private void ProcessClassAttributes(MetaDataTypeDefinition type,
                                        ClassDefinition[] rules,
                                        XmlNode parent)
    {
        if (type.CustomAttributes == null) {
            return;
        }

        foreach (MetaDataCustomAttribute attrib in type.CustomAttributes) {
            foreach (ClassDefinition rule in rules) {
                if (attrib.Name == rule.attribute) {
                    XmlNode node = CreateNode(attrib, rule);
                    parent.AppendChild(node);
                }
            }
        }
    }

    // this kicks off the processing of a type; see if it is decorated by
    // rules.triggers, and if so, then build an xml node and process the rest
    // of the rules object for this type
    private bool ProcessType(MetaDataTypeDefinition type,
                             ParseRules rules,
                             XmlNode parent,
                             ref int categoryIndex,
                             ref XmlNode categories)
    {
        if (type.CustomAttributes == null) {
            return false;
        }


        foreach (MetaDataCustomAttribute attrib in type.CustomAttributes) {
            foreach (TriggerDefinition rule in rules.triggers) {
                if (attrib.Name == rule.attribute) {
                    // only process this entry if the ancestry is valid
                    if (MatchInheritance(rule.derivesFromClass, type)) {
                        if (categoryIndex == 0) {
                            categories = AddElement(parent,"categories");
                        }
                        // create an xml node from (attrib, rule)
                        XmlNode node = CreateNode(attrib, rule);

                        AddAttribute(node, "id", (categoryIndex++).ToString());
                        if (rule.categoryName != null) {
                            AddAttribute(node, "name", rule.categoryName);
                        }
                        AddAttribute(node, "class", type.FullName);

                        // then do the rules.classDefinitions work
                        ProcessClassAttributes(type, rules.classAttributes, node);

                        // then do the rules.fieldDefinitions work
                        ProcessFieldAttributes(type, rules.fieldAttributes, node);

                        // then append this xml node to the manifest root doc
                        if (categories == null) {
                            Console.WriteLine(" categories is null at index {0}",categoryIndex);
                        }
                        else {
                            categories.AppendChild(node);
                        }
                        // once we match once, we stop operating on this type
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private String KeyToString(byte[] key)
    {
        StringBuilder sb = new StringBuilder("");
        int count = key.Length;
        if (count > 0) {
            for (int i = 0; i < count; i++) {
                sb.Append(key[i].ToString("x2"));
            }
        }
        return sb.ToString();
    }

    private String StripPathFromPath(string path)
    {
        int index = Math.Max(path.LastIndexOf(':'),
                             Math.Max(path.LastIndexOf('\\'),
                                      path.LastIndexOf('/')));
        if (index >= 0) {
            return path.Substring(index + 1);
        }
        return path;
    }

    private String StripCacheFromPath(string path)
    {
        if (cache != null && path.ToLower().StartsWith(cache)) {
            return path.Substring(cache.Length).Replace('\\', '/');
        }
        return path.Replace('\\', '/');
    }

    // augment a manifest based on the assembly given.  This touches:
    // <assemblies>, <ConsoleCategory>, <category>, and <drivercategory>
    private void ParseAssemblies(XmlNode assemblies)
    {
    }

}
