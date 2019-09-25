////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TokenDefinition.cs
//
//  Note:   Declares a class describing MetaData tokens, so that the
//          metadata parser's consts can all be easily identified.
using System;
using System.Diagnostics;
using System.Xml;
using Bartok.MSIL;

public class TokenDefinition
{
    // name of the metadata attribute to match
    public readonly string attribute;

    // name of the xml tag to output
    public readonly string xmlTagName;

    // labels for constructor fields during output
    public readonly string [] constructorFields;

    // labels for properties to be renamed during output
    // each property uses two addresses [default, new name]
    public readonly string [] propertyReplacements;

    // fields to be added with default values, if not named
    public readonly string [] defaultFields;

    // basic constructor; everything is public, but now it's all very easy to
    // keep track of.
    public TokenDefinition(string xmlTagName,
                           string attribute,
                           string [] constructorFields,
                           string [] propertyReplacements,
                           string [] defaultFields)
    {
        this.xmlTagName = xmlTagName;
        this.attribute = attribute;
        this.constructorFields = constructorFields;
        if (propertyReplacements != null && (propertyReplacements.Length % 2) != 0) {
            Console.WriteLine("{0} has bad propertyReplacements", xmlTagName);
        }
        this.propertyReplacements = propertyReplacements;
        if (defaultFields != null && (defaultFields.Length % 2) != 0) {
            Console.WriteLine("{0} has bad defaultFields", xmlTagName);
        }
        this.defaultFields = defaultFields;
    }

    public TokenDefinition(string xmlTagName,
                           string attribute,
                           string [] constructorFields,
                           string [] propertyReplacements)
        : this(xmlTagName, attribute, constructorFields, propertyReplacements, new string[0])
    {
    }

    public TokenDefinition(string xmlTagName,
                           string attribute,
                           string [] constructorFields)
        : this(xmlTagName, attribute, constructorFields, new string[0], new string[0])
    {
    }

    public TokenDefinition(string xmlTagName,
                           string attribute)
        : this(xmlTagName, attribute, new string[0], new string[0], new string[0])
    {
    }

    public string FindPropertyReplacement(string name)
    {
        if (propertyReplacements != null) {
            for (int pair = 0; pair < propertyReplacements.Length; pair += 2) {
                if (propertyReplacements[pair] == name) {
                    return propertyReplacements[pair + 1];
                }
            }
        }
        return name;
    }
}

public class TriggerDefinition : TokenDefinition
{
    // name of the category
    public readonly string categoryName;

    // name of the class that the decorated class must directly inherit from
    public readonly string derivesFromClass;

    public TriggerDefinition(string xmlTagName,
                             string categoryName,
                             string attribute,
                             string derivesFromClass,
                             string [] constructorFields,
                             string [] propertyReplacements,
                             string [] defaultFields)
        : base(xmlTagName,
               attribute,
               constructorFields,
               propertyReplacements,
               defaultFields)
    {
        this.derivesFromClass = derivesFromClass;
        this.categoryName = categoryName;
    }

    public TriggerDefinition(string xmlTagName,
                             string categoryName,
                             string attribute,
                             string derivesFromClass,
                             string [] constructorFields,
                             string [] propertyReplacements)
        : base(xmlTagName, attribute, constructorFields, propertyReplacements, new string[0])
    {
        this.derivesFromClass = derivesFromClass;
        this.categoryName = categoryName;
    }

    public TriggerDefinition(string xmlTagName,
                             string categoryName,
                             string attribute,
                             string derivesFromClass,
                             string [] constructorFields)
        : base(xmlTagName, attribute, constructorFields, new string[0], new string[0])
    {
        this.derivesFromClass = derivesFromClass;
        this.categoryName = categoryName;
    }

    public TriggerDefinition(string xmlTagName,
                             string categoryName,
                             string attribute,
                             string derivesFromClass)
        : base(xmlTagName, attribute, new string[0], new string[0], new string[0])
    {
        this.derivesFromClass = derivesFromClass;
        this.categoryName = categoryName;
    }
}

public class ClassDefinition : TokenDefinition
{
    public ClassDefinition(string xmlTagName,
                           string attribute,
                           string [] constructorFields,
                           string [] propertyReplacements,
                           string [] defaultFields)
        : base(xmlTagName,
               attribute,
               constructorFields,
               propertyReplacements,
               defaultFields)
    {
    }

    public ClassDefinition(string xmlTagName,
                           string attribute,
                           string [] constructorFields,
                           string [] propertyReplacements)
        : base(xmlTagName, attribute, constructorFields, propertyReplacements, new string[0])
    {
    }

    public ClassDefinition(string xmlTagName,
                           string attribute,
                           string [] constructorFields)
        : base(xmlTagName, attribute, constructorFields, new string[0], new string[0])
    {
    }

    public ClassDefinition(string xmlTagName,
                           string attribute)
        : base(xmlTagName, attribute, new string[0], new string[0], new string[0])
    {
    }
}

public class ParameterDefinition : FieldDefinition
{
    public ParameterDefinition(string xmlGroup,
                           string xmlTagName,
                           string attribute,
                           string matchClassType,
                           string [] constructorFields)
        : base(xmlGroup,
               xmlTagName,
               attribute,
               matchClassType,
               constructorFields)
        {
        }
    
}
public class FieldDefinition : TokenDefinition
{
    // name of the group to put the field into.
    public readonly string xmlGroup;

    // name of the class that the decorated class must be (fields only)
    public readonly string matchClassType;

    public FieldDefinition(string xmlGroup,
                           string xmlTagName,
                           string attribute,
                           string matchClassType,
                           string [] constructorFields,
                           string [] propertyReplacements,
                           string [] defaultFields)
        : base(xmlTagName,
               attribute,
               constructorFields,
               propertyReplacements,
               defaultFields)
    {
        this.xmlGroup = xmlGroup;
        this.matchClassType = matchClassType;
    }

    public FieldDefinition(string xmlGroup,
                           string xmlTagName,
                           string attribute,
                           string matchClassType,
                           string [] constructorFields,
                           string [] propertyReplacements)
        : base(xmlTagName,
               attribute,
               constructorFields,
               propertyReplacements,
               new string[0])
    {
        this.xmlGroup = xmlGroup;
        this.matchClassType = matchClassType;
    }

    public FieldDefinition(string xmlGroup,
                           string xmlTagName,
                           string attribute,
                           string matchClassType,
                           string [] constructorFields)
        : base(xmlTagName,
               attribute,
               constructorFields,
               new string[0],
               new string[0])
    {
        this.xmlGroup = xmlGroup;
        this.matchClassType = matchClassType;
    }

    public FieldDefinition(string xmlGroup,
                           string xmlTagName,
                           string attribute,
                           string matchClassType)
        : base(xmlTagName,
               attribute,
               new string[0],
               new string[0],
               new string[0])
    {
        this.xmlGroup = xmlGroup;
        this.matchClassType = matchClassType;
    }
}

public class EndpointDefinition : FieldDefinition
{
    public EndpointDefinition(string xmlGroup,
                              string xmlTagName,
                              string attribute,
                              string matchClassType)
        : base(xmlGroup,
               xmlTagName,
               attribute,
               matchClassType,
               new string[0],
               new string[0],
               new string[0])
    {
    }
    public EndpointDefinition(string xmlGroup,
                              string xmlTagName,
                              string attribute,
                              string matchClassType,
                              string[] constructorFields)
        : base(xmlGroup,
                xmlTagName,
                attribute,
                matchClassType,
                constructorFields,
                new string[0],
                new string[0]) 
    {
    }
    
    public virtual void AddContractNameAttribute(ManifestBuilder mfb, 
                                                 XmlNode node,
                                                 MetaDataCustomAttribute data, 
                                                 string contractName)
    {
        mfb.AddAttribute(node, "contractName", contractName);
    }
}

public class ServiceEndpointDefinition : EndpointDefinition
{
    public ServiceEndpointDefinition(string xmlGroup,
                                     string xmlTagName,
                                     string attribute,
                                     string matchClassType)
        : base(xmlGroup, xmlTagName, attribute, matchClassType)
    {
    }

    public override void AddContractNameAttribute(ManifestBuilder mfb,
                                                  XmlNode node,
                                                  MetaDataCustomAttribute data,
                                                  string contractName)
    {
        // takes endpoint type as argument
        if (data.FixedArgs == null || data.FixedArgs.Length != 1) {
            mfb.Error("ServiceEndpoint attribute must have 1 type argument");
            return;
        }

        // now make it easy to split into name=value pairs by doing some
        // string replacing
        string ctorArgument = "contractName=" + data.FixedArgs[0];
        ctorArgument = ctorArgument.Replace("+", " endpointEnd=");
        ctorArgument = ctorArgument.Replace(", V", " v");
        ctorArgument = ctorArgument.Replace(", C", " c");
        ctorArgument = ctorArgument.Replace(", P", " p");
        ctorArgument = ctorArgument.Replace(",", " assembly=");

        // now we can split on ' ' and '=' to get name/value pairs
        string [] endpointConfig = ctorArgument.Split(' ');

        // grab only the contractName, ignore the rest
#if false
        foreach (string attrib in endpointConfig) {
            string [] pair = attrib.Split('=');
            if (pair.Length == 2) {
                string name = pair[0];
                string value = pair[1];
                AddAttribute(node, name, value);
            }
        }
#else
        string [] pair = endpointConfig[0].Split('=');
        Debug.Assert(pair.Length == 2);
        string name = pair[0];
        Debug.Assert(name == "contractName");
        string value = pair[1];
        base.AddContractNameAttribute(mfb, node, data, value);
#endif
    }
}
