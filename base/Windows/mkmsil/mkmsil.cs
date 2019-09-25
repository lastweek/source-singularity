// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//=====================================================================
//=====================================================================  


using System;
using System.Collections;
using System.IO;
using System.Reflection;
using System.Runtime.InteropServices;
using Bartok.MSIL;

public class MkMsil {

    public static bool HasCustomAttributes(MetaDataTypeDefinition type)
    {
        if (type.CustomAttributes != null) {
            return true;
        }

#if DONT_DO_INTERFACES
        if (type.Interfaces != null && type.Interfaces.Length != 0) {
            Console.WriteLine("     interfaces:");
            foreach (MetaDataObject iface in type.Interfaces) {
                Console.WriteLine("        {0}", iface);
            }
        }
#endif
#if DONT_DO_FIELDS
        if (type.Fields != null && type.Fields.Length != 0) {
            Console.WriteLine("     fields:");
            foreach (MetaDataField field in type.Fields) {
                Console.WriteLine("        {0}", field.Name);
            }
        }
#endif
        if (type.Methods != null && type.Methods.Length != 0) {
            foreach (MetaDataMethod method in type.Methods) {
                if (method.CustomAttributes != null) {
                    return true;
                }
            }
        }
        return false;
    }

    public static void DumpMetaData(MetaData metadata)
    {
        foreach (MetaDataTypeDefinition type in metadata.TypeDefs) {
            Console.WriteLine("  {0}", type.FullName);

            ArrayList customAttributes = type.CustomAttributes;

            if (customAttributes != null) {
                foreach (MetaDataCustomAttribute attribute in customAttributes) {
                    Console.WriteLine("    {0}", attribute.Type);
                }
            }

            if (type.Extends != null) {
                Console.WriteLine("     extends {0}", type.Extends);
            }

            if (type.Methods != null && type.Methods.Length != 0) {
                foreach (MetaDataMethod method in type.Methods) {
                    Console.WriteLine("      {0}", method.Name);

                    customAttributes = method.CustomAttributes;
                    if (customAttributes != null) {
                        foreach (MetaDataCustomAttribute attribute in customAttributes) {
                            Console.WriteLine("        {0}", attribute.Name);
                            if (attribute.FixedArgs != null) {
                                foreach (object o in attribute.FixedArgs) {
                                    Console.WriteLine("         [{0}]", o);
                                }
                            }
                            else {
                                Console.WriteLine("          [no fixed args]");
                            }

                            if (attribute.NamedArgs != null) {
                                foreach (MetaDataCustomAttribute.NamedArg a in attribute.NamedArgs) {
                                    Console.WriteLine("         [{0}]", a);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    public static MetaDataCustomAttribute MethodFindAttribute(MetaDataMethod method,
                                                              MetaDataTypeDefinition type)
    {
        if (method.CustomAttributes != null) {
            foreach (MetaDataCustomAttribute attribute in method.CustomAttributes) {
                if (attribute.TypeDefOrRef == type) {
                    return attribute;
                }
            }
        }
        return null;
    }

    public static void Main(String[] args)
    {
        Console.WriteLine("MkMsil:");

        ArrayList streams = new ArrayList();

        foreach (string arg in args) {
            streams.Add(new MetaDataResolver.LoadedStream(arg,
                                                          Path.GetFullPath(arg),
                                                          new FileStream(arg,
                                                                         FileMode.Open,
                                                                         FileAccess.Read,
                                                                         FileShare.Read)));
        }

        Console.WriteLine("-----------------------------------------------------------------");
        MetaDataResolver resolver = new MetaDataResolver(streams, false, false, false);
        Console.WriteLine("-----------------------------------------------------------------");
        MetaDataResolver.ResolveCustomAttributes(new MetaDataResolver[] {resolver});
        Console.WriteLine("-----------------------------------------------------------------");

        MetaDataTypeDefinition shellCommandAttribute
            = resolver.ResolveName("Microsoft.Singularity.Shell.ShellCommandAttribute");
        Console.WriteLine("{0}", shellCommandAttribute);
        Console.WriteLine("-----------------------------------------------------------------");

#if DONT
        foreach (MetaData metadata in resolver.MetaDataList) {
            DumpMetaData(metadata);
        }
#endif

        foreach (MetaData metadata in resolver.MetaDataList) {
            foreach (MetaDataTypeDefinition type in metadata.TypeDefs) {
                foreach (MetaDataMethod method in type.Methods) {
                    MetaDataCustomAttribute attribute
                        = MethodFindAttribute(method, shellCommandAttribute);

                    if (attribute != null) {
                        Console.WriteLine("new ShellCommand(\"{0}\", \"{1}\", new Command({2})),",
                                          attribute.FixedArgs[0],
                                          attribute.FixedArgs[1],
                                          method.Name);
                    }
                }
            }
        }
    }
}

