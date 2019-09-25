//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{

  using System;
  using System.Collections;
  using System.IO;
  using System.Reflection;
  using System.Text;

  //
  // MetaDataResolver.cs
  //
  // Facility for loading metadata from multiple assemblies and
  // supporting resolution of references to definitions

  public class MetaDataResolver {

      // Use these constructors to load a set of assemblies (including code)
      public MetaDataResolver(ArrayList loadFileNames, bool fLoadDebugInfo):
          this(loadFileNames, System.DateTime.Now, fLoadDebugInfo)
      {
      }

      public MetaDataResolver(ArrayList loadFileNames,
                              DateTime startTime,
                              bool fLoadDebugInfo)
      {
          this.startTime = startTime;
          LoadMetaData(LoadStreams(loadFileNames, null), true, true, fLoadDebugInfo);
          BuildMap();
      }

      // Use these constructor to create a resolver for library assemblies
      public MetaDataResolver(ArrayList refFileNames,
                              ArrayList libDirNames,
                              bool fLoadDebugInfo):
          this(refFileNames, libDirNames, System.DateTime.Now, fLoadDebugInfo)
      {
      }

      public MetaDataResolver(ArrayList refFileNames,
                              ArrayList libDirNames,
                              DateTime startTime,
                              bool fLoadDebugInfo) {
          this.startTime = startTime;
          LoadMetaData(LoadStreams(refFileNames, libDirNames), false, false, fLoadDebugInfo);
          BuildMap();
      }


      // Use these constructors to load a set of assemblies from streams.
      public MetaDataResolver(ArrayList loadedStreams,
                              bool fLoadCode,
                              bool fLoadSectionsFromExecutable,
                              bool fLoadDebugInfo):
          this(loadedStreams,
               System.DateTime.Now,
               fLoadSectionsFromExecutable,
               fLoadDebugInfo,
               fLoadDebugInfo)
      {
      }

      public MetaDataResolver(ArrayList loadedStreams,
                              DateTime startTime,
                              bool fLoadCode,
                              bool fLoadSectionsFromExecutable,
                              bool fLoadDebugInfo)
      {
          this.startTime = startTime;
          LoadMetaData(loadedStreams, fLoadCode, fLoadSectionsFromExecutable, fLoadDebugInfo);
          BuildMap();
      }

      public MetaDataTypeDefinition ResolveTypeRef(MetaDataTypeReference reference) {
          String refName = reference.Namespace+"."+reference.Name;
          return ResolveName(refName);
      }

      public MetaDataTypeDefinition ResolveName(String refName) {
          if (fDebug) {
              Console.Out.WriteLine("Attempting to resolve in "+this.GetHashCode()+": "+refName);
          }
          EntryPair pair = (EntryPair)mapTable[refName];
          if (pair == null) {
              if (fDebug) {
                  Console.Out.WriteLine("...failed");
              }
              return null;
          }
          else {
              MetaDataTypeDefinition result = pair.Definition;
              if (fDebug) {
                  ResolverEntry entry = pair.Entry;
                  Console.Out.WriteLine("...found "+result+" in "+entry);
              }
              return result;
          }
      }

      public ArrayList EntryList {
          get { return entryList; }
      }

      public ArrayList MetaDataList {
          get { return metaDataList; }
      }

      public override String ToString() {
          StringBuilder sb = new StringBuilder("MetaDataResolver(");
          foreach (Object element in this.entryList) {
              sb.Append(element.ToString());
              sb.Append(",");
          }
          sb.Append(")");
          return sb.ToString();
      }

      //////////////////////////

      private ArrayList LoadStreams(ArrayList refFileNames,
                                    ArrayList libDirNames) {
          // try to create streams for all files in refFileNames,
          // looking first in the current directory, then (sequentially) in
          // all the directories named in libDirNames

          ArrayList streams = new ArrayList();

          foreach (String fileName in refFileNames) {
              Stream stream = null;
              String successName = null;

              if (fDebug) {
                  Console.Out.WriteLine("looking for '"+fileName+"'");
              }

              try {
                  stream = new FileStream(fileName,
                                          FileMode.Open,
                                          FileAccess.Read,
                                          FileShare.Read);
                  successName = fileName;
              }
              catch (FileNotFoundException) {
                  // failed on raw filename; try prefixing with libDirNames elts
                  if (fDebug) {
                      Console.Out.WriteLine("...failed");
                  }
                  if (libDirNames != null) {
                      foreach (String dirName in libDirNames) {
                          try {
                              String fullName = dirName+"\\"+fileName;
                              if (fDebug) {
                                  Console.Out.WriteLine("looking for '"+fullName+"'");
                              }
                              stream = new FileStream(fileName,
                                                      FileMode.Open,
                                                      FileAccess.Read,
                                                      FileShare.Read);
                              successName = fullName;
                          }
                          catch (FileNotFoundException) {
                              if (fDebug) {
                                  Console.Out.WriteLine("...failed");
                              }
                              continue;
                          }
                          catch (DirectoryNotFoundException) {
                              if (fDebug) {
                                  Console.Out.WriteLine("...failed");
                              }
                              continue;
                          }
                      }
                  }
              }

              StringBuilder sb = new StringBuilder();
              if (successName == null) {
                  sb.Append("Unable to find '");
                  sb.Append(fileName);
                  sb.Append("' in current dir");
                  if (libDirNames != null && libDirNames.Count > 0) {
                      sb.Append(" or {");
                      foreach (String dirName in libDirNames) {
                          sb.Append(dirName);
                          sb.Append(", ");
                      }
                      sb.Remove(sb.Length-2, 2);
                      sb.Append("}");
                  }
                  Console.Out.WriteLine(sb.ToString());
                  Console.Out.WriteLine("Aborting!");
                  String stackTrace = System.Environment.StackTrace;
                  Console.Out.WriteLine(stackTrace);
                  throw new Exception(sb.ToString());
              }

              streams.Add(new LoadedStream(successName,
                                           Path.GetFullPath(successName),
                                           stream));
          }
          return streams;
      }

      private void LoadMetaData(ArrayList loadedStreams,
                                bool fLoadCode,
                                bool fLoadSectionsFromExecutable,
                                bool fLoadDebugInfo) {
          // try to load the metadata for all streams in loadedStreams.

          this.entryList = new ArrayList();
          this.metaDataList = new ArrayList();

          foreach (LoadedStream stream in loadedStreams) {
              PELoader loader = null;
              try {
                  if (fDebug) {
                      Console.Out.WriteLine("loading "+stream.Name+"'");
                  }
                  loader = new PELoader(stream.Content, stream.Name);
              }
              catch (FileNotFoundException) {
                  // failed on raw filename; try prefixing with libDirNames elts
                  if (fDebug) {
                      Console.Out.WriteLine("...failed");
                  }
              }
              StringBuilder sb = new StringBuilder();
              if (loader == null) {
                  sb.Append("Unable to load '");
                  sb.Append(stream.Name);
                  sb.Append("'");
                  Console.Out.WriteLine(sb.ToString());
                  Console.Out.WriteLine("Aborting!");
                  String stackTrace = System.Environment.StackTrace;
                  Console.Out.WriteLine(stackTrace);
                  throw new Exception(sb.ToString());
              }

              TimeSpan diffSpan = System.DateTime.Now.Subtract(startTime);
              int diffMsec = (int) diffSpan.TotalMilliseconds;
              String secString = (diffMsec / 1000).ToString();
              sb.Append("        ", 0, (8 - secString.Length));
              sb.Append(secString);
              sb.Append('.');
              sb.Append((diffMsec%1000).ToString("000"));
              sb.Append(":  ");
              sb.Append("Loading metadata ");
              if (fLoadCode) {
                  sb.Append("with code ");
              }
              sb.Append("from '");
              sb.Append(stream.Name);
              sb.Append("'");
              Console.Out.WriteLine(sb.ToString());
              MetaData metaData =
                  MetaData.loadMetaData(stream.Path, loader, fLoadCode, fLoadDebugInfo);
              metaDataList.Add(metaData);
              ResolverEntry entry = new ResolverEntry(metaData, stream.Name);
              entryList.Add(entry);
              //              if (fLoadSectionsFromExecutable && loader.IsExecutableImage()) {
              //                  Console.Out.WriteLine("loading all sections from " + fileName);
              //                  loader.loadSections();
              //              }
              loader.getStream().Close();
          }
      }

      private void BuildMap() {
          // walk entryList in reverse, adding exports to mapTable
          mapTable = new Hashtable();
          for (int i = entryList.Count - 1; i >= 0; i--) {
              ResolverEntry entry = (ResolverEntry)entryList[i];
              MetaData metaData = entry.MetaData;
              // export public typedefs
              if (fDebug) {
                  Console.Out.WriteLine("Registering "+metaData.TypeDefs.Length+" public TypeDefs from '"+entry.Filename+"' in "+this.GetHashCode());
              }
              foreach (MetaDataTypeDefinition def in metaData.TypeDefs) {
                  TypeAttributes visibility =
                      def.Flags & TypeAttributes.VisibilityMask;
                  String fullName = def.FullName;
                  if ((visibility == TypeAttributes.Public) ||
                      (visibility == TypeAttributes.NestedPublic) ||
                      ((visibility == TypeAttributes.NotPublic) &&
                       (fullName.StartsWith("System.Runtime.Compiler") ||
                        fullName.StartsWith("Microsoft.Win32.Win32Native")))) {
                      if (fDebug) {
                          Console.Out.WriteLine("Registering "+fullName);
                      }
                      mapTable[fullName] = new EntryPair(def, entry);
                  }
              }
              // export ExportedTypes
              if (fDebug) {
                  Console.Out.WriteLine("Registering "+metaData.ExportedTypes.Length+" public ExportTypes from '"+entry.Filename+"'");
              }
              foreach (MetaDataExportedType exportType in metaData.ExportedTypes) {
                  String fullName = (exportType.Namespace.Length > 0)
                      ? exportType.Namespace+"."+exportType.Name
                      : exportType.Name;
                  if (mapTable[fullName] == null) {
                      Console.Out.WriteLine("MetaDataResolver doesn't know how to handle "+fullName+"--"+exportType.ToStringLong());
                      throw new Exception();
                  }
                  Console.Out.WriteLine("WARNING: assuming that ExportedType "+exportType.ToStringLong()+" matches "+mapTable[fullName]);
              }
          }
      }

      public static void ResolveCustomAttributes(MetaDataResolver[] resolvers)
      {
          foreach (MetaDataResolver resolver in resolvers) {
              resolver.ResolveMyCustomAttributes(resolvers);
          }
      }

      public void ResolveMyCustomAttributes(MetaDataResolver[] resolvers)
      {
          for (int i = this.entryList.Count - 1; i >= 0; i--) {
              ResolverEntry entry = (ResolverEntry) this.entryList[i];
              MetaData metaData = entry.MetaData;
              foreach (MetaDataCustomAttribute ca in metaData.CustomAttributes) {
                  // Console.WriteLine(ca.ToString());
                  ca.resolveReferences(this, resolvers);
                  // Console.WriteLine(ca.ToStringLong());
              }
          }
      }

      //////////////////////////

      private static readonly bool fDebug = false;

      private DateTime startTime;
      private ArrayList entryList;    // associates filenames with MetaData instances
      private Hashtable mapTable;     // map FullName to EntryPair(typeRef, resolverEntry)
      private ArrayList metaDataList;

      /////////////////////////////////////////

      private class EntryPair {

          public EntryPair(MetaDataTypeDefinition definition,
                           ResolverEntry entry) {
              this.Definition = definition;
              this.Entry = entry;
          }

          public readonly MetaDataTypeDefinition Definition;
          public readonly ResolverEntry Entry;

          public override String ToString() {
              StringBuilder sb = new StringBuilder("EntryPair(");
              sb.Append(Definition.ToString());
              sb.Append(",");
              sb.Append(Entry.ToString());
              sb.Append(")");
              return sb.ToString();
          }
      }

      // descriptive info associated with resolved metadata objects
      public class ResolverEntry {

          public ResolverEntry(MetaData metaData, String filename) {
              this.metaData = metaData;
              this.filename = filename;
          }

          public MetaData MetaData {
              get { return metaData; }
          }

          public String Filename {
              get { return filename; }
          }

          public override String ToString() {
              return ("<ResolverEntry '"+filename+"'>");
          }
          /////////////////////////////

          private MetaData metaData;
          private String filename;
      }

      public class LoadedStream
      {
          public LoadedStream(String name, String path, Stream stream)
          {
              this.name = name;
              this.path = path;
              this.stream = stream;
          }

          public LoadedStream(String name, Stream stream)
          {
              this.name = name;
              this.path = name;
              this.stream = stream;
          }

          public LoadedStream(Stream stream)
          {
              this.name = "<anonymous>";
              this.path = "<anonymous>";
              this.stream = stream;
          }

          public String Name {
              get { return name; }
          }

          public String Path {
              get { return path; }
          }

          public Stream Content {
              get { return stream; }
          }

          public override String ToString() {
              return ("LoadedStream("+name+":"+path+")");
          }

          private String name;
          private String path;
          private Stream stream;
      }
  }
}
