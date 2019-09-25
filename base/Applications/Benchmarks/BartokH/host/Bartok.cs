//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

#define NONONNULLTYPECHECK  // required on Singularity, no affect on other Windows.

namespace Bartok {

  using System;
  using System.IO;
  using System.Text;
  using System.Collections;
  using Bartok.Utility;
  using Bartok.Datatype;
  using Bartok.CfgUtil;
  using Bartok.Ir;
  using Bartok.Lir;
  using Bartok.Analysis;
  using Bartok.Opt.IrCleanup;
  using Bartok.Opt.Ir;
  using Bartok.Opt.Lir;
  using Bartok.Opt;
  using Bartok.Regalloc;
  using Bartok.Opt.Ssa;
  using Bartok.Backend;

#if ON_SINGULARITY
  using Microsoft.Singularity;
#endif

  //
  // Bartok.cs
  //
  // Main entry point for compiler

  // "public class Bartok {..}" breaks the namespace lookup of Bartok.*
  // Is this a bug?
  public class BartokClass {

      public static long CHECK_COUNT = 0;
      public static long CHECK_COUNT_LOWER = 0;

      public static int Main(String[] args) {
#if ON_SINGULARITY
          // AppRuntime.EnableGCVerify = false;
          // DebugStub.WriteLine("Bartok Host: Enabled GC Verifier");
          // AppRuntime.EnableGCAccounting = true;
          // DebugStub.WriteLine("Bartok Host: Enabled GC Accounting");
#endif
          Bartok.MSIL.MetaDataUtil.Configure(new MetaDataOutput());

          try {
              ProcessCmdLine(args);
              if((fileNames.Count == 0) && (linkNames.Count == 0)) {
                  CHECK_COUNT++;
                  CHECK_COUNT_LOWER++;

                  PrintUsage();
                  Util.Error("\nno files to process...aborting.");
                  Util.Exit(-11);
              }

              if(StageControl.AtomicSupport) {
                  StageControl.TryAllSupport = true;
              }

              Util.Message(NoiseLevel.PerPhase,
                           "fileNames = "
                           + new CollectionFormatter(fileNames));
              Util.Message(NoiseLevel.PerPhase,
                           "refFileNames = "
                           + new CollectionFormatter(refFileNames));
              Util.Message(NoiseLevel.PerPhase,
                           "libDirNames = "
                           + new CollectionFormatter(libDirNames));
              Util.Message(NoiseLevel.PerPhase,
                           "outputDirName = " + outputDirName);

              if (overrideNames.Count > 0) {
                  Util.Message(NoiseLevel.PerPhase,
                               "overrideNames = "
                               + new CollectionFormatter(overrideNames));
              }
              if (entryPoints.Count > 0) {
                  Util.Message(NoiseLevel.PerPhase,
                               "entryPoints = "
                               + new CollectionFormatter(entryPoints));
              }

              // Create helper data structures
              DateTime startTime = Util.startTime;
              bool fLoadDebugInfo = StageControl.SymbolicDebug;
              StageControl.BartokLinkPhase = false;
              if (StageControl.CompileOnly) {
                  // separate compilation
                  foreach (String fileName in fileNames) {
                      String outputName =
                          ComputeOutputName(fileName, outputDirName);
                      ArrayList loadFileNames = new ArrayList(1);
                      loadFileNames.Add(fileName);
                      String shortName = GetShortName(fileName).ToLower();

                      // we need to compile mscorlib.dll together with
                      // system.dll
                      bool fDefineOverride = shortName.Equals("mscorlib.dll");

                      TypeData typeData = new TypeData();
                      CompileFile(typeData, loadFileNames, refFileNames,
                                  overrideNames, overrideDefNames,
                                  fDefineOverride, outputName,
                                  startTime, fLoadDebugInfo);
                  }
              } else {
                  // Create output root name.
                  if (outputRootName == null) {
                      outputRootName = (String) fileNames[0];
                  }

                  // strip off extension, if there is one.
                  int dotIndex = outputRootName.LastIndexOf('.');
                  if (dotIndex != -1) {
                      String ext = outputRootName.Substring(dotIndex + 1);
                      if (ext.Equals("dll") || ext.Equals("obj")
                          || ext.Equals("exe")) {
                          outputRootName =
                              outputRootName.Substring(0, dotIndex);
                      }
                  }

                  bool fDefineOverride = StageControl.WholeProgram;
                  TypeData typeData = new TypeData();
                  String objFileName =
                      CompileFile(typeData, fileNames, refFileNames,
                                  overrideNames, overrideDefNames, fDefineOverride,
                                  outputRootName, startTime, fLoadDebugInfo);
                  linkNames.Add(objFileName);

#if DO_LINK
                  StageControl.BartokLinkPhase = true;
                  BartokLinker bartokLinker = new BartokLinker();
                  typeData = StageControl.WholeProgram ? typeData : null;
                  bartokLinker.Link(typeData, fileNames, linkNames,
                                    refFileNames, overrideNames, overrideDefNames,
                                    libDirNames,
                                    entryPoints, initializerSkips,
                                    outputRootName);
#endif
              }
          } catch(AbortException) {
              // Abort code already dumped the stack
              Util.Exit(-1);
          } catch(Exception e) {
              Util.Error("Internal uncaught {0} exception", e);
              Util.Exit(-1);
          }
          Util.Message(NoiseLevel.PerPhase,
                       "STATIC COUNT IS: " + CHECK_COUNT);
          Util.Message(NoiseLevel.PerPhase,
                       "STATIC LOWER IS: " + CHECK_COUNT_LOWER);
          return 0;
      }

      private static String CompileFile(TypeData typeData,
                                        ArrayList fileNames,
                                        ArrayList refFileNames,
                                        ArrayList overrideNames,
                                        ArrayList overrideDefNames,
                                        bool fDefineOverride,
                                        String outputName,
                                        DateTime startTime,
                                        bool fLoadDebugInfo) {
          ConvertMsil2Ir(fileNames, refFileNames, overrideNames,
                         overrideDefNames, fDefineOverride, startTime,
                         fLoadDebugInfo, typeData);

          CHECK_COUNT++;
          CHECK_COUNT_LOWER++;


#if SELF_PROFILING
          System.GC.Collect();
          long memoryUsage = System.GC.GetTotalMemory(false);
          Util.Message("memory usage: " + memoryUsage);
#endif

          if (entryPoints.Count > 0) {
              Util.Message(NoiseLevel.PerPhase,
                           "entryPoints = "
                           + new CollectionFormatter(entryPoints));
          }
          if(!StageControl.CompileOnly && (entryPoints.Count == 0)) {
              Util.Abort("No entry points found");
          }

          typeData.ComputeEntryMethod(entryPoints);
          Util.Assert(typeData.EntryPoints.Count == entryPoints.Count);

          // register all global analysis
          AnalysisRegistry analysisRegistry = RegisterAnalysis(typeData);

          // Create a series of phases that are each applied to the
          // whole program.
          Bartok.Ir.PhaseList phases = new Bartok.Ir.PhaseList("ir");

          CHECK_COUNT--;
          CHECK_COUNT_LOWER--;

          AddPhases(phases, analysisRegistry, outputName, typeData);

          Util.Message(phases.ComponentPhases.ToString());
          if (StageControl.DumpContainers) {
              phases.Add(new TypeDataPrettyPhase("After IR:"));
          }
          Bartok.Opt.IrCleanup.Statistics.Reset(typeData);
          BartokList phaseNames = phases.ComponentPhases;
          foreach(Object phaseObj in phaseNames) {
              if(!(phaseObj is string)) {
                  Util.Warn("Not string: {0}X",
                            phaseObj.ToString());
                  continue;
              }
              string phaseName = (string)phaseObj;
              if(phaseName.IndexOf(' ') != -1) {
                  Util.Warn("Phase has a space in name: {0}", phaseName);
              }
          }
          foreach(string phaseName in StageControl.disabledPhaseNames) {
              if(phaseNames.Contains(phaseName)) {
                  continue;
              }
              if(StageControl.disabledPhaseNamesFound.Contains(phaseName)) {
                  continue;
              }
              Util.Abort("Couldn't find phase: " + phaseName);
          }
          phases.Go(typeData);

          Bartok.Opt.IrCleanup.Statistics.Summary();

#if SELF_PROFILING
          memoryUsage = System.GC.GetTotalMemory(false);
          Util.Message("memory usage: " + memoryUsage);
#endif

          // backend phases:
          Util.Message("outputRootName = " + outputName);

          String objFileName = LirPhases.run(typeData, fileNames, outputName,
                                             StageControl.GenObjFile);
          System.GC.Collect();
          Util.Message("End of Bartok: " + GC.GetTotalMemory(false));
          return objFileName;
      }

      private static void ConvertMsil2Ir(ArrayList fileNames,
                                         ArrayList refFileNames,
                                         ArrayList overrideNames,
                                         ArrayList overrideDefNames,
                                         bool fDefineOverride,
                                         DateTime startTime,
                                         bool fLoadDebugInfo,
                                         TypeData typeData) {
          // Remove redundant fileNames
          // Remove refFileNames that are redundant with fileNames
          for(int i=0; i<fileNames.Count; ++i) {
#if ON_SINGULARITY
              String fileI = ((String)fileNames[i]).ToLower();
#else
              String fileI = Path.GetFullPath((String) fileNames[i]).ToLower();
#endif
              for(int j=i+1; j<fileNames.Count; ++j) {
#if ON_SINGULARITY
                  String fileJ =((String) fileNames[j]).ToLower();
#else
                  String fileJ =
                      Path.GetFullPath((String) fileNames[j]).ToLower();
#endif
                  if(fileI == fileJ) {
                      Util.Warn("Removing redundant input {0} from command line",
                                fileNames[j]);
                      fileNames.RemoveAt(j);
                  }
              }

              for(int j=0; j<refFileNames.Count; ++j) {
                  String fileJ = MSIL.MetaDataResolver.ResolveFileName
                      (libDirNames, (String) refFileNames[j]);
                  if(fileJ == null) {
                      // Future failure in MetaDataResolver will have a better
                      // error message so move on.
                      continue;
                  }
                  fileJ = fileJ.ToLower();

                  if(fileI == fileJ) {
                      Util.Warn("Removing redundant reference {0} (with a code input) from command line",
                                refFileNames[j]);
                      refFileNames.RemoveAt(j);
                  }
              }

          }

          // Remove redundant refFileNames (may be redundant with fileNames
          // or other refFileNames)
          for(int i=0; i<refFileNames.Count; ++i) {
              String fileI = MSIL.MetaDataResolver.ResolveFileName
                  (libDirNames, (String) refFileNames[i]);
              if(fileI == null) {
                  // Future failure in MetaDataResolver will have a better
                  // error message so move on.
                  continue;
              }
              fileI = fileI.ToLower();

              for(int j=i+1; j<refFileNames.Count; ++j) {
                  String fileJ = MSIL.MetaDataResolver.ResolveFileName
                      (libDirNames, (String) refFileNames[j]);
                  if(fileJ == null) {
                      // Future failure in MetaDataResolver will have a better
                      // error message so move on.
                      continue;
                  }
                  fileJ = fileJ.ToLower();

                  if(fileI == fileJ) {
                      Util.Warn("Removing redundant reference {0} from command line",
                                refFileNames[j]);
                      refFileNames.RemoveAt(j);
                  }
              }
          }

          bool fTranslateTryAll = StageControl.TryAllSupport;
          bool fTranslateAtomic = StageControl.AtomicSupport;
          bool fMsilMessages = Verbosity.level >= NoiseLevel.PerPhase;

          Bartok.MSIL.MetaDataResolver libResolver =
              new Bartok.MSIL.MetaDataResolver(refFileNames, libDirNames,
                                               startTime, fLoadDebugInfo,
                                               fMsilMessages);
          Bartok.MSIL.MetaDataResolver overrideResolver;
          if (fDefineOverride) {
              // load code
              overrideResolver =
                  new Bartok.MSIL.MetaDataResolver(overrideNames,
                                                   startTime,
                                                   fLoadDebugInfo,
                                                   fTranslateTryAll,
                                                   fTranslateAtomic,
                                                   fMsilMessages);
          } else {
              // don't load code
              overrideResolver =
                  new Bartok.MSIL.MetaDataResolver(overrideNames,
                                                   libDirNames,
                                                   startTime, fLoadDebugInfo,
                                                   fMsilMessages);
          }
          Bartok.MSIL.MetaDataResolver overrideDefResolver =
              new Bartok.MSIL.MetaDataResolver(overrideDefNames, startTime,
                                               fLoadDebugInfo,
                                               fTranslateTryAll,
                                               fTranslateAtomic,
                                               fMsilMessages);
          Bartok.MSIL.MetaDataResolver loadResolver =
              new Bartok.MSIL.MetaDataResolver(fileNames, startTime,
                                               fLoadDebugInfo,
                                               fTranslateTryAll,
                                               fTranslateAtomic,
                                               fMsilMessages);
          Bartok.MSIL.MetaDataResolver[] resolvers =
              new Bartok.MSIL.MetaDataResolver[] {
                  libResolver, overrideResolver, overrideDefResolver,
                  loadResolver
              };
          Bartok.MSIL.MetaDataResolver.ResolveCustomAttributes(resolvers);
          MetaDataParser parser =
              new MetaDataParser(entryPoints.Count == 0 ? entryPoints : null);
          Util.TimestampMessage(NoiseLevel.PerPhase,
                                "translating from MSIL");
          parser.Parse(loadResolver, overrideResolver,
                       overrideDefResolver, libResolver,
                       typeData, fDefineOverride, false);

          Util.TimestampMessage(NoiseLevel.PerPhase,
                                "finished translating");
      }

      private static AnalysisRegistry RegisterAnalysis(TypeData typeData) {
          AnalysisRegistry analysisRegistry = new AnalysisRegistry(typeData);
          analysisRegistry.RegisterAnalysis(VirtualCallAnalysis.makeFactory());
          return analysisRegistry;
      }

      private static void AddPhases(Bartok.Ir.PhaseList phases,
                                    AnalysisRegistry analysisRegistry,
                                    String outputName,
                                    TypeData typeData) {
          if (StageControl.PrintContainers) {
              phases.Add(new TypeDataPrintPhase("After parse:"));
          }
          if (StageControl.DumpContainers) {
              phases.Add(new TypeDataPrettyPhase("After parse:"));
          }
          if (StageControl.SingSharpTemplateRemover) {
              phases.Add(new SingSharpTemplateRemover());
          }
          if (StageControl.RuntimeMods) {
              phases.Add(new RuntimeMods());
          }
          if (StageControl.IrMultiPropSimple) {
              phases.Add(new IrMultiPropSimple("System.GC"));
          }
          if (StageControl.IrDeadAssignmentSimple1) {
              phases.Add(new IrDeadAssignmentSimplePhase("System.GC"));
          }
          if (StageControl.IrTreeShake) {
              phases.Add(new IrTreeShake(typeData.EntryPoints,
                                         dynamicLoads,
                                         StageControl.WholeProgram,
                                         analysisRegistry));
          }

          //
          //phases.Add
          //  (new DynamicCount
          //      ("VirtualCallsStart",
          //       new DynamicCount.OpcodeFilter
          //           (Operator.OpCodes.CallVirtual,
          //            Operator.OpCodes.InterfaceCall),
          //       DynamicCount.Granularity.PerSite));
          //

          //
          //phases.Add
          //  (new DynamicCount
          //      ("ASCstart",
          //       new DynamicCount.OpcodeFilter
          //           (Operator.OpCodes.CheckArrayStore,
          //            Operator.OpCodes.CheckVectorStore),
          //       DynamicCount.Granularity.PerSite));
          //

          if (StageControl.PtrAnalysis) {
              phases.Add(PtrTypeSimpleSystem.CreateAnalysis());
              phases.Add(PtrTypeHierarchySystem.CreateAnalysis());
              phases.Add(PtrTypeSetSystem.CreateAnalysis());
          }

          // create wrapper that insert calls to leaveGCSafeState and
          // enterGCSafeState.
          phases.Add(new CreateEntryPointWrapper());

          // trap ValueType.Equals and override it by compiler generated
          // routines.
          if (StageControl.IrOverrideValueTypeEquals) {
              phases.Add(new Convert.ValueTypeEquals());
          }

          if (StageControl.LimitedReflection) {
              phases.Add(new Convert.OverrideVTableInit());
          }

          if (StageControl.IrConvertSizeofPrimitive) {
              Convert.ToMir.Mask mask = Convert.ToMir.Mask.SizeofPrimitive;
              phases.Add(new Convert.ToMir(mask));
          }

          // SPOONS: region related phases:
          //// A temporary pass that cleans up the scratch objects so that the
          //// DemandAnalysis is not confused by the randomness that the tree
          //// shaker leaves behind.
          //phases.Add(new CleanScratch());
//
          //// Build a "Foo_layout" for each class "Foo"; other setup required
          //// by DemandAnalysis.
          //phases.Add(new LayoutBuilder());
//
          //// Perform first- and last-use analysis; add explicit region
          //// variables and effects.
          //phases.Add(new DemandAnalysis());
//
          //// Print the code
          //phases.Add(new TypeDataPrettyPhase("After Demand:"));
          //

          // Perform first- and last-use analysis; add explicit region
          // variables and effects.

          // must happen after DemandAnalysis, but before any inlining /
          // rearranging basic blocks or calls.
#if !VC
          if(StageControl.TryAllSupport) {
              phases.Add(new Bartok.Convert.PropagateLogging(analysisRegistry));
              phases.Add(new TypeDataDummyPhase());
          }
#endif

          if (StageControl.IrScanCallEffects) {
              phases.Add(new IrScanCallEffects());
          }

          if(StageControl.DumpInheritance) {
              phases.Add(new DumpInheritancePhase(StageControl.DumpInheritanceFile));
          }

#if PHX_TODO
          phases.Add(new TypeDataToPhoenix());
#endif
          phases.Add(new TypeInit(initializerSkips));

          if (StageControl.InstrumentCalls) {
              phases.Add(new InstrumentCalls());
          }

          if (StageControl.IrStoreChecks) {
              phases.Add(new IrStoreCheckElim());
          }
          if (StageControl.BuildC2Mods
              && StageControl.UnmanagedStrings) {
              phases.Add(new IrUnmanagedStrings());
          }
          phases.Add(IrCleanup.Create());
          if (StageControl.BuildC2Mods
              && StageControl.IdentifyAsMethods) {
              phases.Add(new IrIdentifyAsMethods());
          }

          if (StageControl.WholeProgram
              && StageControl.IrDeadAssignmentSimpleFormals
              && StageControl.IrTreeShake) {
              phases.Add(new IrDeadAssignmentSimpleFormalsPhase());
              phases.Add(new IrTreeShake(typeData.EntryPoints,
                                         dynamicLoads,
                                         StageControl.WholeProgram,
                                         analysisRegistry));
          }

          phases.Add(new Convert.IrInsertDelegate());

          IrFieldAnalysis fieldAnalysis = null;
          if (StageControl.GCType ==
              StageControl.ReferenceCountingCollector &&
              StageControl.RCCollectorOptRCSubsumed &&
              StageControl.RCCollectorOptRCSubsumedByROFields) {
              IrFieldAnalysis.FieldFilter filter =
                  new IrFieldAnalysis.RCAproposFieldFilter();
              fieldAnalysis = new IrFieldAnalysis(true, filter);
              phases.Add(fieldAnalysis);
          }

          if(StageControl.IrInlineConstructor) {
              phases.Add(new Convert.ToMir(Convert.ToMir.Mask.Constructor));
          }
          // When only one class implements an interface, replace the interface
          // with the class.
          if (StageControl.IrInterfaceElim && StageControl.WholeProgram) {
              phases.Add(new InterfaceElim());
          }

          if (StageControl.IrSimpleInliner) {
              phases.Add(new IrSimpleInliner(new IrInline(), false, false, false));
          } else if (StageControl.IrAttributeInliner) {
              // inline methods that has [inline] attributes.
              phases.Add(new IrSimpleInliner(new IrInline(), false, false));
          }

          if (StageControl.FailAfterInliner) {
              phases.Add(new FailPhase());
          }

          if (StageControl.IrMultiPropSimple) {
              phases.Add(new IrMultiPropSimple());
          }
          if (StageControl.IrSuppressExnEdges) {
              phases.Add(new IrSuppressExnEdges());
          }
          if (StageControl.IrLoadStoreOpt) {
              phases.Add(new IrLoadStoreOpt(analysisRegistry));
          }
          if (StageControl.DevirtualizeCall) {
              phases.Add(new IrDevirtualizeCall(analysisRegistry));
          }

          if (StageControl.IrSimpleInliner &&
              StageControl.IrInlinerDoIncreaseSize) {
              phases.Add(new IrSimpleInliner(new IrInline(), true, false, false));
          }

          if (StageControl.LazyTypeInits) {
              phases.Add(new TypeInit(initializerSkips, true));
          }

          // Eliminate unnecessary instanceOf/check casts.   Only makes
          // 2 passes by punting back edges.
          if (StageControl.IrTypeTestElimPunt) {
              phases.Add(new TypeTestElimPunt());
          }

          // Eliminate unnecessary instanceOf/check casts - full iterative
          // analysis.   More expensive than the above analysis, but yields
          // little improvement in practice.
          if (StageControl.IrTypeTestElim) {
              phases.Add(new TypeTestElim());
          }

          // Deletes all CheckCasts and instanceOf IDisposable for sake of
          // experimentation.  Normally not enabled, as it is unsafe.

          if (StageControl.IrDeleteCheckCasts) {
              phases.Add(new DeleteCheckCast());
          }

          if (StageControl.IrConvertOpt) {
              phases.Add(new IrConvertOpt());
              phases.Add(new IrDeadAssignmentSimplePhase());
              phases.Add(new IrReverseCopyProp());
          }

          // Just do thread analysis once.
          IrLockedFields locks = null;
          if (StageControl.ExtendThreadFieldsABCD ||
              StageControl.SsaNullCheckGlobalThreaded) {

              if (StageControl.IrTreeShake) {
                  phases.Add(new IrTreeShake(typeData.EntryPoints,
                                             dynamicLoads,
                                             StageControl.WholeProgram,
                                             analysisRegistry));
              }

              if(StageControl.OptimisticLocking) {
                  locks = new ClassIrLockedFields(analysisRegistry);
              } else {
                  locks = new IrLockedFields(analysisRegistry);
              }
              phases.Add(locks);
          }

          // Array bounds check elimination
          if (StageControl.ABCD) {
              phases.Add(new ABCD(analysisRegistry, locks));
          }

          if (StageControl.IrConvertArrayBounds) {
              Convert.ToMir.Mask mask = Convert.ToMir.Mask.CheckVectorBounds;
              phases.Add(new Convert.ToMir(mask));
          }

          if (StageControl.IrConvertInferface) {
              Convert.ToMir.Mask mask = Convert.ToMir.Mask.InterfaceCall;
              phases.Add(new Convert.ToMir(mask));
          }

          if (StageControl.IrConvertSimpleArrayAccess) {
              Convert.ToMir.Mask mask = Convert.ToMir.Mask.SimpleArrayAccess;
              phases.Add(new Convert.ToMir(mask));
          }

          if (StageControl.IrCloneLoopHeader) {
              phases.Add(new IrCloneLoopHeader());
              phases.Add(new IrJumpElim());
              phases.Add(new IrMultiPropSimple());
          }

          if (StageControl.SsaOpts) {
              if (StageControl.SsaNullCheckGlobalThreaded) {
                  phases.Add(SSAPhase.Create(analysisRegistry, locks));
              } else {
                  phases.Add(SSAPhase.Create());
              }
          }

          if(locks != null) {
              locks = null;
          }

          // IrInsertStructCopy phase insert a StructCopy() method
          // to each struct type, and lower struct Id operators
          // to a call to StructCopy() method.
          phases.Add(new Convert.IrInsertStructCopy());

#if !VC
          if(StageControl.TryAllSupport) {
              phases.Add(new IrInsertLogging());
          }

          if(StageControl.TryAllSupport &&
             StageControl.AtomicSupportUpdateEnlistOptFlow) {
              // without the IrLoadStoreOpt here, EnlistIndirects
              // generated by [Store]StructFields can't be moved.
              phases.Add(new IrLoadStoreOpt(analysisRegistry));
              phases.Add(new IrInsertUpdateEnlistments());
              // otherwise CSE misses things that it should be eliminating
              phases.Add(new IrMultiPropSimple());
          }

          if (StageControl.TryAllSupport &&
              StageControl.IrKeepManager) {
              phases.Add(new IrKeepManager(analysisRegistry));
          }
#endif

          if(StageControl.IrStructVectorOperations) {
              phases.Add(new IrStruct(true));
          }

          if (StageControl.IrLoadStoreOpt) {
              phases.Add(new IrLoadStoreOpt(analysisRegistry));
          }

#if !VC
          if (StageControl.TryAllSupport &&
              StageControl.AtomicSupportUpdateEnlistOpt) {
              phases.Add(new IrSimpleAvoidUpgrade());
          }
#endif

          if (StageControl.IrConvertComplexArrayAccess) {
              Convert.ToMir.Mask mask = Convert.ToMir.Mask.ComplexArrayAccess;
              phases.Add(new Convert.ToMir(mask));
          }

          if (StageControl.IrConvertExpandedArrayAccess) {
              Convert.ToMir.Mask mask = Convert.ToMir.Mask.ExpandedArrayAccess;
              phases.Add(new Convert.ToMir(mask));
          }

          if (StageControl.ArraySupportOptimizePass && StageControl.SsaOpts) {
              phases.Add(SSAPhase.Create());
          }

#if !VC
          if (StageControl.TryAllSupport &&
              StageControl.TryAllSupportOptimizePass &&
              StageControl.SsaOpts) {
              phases.Add(SSAPhase.Create());
          }
#endif

          if (StageControl.IrInitStaticField) {
              phases.Add(new IrInitStaticField());
          }

          if (StageControl.LazyTypeInits
              && StageControl.TypeInitRemoveEmptyCctors) {
              phases.Add(new TypeInit(initializerSkips, true));
          }

          if (StageControl.GCType ==
              StageControl.ReferenceCountingCollector) {
              phases.Add(new IrStructRCUpdate());
          }

          if (StageControl.GCType ==
              StageControl.DeferredReferenceCountingCollector) {
              phases.Add(new IrStructDRCUpdate());
          }

          if (StageControl.IrTreeShake && StageControl.IrTreeShakeLate) {
              phases.Add(new IrTreeShake(typeData.EntryPoints,
                                         dynamicLoads,
                                         StageControl.WholeProgram,
                                         analysisRegistry));
          }

          if (StageControl.TypedReference) {
              phases.Add(new Convert.ToMir(Convert.ToMir.Mask.Vararg1));

              // All of vararg1 must finish before vararg2, so we wrap vararg2
              // in a typedata phase to enforce that.
              phases.Add(new TypeDataMethodPhase
                  (new Convert.ToMir(Convert.ToMir.Mask.Vararg2)));
          }

          //
          //// We do not know where all of the calls will be because lowering can
          //// introduce calls.  We make a best guess here.  If we moved all
          //// call-generating lowering to HIR (via ToMir or equivalent), then
          //// this could be easily done.  We are currently missing calls for the
          //// following:
          //// - pinvoke, stubs, etc
          //// - some arithmetic conversions
          //// - casts - can't add because not all are calls
          //// - RC, tryall, atomic
          //// - others?
          //phases.Add
          //  (new DynamicCount
          //      ("Calls",
          //       new DynamicCount.OpcodeFilter
          //           (Operator.OpCodes.Call,
          //            Operator.OpCodes.CallIndirect,
          //            Operator.OpCodes.CallVirtual,
          //            Operator.OpCodes.InterfaceCall,
          //            Operator.OpCodes.MonitorEnter,
          //            Operator.OpCodes.MonitorExit,
          //            Operator.OpCodes.IndirectToData,
          //            Operator.OpCodes.CustomGetSize,
          //            Operator.OpCodes.CheckVectorStore,
          //            Operator.OpCodes.CheckVectorElementAddress,
          //            Operator.OpCodes.InitVector,
          //            Operator.OpCodes.CheckArrayStore,
          //            Operator.OpCodes.CheckArrayElementAddress,
          //            Operator.OpCodes.InitArray,
          //            Operator.OpCodes.InitType,
          //            Operator.OpCodes.GetITable,
          //            Operator.OpCodes.NewObject,
          //            Operator.OpCodes.NewVector,
          //            Operator.OpCodes.NewArray),
          //       DynamicCount.Granularity.Global));
          //phases.Add(new TypeDataDummyPhase());
          //phases.Add
          //  (new DynamicCount
          //      ("VirtualCallsEnd",
          //       new DynamicCount.OpcodeFilter
          //           (Operator.OpCodes.CallVirtual,
          //            Operator.OpCodes.InterfaceCall),
          //       DynamicCount.Granularity.PerSite));
//
          //phases.Add
          //  (new DynamicCount
          //      ("ASCend",
          //       new DynamicCount.OpcodeFilter
          //           (Operator.OpCodes.CheckArrayStore,
          //            Operator.OpCodes.CheckVectorStore),
          //       DynamicCount.Granularity.PerSite));
          //phases.Add(new TypeDataDummyPhase());
//
          //phases.Add
          //  (new DynamicCount
          //      ("WB",
          //       new DynamicCount.OpcodeFilter
          //           (Operator.OpCodes.LocWriteBarrier),
          //       DynamicCount.Granularity.Global));
          //phases.Add(new TypeDataDummyPhase());
          //

          if (StageControl.WholeProgram && StageControl.OptRuntimeData) {
              phases.Add(new RuntimeData());
          }

          if (StageControl.IrConvertArrayOpt) {
              phases.Add(new IrConvertArrayOpt());
          }

          // insert write barrier after chooserep so we know the size of
          // of objects. This is needed because we try to remove write
          // barrier when we store to the young generation, however,
          // big objects are in the old generation even though it is
          // newly created. Therefore, we need to know object size to
          // know if it is a big object.
          if (StageControl.InsertWriteBarrier) {
              phases.Add(new IrWriteBarrier());
              phases.Add(new Convert.ToMir
                  (Convert.ToMir.Mask.ConvertWriteBarrier));
          }

          // convert type tests and sizeof effect to Mir
          Convert.ToMir.Mask typeMask = Convert.ToMir.Mask.CheckCast
                                        | Convert.ToMir.Mask.Sizeof;
          if (!(StageControl.GCType ==
              StageControl.ReferenceCountingCollector ||
              StageControl.GCType ==
              StageControl.DeferredReferenceCountingCollector)) {
              typeMask |= Convert.ToMir.Mask.GetCurrentThread;
          }
          if (StageControl.TypedReference) {
              typeMask |= Convert.ToMir.Mask.TypedRef;
          }
          phases.Add(new Convert.ToMir(typeMask));

          if (StageControl.IrSimpleInliner) {
              phases.Add(new IrSimpleInliner(new IrInline(), false, true,
                                             true, 0, 0, 0));
          }

           if(StageControl.TypeInitElim) {
               phases.Add(new IrTypeInitElim(analysisRegistry));
           }

          if (StageControl.IrRemoveDoubleCmp) {
              phases.Add(new IrCmpElim());
          }

          if (StageControl.IrArrayBaseLength) {
              phases.Add(new IrArrayBaseLength());
              phases.Add(new IrDeadAssignmentSimplePhase());
          }

          if (StageControl.IrInitTypeInliner &&
              StageControl.LazyTypeInits) {
              phases.Add(new IrInitTypeInliner(typeData, new IrInline()));
          }

          if (StageControl.GCType ==
              StageControl.ReferenceCountingCollector) {
              if (StageControl.RCCollectorShowStatistics) {
                  String message = "Before RC Update Injection";
                  phases.Add(new IrBBStats(message));
              }

              phases.Add(new IrRCUpdate());

              if (StageControl.RCCollectorShowStatistics) {
                  String message = "After RC Update Injection";
                  phases.Add(new IrBBStats(message));
              }
              if (StageControl.RCCollectorOptImmortals) {
                  phases.Add(new IrImmortalObjectRCUpdates());
              }
              if (StageControl.RCCollectorOptRCSubsumed) {
                  IrSimpleThreadEscape threadLocalObjects = null;
                  if (StageControl.RCCollectorOptThreadLocalAnalysis) {
                      IrLockedFields threadSafeFields = null;
                      if (StageControl.WholeProgram &&
                          StageControl.
                          RCCollectorOptRCSubsumedByTSFields) {
                          threadSafeFields =
                              new IrLockedFields(analysisRegistry);
                          phases.Add(threadSafeFields);
                      }
                      threadLocalObjects =
                          new IrSimpleThreadEscape(analysisRegistry,
                                                   threadSafeFields);
                      phases.Add(threadLocalObjects);
                  }
                  IrRCSubsumedRCUpdates rcSubsumption =
                      new IrRCSubsumedRCUpdates(analysisRegistry,
                                                fieldAnalysis,
                                                threadLocalObjects);
                  phases.Add(rcSubsumption);
              }
              if (StageControl.RCCollectorOptCoalescingUpdates) {
                  phases.Add(new IrBBLocalCoalesceRCUpdates());
              }
              if (StageControl.
                  RCCollectorOptStaticAcyclicRefTypeUpdates) {
                  phases.Add(new IrAcyclicRefTypeRCUpdates());
              }
              if (StageControl.RCCollectorOptNonNullRCUpdates) {
                  phases.Add(SSAPhase.NullCheckAnalysis());
              }
              if (StageControl.RCCollectorShowStatistics) {
                  String message = "After RC Optimizations";
                  phases.Add(new IrBBStats(message));
              }

              Convert.ToMir.Mask mask = Convert.ToMir.Mask.RCUpdate |
                  Convert.ToMir.Mask.GetCurrentThread;
              phases.Add(new Convert.ToMir(mask));
              if (StageControl.RCCollectorOptInlineRCUpdates &&
                  StageControl.IrSimpleInliner) {
                  phases.Add(new IrSimpleInliner(new IrInline(),
                                                 true,
                                                 false,
                                                 true));
              }
              phases.Add(new TypeDataDummyPhase());
          }

          if (StageControl.GCType ==
              StageControl.DeferredReferenceCountingCollector) {
              if (StageControl.RCCollectorShowStatistics) {
                  String message = "Before DRC Update Injection";
                  phases.Add(new IrBBStats(message));
              }

              phases.Add(new IrDRCUpdate());

              if (StageControl.RCCollectorShowStatistics) {
                  String message = "After DRC Update Injection";
                  phases.Add(new IrBBStats(message));
              }
              if (StageControl.RCCollectorOptImmortals) {
                  phases.Add(new IrImmortalObjectRCUpdates());
              }
              if (StageControl.RCCollectorOptCoalescingUpdates) {
                  phases.Add(new IrBBLocalCoalesceRCUpdates());
              }
              if (StageControl.
                  RCCollectorOptStaticAcyclicRefTypeUpdates) {
                  phases.Add(new IrAcyclicRefTypeRCUpdates());
              }
              if (StageControl.RCCollectorOptNonNullRCUpdates) {
                  phases.Add(SSAPhase.NullCheckAnalysis());
              }
              if (StageControl.RCCollectorShowStatistics) {
                  String message = "After DRC Optimizations";
                  phases.Add(new IrBBStats(message));
              }

              Convert.ToMir.Mask mask = Convert.ToMir.Mask.RCUpdate |
                  Convert.ToMir.Mask.GetCurrentThread;
              phases.Add(new Convert.ToMir(mask));
              if (StageControl.RCCollectorOptInlineRCUpdates &&
                  StageControl.IrSimpleInliner) {
                  phases.Add(new IrSimpleInliner(new IrInline(),
                                                 true,
                                                 false,
                                                 true));
              }
              phases.Add(new TypeDataDummyPhase());
          }


#if !VC
          if(StageControl.TryAllSupport &&
             StageControl.TryAllDecomposeOpt) {
              phases.Add(new IrDecomposeTransMemChecks(analysisRegistry));
              // IrDecomposeTransMemChecks emits GetCurrentThread ops
              phases.Add(new IrLoadStoreOpt(analysisRegistry));
              Convert.ToMir.Mask mask = Convert.ToMir.Mask.GetCurrentThread;
              phases.Add(new Convert.ToMir(mask));
          }

          if (StageControl.TryAllSupport &&
              StageControl.IrConvertTryAll) {
              Convert.ToMir.Mask mask = Convert.ToMir.Mask.TryAll;
              phases.Add(new Convert.ToMir(mask));
              if (StageControl.IrSimpleInliner) {
                  phases.Add(new IrSimpleInliner(new IrInline(),
                                                 true,
                                                 false));
              }
          }
#endif

          // The inliners may inline some of the methods that handle special
          // MSIL opcodes, adding in instructions like Id<Struct> that we
          // don't expect to see this late in the lowering.  Add one more
          // scan of the code to remove them.
          phases.Add(new Convert.IrInsertStructCopy());

          if (StageControl.IrTreeShake && StageControl.IrTreeShakeLate) {
              phases.Add(new IrTreeShake(typeData.EntryPoints,
                                         dynamicLoads,
                                         StageControl.WholeProgram,
                                         analysisRegistry));
          }

          if (StageControl.PtrAnalysis) {
              phases.Add(PtrTypeSimpleSystem.CreateAnalysis());
              phases.Add(PtrTypeHierarchySystem.CreateAnalysis());
              phases.Add(PtrTypeSetSystem.CreateAnalysis());
          }

          if (StageControl.PrintContainers) {
              phases.Add(new TypeDataPrintPhase("end of HIR:"));
          }
      }

      public static ArrayList fileNames;
      public static ArrayList refFileNames;
      public static ArrayList libDirNames;
      private static ArrayList outputDirNames;
      public static String outputDirName;
      public static ArrayList overrideNames;
      public static ArrayList overrideDefNames;
      public static String outputRootName;
      public static ArrayList entryPoints;
      public static ArrayList linkNames;
      private static ArrayList initializerSkips;
      private static ArrayList dynamicLoads;
      private static bool alreadyPrintedUsage = false;

      private static String StripName(String fileName) {
          // strip off extension, if there is one.
          int dotIndex = fileName.LastIndexOf('.');
          if (dotIndex != -1) {
              String ext = fileName.Substring(dotIndex + 1);
              if (ext.Equals("dll") || ext.Equals("obj")
                  || ext.Equals("exe")) {
                  fileName = fileName.Substring(0, dotIndex);
              }
          }
          return fileName;
      }

      private static String GetShortName(String fileName) {
          int charindex = Math.Max(fileName.LastIndexOf('/'),
              fileName.LastIndexOf('\\'));
          String shortName = (charindex >= 0)
              ? fileName.Substring(charindex + 1)
              : fileName;
          return shortName;
      }

      private static String GetDirName(String fileName) {
          int charindex = Math.Max(fileName.LastIndexOf('/'),
                                   fileName.LastIndexOf('\\'));
          String dirName = (charindex >= 0)
              ? fileName.Substring(0, charindex + 1)
              : "";
          return dirName;
      }

      private static String ComputeOutputName(String inputFileName,
                                              String outputDirName) {
          String fileName = Path.GetFileNameWithoutExtension(inputFileName);
          String outputName = outputDirName + '\\' + fileName;
          return outputName;
      }

      private static void ProcessCmdLine(String[] args) {
          fileNames = new ArrayList();
          refFileNames = new ArrayList();
          libDirNames = new ArrayList();
          overrideNames = new ArrayList();
          overrideDefNames = new ArrayList();
          outputDirNames = new ArrayList();
          entryPoints = new ArrayList();
          initializerSkips = new ArrayList();
          linkNames = new ArrayList();
          dynamicLoads = new ArrayList();
          int index = 0;
#if ON_SINGULARITY
          index = 1;
#endif
          while (index < args.Length) {
              String argument = args[index];
              if ((argument[0] == '-') || (argument[0] == '/')) {
                  String option = argument.Substring(1);
                  ProcessOption(argument, option, args, ref index);
              } else {
                  index++;
                  fileNames.Add(argument);
              }
          }
          switch (outputDirNames.Count) {
            case 0: {
                outputDirName = ".\\debug";
                break;
            }
            case 1: {
                outputDirName = (String)outputDirNames[0];
                break;
            }
            default: {
                Util.Error("Error: specified multiple output directories {0}",
                           new CollectionFormatter(outputDirNames));
                break;
            }
          }

          if((StageControl.GCType == StageControl.ReferenceCountingCollector)
             && StageControl.StructInheritance) {
              Util.Abort("Error: RC Collector code has not been updated to "
                         + "handle struct inheritance");
          }
          if((StageControl.GCType ==
             StageControl.DeferredReferenceCountingCollector)
             && StageControl.StructInheritance) {
              Util.Abort("Error: Deferred RC Collector code has not been updated to "
                         + "handle struct inheritance");
          }
      }

      private static void ProcessOption(String argument, String option,
                                        String[] args, ref int index) {
          String loweredOption = option.ToLower();
          String optionValue;

          if (IsOption(args, option, loweredOption, "entry:",
                       ref index, out optionValue)) {
              AddSemicolonDelimitedNames(entryPoints, optionValue);
          } else if (IsOption(args, option, loweredOption, "reference:",
                              ref index, out optionValue)
                     || IsOption(args, option, loweredOption, "r:",
                                 ref index, out optionValue)) {
              AddSemicolonDelimitedNames(refFileNames, optionValue);
          } else if (IsOption(args, option, loweredOption, "bartoklink:",
                              ref index, out optionValue)) {
              AddSemicolonDelimitedNames(linkNames, optionValue);
          } else if (IsOption(args, option, loweredOption, "override:",
                              ref index, out optionValue)) {
              AddSemicolonDelimitedNames(overrideNames, optionValue);
          } else if (IsOption(args, option, loweredOption, "overridedef:",
                              ref index, out optionValue)) {
              AddSemicolonDelimitedNames(overrideDefNames, optionValue);
          } else if (IsOption(args, option, loweredOption, "lib:",
                              ref index, out optionValue)) {
              AddSemicolonDelimitedNames(libDirNames, optionValue);
          } else if (IsOption(args, option, loweredOption, "out:",
                              ref index, out optionValue)) {
              outputRootName = optionValue;
          } else if (IsOption(args, option, loweredOption, "outdir:",
                              ref index, out optionValue)) {
              AddSemicolonDelimitedNames(outputDirNames, optionValue);
          } else if (IsOption(args, option, loweredOption, "skip:",
                              ref index, out optionValue)) {
              AddSemicolonDelimitedNames(initializerSkips, optionValue);
          } else if (IsOption(args, option, loweredOption, "substitute:",
                              ref index, out optionValue)) {
              StageControl.substituteString = optionValue;
          } else if (IsOption(args, option, loweredOption, "disable:",
                              ref index, out optionValue)) {
              StageControl.disabledPhaseNames.Add(optionValue);
          } else if (IsOption(args, option, loweredOption, "dynamicload:",
                              ref index, out optionValue)) {
              AddSemicolonDelimitedNames(dynamicLoads, optionValue);
          } else if (IsOption(args, option, loweredOption, "features:",
                              ref index, out optionValue)) {
              StageControl.mixinConditionals =
                  StageControl.mixinConditionals + "," + optionValue;
          } else if (IsOption(args, option, loweredOption, "noisymethod:",
                              ref index, out optionValue)) {
              StageControl.noisyMethodNames.Add(optionValue);
              //Util.Message("noisyMethodNames="
              //             + StageControl.noisyMethodNames);
          } else if (IsOption(args, option, loweredOption, "debugmethod:",
                              ref index, out optionValue)) {
              StageControl.debugMethodNames.Add(optionValue);
              StageControl.noisyMethodNames.Add(optionValue);
              //Util.Message("debugMethodNames="
              //             + StageControl.debugMethodNames);
          } else if (IsOption(args, option, loweredOption, "verbosity:",
                              ref index, out optionValue)) {
              Verbosity.FromString(optionValue);
          } else if (IsOption(args, option, loweredOption, "marksweepgc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.MarkSweepCollector;
              StageControl.GCLargeObjectSize = 2040;
              StageControl.InlineSegregatedFreeList = true;
              StageControl.InsertWriteBarrier = false;
          } else if (IsOption(args, option, loweredOption, "semispacegc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.SemispaceCollector;
              StageControl.InsertWriteBarrier = true;
          } else if (IsOption(args, option, loweredOption, "slidinggc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.SlidingCollector;
              StageControl.InsertWriteBarrier = true;
          } else if (IsOption(args, option, loweredOption, "adaptivecopyinggc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.AdaptiveCopyingCollector;
              StageControl.InsertWriteBarrier = true;
          } else if (IsOption(args, option, loweredOption,
                              "referencecountinggc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.ReferenceCountingCollector;
              StageControl.InsertWriteBarrier = false;
              StageControl.GCInlineAllocations = false;
              StageControl.mixinConditionals =
                  StageControl.mixinConditionals + ",ReferenceCountingGC";
              if (StageControl.RCCollectorVerifyRefCounts) {
                  StageControl.UseVTableBits = true;
                  StageControl.mixinConditionals =
                      StageControl.mixinConditionals +
                      ",ReferenceCountingGCVerification";
              }
          } else if (IsOption
                     (args, option, loweredOption, "deferredreferencecountinggc",
                      ref index, out optionValue)) {

              StageControl.GCType = StageControl.DeferredReferenceCountingCollector;
              StageControl.InsertWriteBarrier = false;
              StageControl.GCInlineAllocations = false;
              StageControl.mixinConditionals =
                  StageControl.mixinConditionals + ",DeferredReferenceCountingGC";
              if (StageControl.RCCollectorVerifyRefCounts) {
                  StageControl.UseVTableBits = true;
                  StageControl.mixinConditionals =
                      StageControl.mixinConditionals +
                      ",DeferredReferenceCountingGCVerification";
              }
          } else if (IsOption(args, option, loweredOption, "concurrentmsgc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.ConcurrentMSCollector;
              StageControl.GCLargeObjectSize = 2040;
              StageControl.Wb = StageControl.WbCMS;
              StageControl.GCInlineAllocations = false;
              StageControl.InlineSegregatedFreeList = true;
              StageControl.PreWriteBarrier = true;
              StageControl.InsertWriteBarrier = true;
              StageControl.GCInlineWriteBarrier = false;
              StageControl.GCWriteBarrierTracksStaticFields = true;
              StageControl.mixinConditionals =
                  StageControl.mixinConditionals + ",ConcurrentMSGC";
          } else if (IsOption(args, option, loweredOption, "nullgc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.NullCollector;
              StageControl.InsertWriteBarrier = false;
          } else if (IsOption(args, option, loweredOption, "atomicrcgc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.AtomicRCCollector;
              StageControl.GCLargeObjectSize = 2040;
              StageControl.Wb = StageControl.WbARC;
              StageControl.GCInlineAllocations = false;
              StageControl.InlineSegregatedFreeList = true;
              StageControl.InsertWriteBarrier = true;
              StageControl.GCInlineWriteBarrier = false;
              StageControl.GCWriteBarrierTracksStaticFields = true;
          } else if (IsOption(args, option, loweredOption, "minopt",
                              ref index, out optionValue)) {
              StageControl.SsaOpts = false;
              StageControl.IrInterfaceElim = false;
              StageControl.DevirtualizeCall = false;
              StageControl.IrTypeTestElimPunt = false;
              StageControl.IrTypeTestElim = false;
              StageControl.IrSimpleInliner = false;

              // IR clean up optimizations
              StageControl.IrDeadAssignmentSimple2 = false;
              StageControl.IrCleanupStructOperations = false;
              StageControl.IrShortCircuitBBlocks = false;
              StageControl.IrTreeShakeLate = false;
              StageControl.IrArrayLoadStoreOpt = false;
              StageControl.IrConvertSimpleArrayAccess = false;

              // from the backend
              StageControl.RegAllocCoalesce = false;
              StageControl.RegAllocSpill = StageControl.SpillOptimizeSinglePass;
              StageControl.OptLirCompactify = false;
              StageControl.OptLirGlobalConstantProp = false;
              StageControl.OptLirLocalConstantProp = true;
              StageControl.OptLirImproveCC = false;
              StageControl.OptLirPeephole = false;
              StageControl.OptLirReverseCSE = false;
              StageControl.OptLirGlobalCopyProp = false;
              StageControl.OptLirLocalCopyProp = true;
              StageControl.LayoutLoopHeaderLast = false;

              if (StageControl.SymbolicDebug) {
                  StageControl.OptimizeLocals = false;
              }
          } else if (IsOption(args, option, loweredOption, "nohiropt",
                              ref index, out optionValue)) {
              StageControl.ABCD = false;
              StageControl.DevirtualizeCall = false;
              StageControl.IdentifyAsMethods = false;
              StageControl.IrAttributeInliner = false;
              StageControl.IrBBLocalCopyProp = false;
              StageControl.IrCleanup = false;
              StageControl.IrCleanupStructOperations = false;
              StageControl.IrCloneLoopHeader = false;
              StageControl.IrConvertOpt = false;
              StageControl.IrDeadAssignmentSimple1 = false;
              StageControl.IrDeadAssignmentSimple2 = false;
              StageControl.IrInitStaticField = false;
              StageControl.IrInterfaceElim = false;
              StageControl.IrJumpElim = false;
              StageControl.IrLoadStoreOpt = false;
              StageControl.IrMultiPropSimple = false;
              StageControl.IrPeepholeNull = false;
              StageControl.IrRemoveDoubleCmp = false;
              StageControl.IrReverseCopyProp = false;
              StageControl.IrShortCircuitBBlocks = false;
              StageControl.IrSimpleInliner = false;
              StageControl.IrStoreChecks = false;
              StageControl.IrTreeShakeLate = false;
              StageControl.IrTypeTestElimPunt = false;
              StageControl.SsaArraySimple = false;
              StageControl.SsaDeadCode = false;
              StageControl.SsaLoopInv = false;
              StageControl.SsaNullCheck = false;
              StageControl.SsaOpts = false;
              StageControl.TypeInitRemoveEmptyCctors = false;
              StageControl.UnmanagedStrings = false;
          } else if (IsOption(args, option, loweredOption, "singularity",
                              ref index, out optionValue)) {
              StageControl.SingSharpTemplateRemover = true;
              StageControl.DisablePInvoke = true;
              StageControl.StrictEcma = true;
              StageControl.CustomAllocatorTypes = true;
              StageControl.SurrogateBoxing = true;
              StageControl.StructInheritance = true;
              StageControl.IrTreeShakeCreatePointedToStructs = true;
              StageControl.IrTreeShakeLate = false; // not tested
              StageControl.TypeInitRemoveEmptyCctors = false; // not tested
              StageControl.CheckNoHeapAllocation = true;
          } else if (IsOption(args, option, loweredOption, "verbosehelp",
                              ref index, out optionValue)) {
              PrintUsage();
              StageControl.PrintUsage();
          } else if (IsOption(args, option, loweredOption, "verbosehelpalpha",
                              ref index, out optionValue)) {
              PrintUsage();
              StageControl.PrintUsageAlpha();
          } else if (IsOption(args, option, loweredOption, "x86",
                              ref index, out optionValue)) {
              StageControl.TargetArch = StageControl.X86;
              StageControl.Target64Bit = false;
          } else if (IsOption(args, option, loweredOption, "x64",
                              ref index, out optionValue)) {
              StageControl.TargetArch = StageControl.X64;
              StageControl.Target64Bit = true;
          } else if (IsOption(args, option, loweredOption, "help",
                              ref index, out optionValue)
                     || IsOption(args, option, loweredOption, "?",
                                 ref index, out optionValue)) {
              PrintUsage();
          }  else if (IsOption
                     (args, option, loweredOption, "centralpt",
                      ref index, out optionValue)) {
                  StageControl.PTType = StageControl.CentralPT;
          } else if (IsOption
                     (args, option, loweredOption, "centralpthimem",
                      ref index, out optionValue)) {
                  StageControl.PTType = StageControl.CentralPTHimem;
          } else if (IsOption
                     (args, option, loweredOption, "flatdistributedpt",
                      ref index, out optionValue)) {
                  StageControl.PTType = StageControl.FlatDistributedPT;
          } else if (IsOption
                     (args, option, loweredOption, "flatdistributedtestpt",
                      ref index, out optionValue)) {
                  StageControl.PTType = StageControl.FlatDistributedPTTest;
          } else if (StageControl.SetOptionFromCommandLine(loweredOption)) {
              index++;
          } else if (loweredOption.StartsWith("stagecontrol")) {
              Util.AbortUserCE("/stagecontrol no longer supported; "
                               + "use the option directly");
          } else {
              Util.AbortUserCE("Unknown option: " + option);
          }
      }

      private static bool IsOption(String[] args,
                                   String option, String loweredOption,
                                   String possibleOptionName,
                                   ref int index, out String optionValue) {
          if(possibleOptionName.EndsWith(":")) {
              if(loweredOption.StartsWith(possibleOptionName)) {
                  index++;
                  if(option.Length == possibleOptionName.Length) {
                      // case: "/option: value"
                      optionValue = args[index++];
                  } else {
                      // case: "/option:value"
                      optionValue = option.Substring(possibleOptionName.Length);
                  }
                  return true;
              }
          } else {
              if(loweredOption == possibleOptionName) {
                  index++;
                  optionValue = null;
                  return true;
              }
          }

          optionValue = null;
          return false;
      }

      private static void AddSemicolonDelimitedNames(ArrayList names,
                                                     String argument) {
          int index = 0;
          StringBuilder buf = new StringBuilder();
          while (index < argument.Length) {
              if (argument[index] != ';') {
                  buf.Append(argument[index]);
                  index++;
              }
              else {
                  if (buf.Length > 0) {
                      names.Add(buf.ToString());
                      buf = new StringBuilder();
                  }
                  index++;
              }
          }
          names.Add(buf.ToString());
      }

      public static void PrintUsage() {
          if (alreadyPrintedUsage) {
              return;
          }
          alreadyPrintedUsage = true;
          Util.Message(
@"Usage:
    bartok [options] files

Bartok main options (case insensitive):
    /entry: <method1>;<method2>;...    specify entry points
    /reference: <file1>;<file2>;...    reference metadata from assembly files
    /r: <file1>;<file2>;...            short form of /reference:
    /bartoklink: <file1>;<file2>;...   reference precompiled object files
    /override: <file1>;<file2>;...     files overriding /r: metadata
    /lib: <dir1>;<dir2>;...            additional dirs to search for references
    /out: <file>                       output file name
    /outdir: <dir>                     dir for output .exe, asm, obj, etc.
                                        (defaults to .\\debug)
    /skip: <type1>;<type2>;...         specify type initializers to disable
                                        if building static ordering
    /substitute:<oldname1>=<newname1>, rename TypeRefs before performing lookup
     <oldname2>=<newname2>,...
    /disable:<phasename>               disable a phase
    /dynamicload:<typename>            make type available for dynamic loading
    /features:<???>                    << TODO >>
    /noisymethod:<methname>            enable noisy output for meth
    /debugmethod:<methname>            enable debug+noisy output for meth
    /verbosity:<noiselevel>            set output level {Silence,PerPhase,
                                        PerClass,PerMethod,PerBlock,
                                        PerInstruction} (defaults to PerPhase)
    /marksweepgc                       compile for mark-sweep collector
    /semispacegc                       compile for semispace collector
    /slidinggc                         compile for sliding collector
    /adaptivecopyinggc                 compile for semispace-sliding hybrid
                                        collector
    /referencecountinggc               compile for reference counting collector
    /deferredreferencecountinggc       compile for deferred reference counting collector
    /concurrentmsgc                    compile for concurrent mark-sweep
                                        collector
    /nullgc                            compile for no collector
    /minopt                            disable most optimizations
    /nohiropt                          disable all HIR optimizations
    /singularity                       set default Singularity options
    /verbosehelp                       help message including stage control
                                        options by category
    /verbosehelpalpha                  help message including stage control
                                        options in alphabetical order
    /help or /?                        help message");
      }
  }

  internal class MetaDataOutput : Bartok.MSIL.IMetaDataOutput {
      public TextWriter Log { get { return Util.Log; } }
      public TextWriter ErrorOut { get { return Util.ErrorOut; } }
      public TextWriter WarnOut { get { return Util.WarnOut; } }

      public void Error(string msg)
      {
          Util.Error(msg);
      }

      public void Error(string format, params Object[] objs)
      {
          Util.Error(format, objs);
      }

      public void ErrorDetail(string msg)
      {
          Util.ErrorDetail(msg);
      }

      public void Warn(string msg)
      {
          Util.Warn(msg);
      }

      public void Warn(string format, params Object[] objs)
      {
          Util.Warn(format, objs);
      }

      public void WarnDetail(string msg)
      {
          Util.WarnDetail(msg);
      }

      public void Message(string msg)
      {
          Util.Message(msg);
      }
  }
}
