//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

#if ON_SINGULARITY
#define NONONNULLTYPECHECK  // required on Singularity, no affect on other Windows.
#endif

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

  //
  // Bartok.cs
  //
  // Main entry point for compiler

  // "public class Bartok {..}" breaks the namespace lookup of Bartok.*
  // Is this a bug?
  public class BartokClass {

      public static int Main(String[] args) {
          Bartok.MSIL.MetaDataUtil.Configure(new MetaDataOutput());

          try {
              ProcessCmdLine(args);
              if((fileNames.Count == 0) && (linkNames.Count == 0)) {
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
              bool fLoadDebugInfo =
                  StageControl.SymbolicDebug || StageControl.SymbolicIR;
              StageControl.BartokLinkPhase = false;
              if (StageControl.CompileOnly) {
                  // separate compilation
                  for (int i=0; i<fileNames.Count; ++i) {
                      String fileName = (String) fileNames[i];
                      String outputName =
                          ComputeOutputName(fileName, outputDirName);
                      ArrayList loadFileNames = new ArrayList(1);
                      loadFileNames.Add(fileName);
                      ArrayList loadMdilFileNames = null;
                      if (StageControl.BindMdil) {
                          loadMdilFileNames = new ArrayList(1);
                          loadMdilFileNames.Add(mdilFileNames[i]);
                      }
                      String shortName = GetShortName(fileName).ToLower();

                      // we need to compile mscorlib.dll together with
                      // system.dll
                      bool fDefineOverride = shortName.Equals("mscorlib.dll");

                      TypeData typeData = new TypeData();
                      CompileFile(typeData, loadFileNames, loadMdilFileNames,
                                  refFileNames, overrideNames, overrideDefNames,
                                  fDefineOverride, outputName,
                                  startTime, fLoadDebugInfo);
                  }
              } else {
                  // Create output root name.
                  if (outputRootName == null) {
                      outputRootName = (String) fileNames[0];
                  }

                  if (!StageControl.TargetMdil) {
                      outputRootName = StripName(outputRootName);
                  }
                  bool fDefineOverride = StageControl.WholeProgram;
                  TypeData typeData = new TypeData();
                  String objFileName =
                      CompileFile(typeData, fileNames, mdilFileNames,
                                  refFileNames, overrideNames, overrideDefNames,
                                  fDefineOverride, outputRootName,
                                  startTime, fLoadDebugInfo);
                  linkNames.Add(objFileName);

                  if (!StageControl.TargetMdil) {
                      StageControl.BartokLinkPhase = true;
                      BartokLinker bartokLinker = new BartokLinker();
                      typeData = StageControl.WholeProgram ? typeData : null;
                      bartokLinker.Link
                          (typeData, fileNames, linkNames, refFileNames,
                           overrideNames, overrideDefNames, libDirNames,
                           entryPoints, initializerSkips, outputRootName);
                  }
              }
          } catch(AbortException) {
              // Abort code already dumped the stack
              Util.Exit(-1);
          } catch(Exception e) {
              Util.Error("Internal uncaught {0} exception", e);
              Util.Exit(-1);
          }
          return 0;
      }

      private static String CompileFile(TypeData typeData,
                                        ArrayList fileNames,
                                        ArrayList mdilFileNames,
                                        ArrayList refFileNames,
                                        ArrayList overrideNames,
                                        ArrayList overrideDefNames,
                                        bool fDefineOverride,
                                        String outputName,
                                        DateTime startTime,
                                        bool fLoadDebugInfo) {
          Util.Assert(!StageControl.BindMdil || (mdilFileNames.Count == 1),
                      "MDIL support requires exactly one input assembly (got {0})",
                      (mdilFileNames != null) ? mdilFileNames.Count : 0);
          MSIL.MetaDataResolver loadResolver;
          MetaDataParser mdParser;
          ConvertMsil2Ir(fileNames, refFileNames, overrideNames,
                         overrideDefNames, fDefineOverride, startTime,
                         fLoadDebugInfo, typeData,
                         out loadResolver, out mdParser);

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
              Util.UserError("No entry points found");
          }

          typeData.ComputeEntryMethod(entryPoints);
          Util.Assert(typeData.EntryPoints.Count == entryPoints.Count);

          // register all global analysis
          AnalysisRegistry analysisRegistry = RegisterAnalysis(typeData);

          // Create a series of phases that are each applied to the
          // whole program.
          Bartok.Ir.PhaseList phases = new Bartok.Ir.PhaseList("ir");

          AddPhases(phases, analysisRegistry, outputName, typeData);

          if (StageControl.PrintContainers) {
              phases.Add(new TypeDataPrintPhase("end-IR"));
          }
          if (StageControl.DumpContainers) {
              phases.Add(new TypeDataPrettyPhase("end-IR"));
          }
          phases.Add(new TypeDataDummyPhase("end-IR"));

          Util.Message(phases.ComponentPhases.ToString());

          Bartok.Opt.IrCleanup.Statistics.Reset(typeData);
          BartokList phaseNames = phases.ComponentPhases;
          foreach(Object phaseObj in phaseNames) {
              Util.Assert(phaseObj is String,
                          "Non-string in phase name list: {0}", phaseObj);
              String phaseName = (String) phaseObj;
              if((phaseName.IndexOf(' ') != -1)
                 || (phaseName.IndexOf(':') != -1)) {
                  Util.Warn("Phase has a space or colon in name: {0}",
                            phaseName);
              }
          }
          foreach(PhaseControl control in StageControl.phaseControls) {
              String phaseName = control.PhaseName;
              if(phaseName == null) {
                  continue;
              }
              if(phaseNames.Contains(phaseName)) {
                  continue;
              }
              if(StageControl.disabledPhaseNamesFound.Contains(phaseName)) {
                  continue;
              }
#if PHXMIR || PHXBRIDGE
              // HACK: allow /disable:gopt to mimic -off:globalopts from phx
              // also allow /noisyphase:gopt
              // also allow /debugphase:PhxGCEncode
              if(phaseName == "gopt" || phaseName == "PhxGCEncode") {
                  continue;
              }
#endif
              Util.UserError("Couldn't find phase: " + phaseName);
          }

          // append .obj to outputName. We still keep outputName
          // for AsmWriter.
          string objFileName = ComputeObjFileName(outputName);
          phases.Go(typeData);
          Bartok.Opt.IrCleanup.Statistics.Summary();

#if PHXBRIDGE
          phases = new Bartok.Ir.PhaseList("convert to phoenixMir");
          // add bartok mir to phx mir phase
          phases.Add(new PhoenixPhases(typeData, fileNames, objFileName,
                                       outputName, StageControl.GenObjFile));
          phases.Go(typeData);
#endif

#if SELF_PROFILING
          memoryUsage = System.GC.GetTotalMemory(false);
          Util.Message("memory usage: " + memoryUsage);
#endif

#if !PHXBRIDGE
          // backend phases:
          Util.Message(NoiseLevel.PerPhase, "outputRootName = " + outputName);

          LirPhases.run(typeData, loadResolver, mdParser, fileNames,
                            mdilFileNames, objFileName, outputName, StageControl.GenObjFile);
#endif

#if SELF_PROFILING
          System.GC.Collect();
          Util.Message("End of Bartok: " + GC.GetTotalMemory(false));
#endif
          return objFileName;
      }

      // sets out parameters (loadResolver for filenames) when /BindMdil=true,
      // to null otherwise
      private static void ConvertMsil2Ir
      (ArrayList fileNames, ArrayList refFileNames,
       ArrayList overrideNames, ArrayList overrideDefNames,
       bool fDefineOverride, DateTime startTime,
       bool fLoadDebugInfo, TypeData typeData,
       out MSIL.MetaDataResolver outLoadResolver,
       out MetaDataParser outMDParser) {
          // Remove redundant fileNames
          // Remove refFileNames that are redundant with fileNames
          for(int i=0; i<fileNames.Count; ++i) {
              String fileI = ((String)fileNames[i]);
#if !ON_SINGULARITY
              fileI = Path.GetFullPath(fileI);
#endif
              fileI = fileI.ToLower();

              for(int j=i+1; j<fileNames.Count; ++j) {
                  String fileJ = ((String) fileNames[j]);
#if !ON_SINGULARITY
                  fileJ = Path.GetFullPath(fileJ);
#endif
                  fileJ = fileJ.ToLower();

                  if (fileI == fileJ) {
                      Util.Warn
                          ("Removing redundant input {0} from command line",
                           fileNames[j]);
                      fileNames.RemoveAt(j);
                  }
              }

              for(int j=0; j<refFileNames.Count; ++j) {
                  String fileJ = MSIL.MetaDataResolver.ResolveFileName
                      (libDirNames, (String) refFileNames[j]);
                  if (fileJ == null) {
                      // Future failure in MetaDataResolver will have a better
                      // error message so move on.
                      continue;
                  }
#if !ON_SINGULARITY
                  fileJ = Path.GetFullPath(fileJ);
#endif
                  fileJ = fileJ.ToLower();

                  if(fileI == fileJ) {
                      Util.Warn
                          ("Removing redundant reference {0} from command line",
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
#if !ON_SINGULARITY
              fileI = Path.GetFullPath(fileI);
#endif
              fileI = fileI.ToLower();

              for(int j=i+1; j<refFileNames.Count; ++j) {
                  String fileJ = MSIL.MetaDataResolver.ResolveFileName
                      (libDirNames, (String) refFileNames[j]);
                  if(fileJ == null) {
                      // Future failure in MetaDataResolver will have a better
                      // error message so move on.
                      continue;
                  }
#if !ON_SINGULARITY
                  fileJ = Path.GetFullPath(fileJ);
#endif
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
          if (StageControl.BindMdil) {
              outLoadResolver = loadResolver;
              outMDParser = parser;
          } else {
              outLoadResolver = null;
              outMDParser = null;
          }
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
              phases.Add(new TypeDataPrintPhase("parser"));
          }
          if (StageControl.DumpContainers) {
              phases.Add(new TypeDataPrettyPhase("parser"));
          }

          // to allow /noisyphase:parser since MetaDataParser is not a phase
          phases.Add(new TypeDataDummyPhase("parser"));

          phases.Add(new ScalarConversion());
          phases.Add(new TypeChecker());

          if (StageControl.SingSharpTemplateRemover) {
              phases.Add(new SingSharpTemplateRemover());
          }
          if (StageControl.RuntimeMods) {
              phases.Add(new RuntimeMods());
          }

          // We need to do some immediate cleanup of the GCs so that the first
          // treeshake will get us down to only the code for the selected GC
          // configuration.  In particular, we need to clear out the statements
          // like "switch(gctype)" and remove the code on dead branches.
          if (StageControl.IrMultiPropSimple) {
              phases.Add(new IrMultiPropSimple("System.GC"));
              phases.Add(new IrMultiPropSimple("Microsoft.Bartok.Runtime.GC"));
          }
          if (StageControl.IrDeadAssignmentSimple1) {
              phases.Add(new IrDeadAssignmentSimplePhase("System.GC"));
              phases.Add(new IrDeadAssignmentSimplePhase("Microsoft.Bartok.Runtime.GC"));
          }

          if (StageControl.IrTreeShake && !StageControl.BindMdil) {
              phases.Add(new IrTreeShake(typeData.EntryPoints,
                                         dynamicLoads,
                                         StageControl.WholeProgram,
                                         analysisRegistry,
                                         false));
          }

          //
          //phases.Add
          //  (new DynamicCount
          //      ("VirtualCallsStart",
          //       new DynamicCount.OpcodeFilter
          //           (Operator.OpCodes.CallVirtual,
          //            Operator.OpCodes.InterfaceCall),
          //       new DynamicCount.SiteAndTargetReporting()));
          //

          //
          //phases.Add
          //  (new DynamicCount
          //      ("ASCstart",
          //       new DynamicCount.OpcodeFilter
          //           (Operator.OpCodes.CheckArrayStore,
          //            Operator.OpCodes.CheckVectorStore),
          //       new DynamicCount.SiteReporting()));
          //

          if (StageControl.PtrAnalysis || StageControl.PtrAnalysisEarly) {
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

          if (!StageControl.TargetMdil) {
              phases.Add(new Convert.MarshalPhase());
          }

          // Perform first- and last-use analysis; add explicit region
          // variables and effects.

          // must happen after DemandAnalysis, but before any inlining /
          // rearranging basic blocks or calls.
#if !VC
          if(StageControl.TryAllSupport) {
              phases.Add(new Bartok.Convert.PropagateLogging(analysisRegistry));
              phases.Add(new TypeDataDummyPhase("TryAll-end-pipeline"));
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
              && StageControl.IrTreeShake
              && !StageControl.BindMdil) {
              phases.Add(new IrDeadAssignmentSimpleFormalsPhase());
              phases.Add(new IrTreeShake(typeData.EntryPoints,
                                         dynamicLoads,
                                         StageControl.WholeProgram,
                                         analysisRegistry,
                                         false));
          }

          if (!StageControl.TargetMdil) {
              phases.Add(new Convert.IrInsertDelegate());
          }

          phases.Add(new Convert.ToMir(Convert.ToMir.Mask.Constructor));

          // When only one class implements an interface, replace the interface
          // with the class.
          if (StageControl.IrFindConcrete && StageControl.WholeProgram) {
              phases.Add(new IrFindConcrete());
          }

          if (StageControl.DevirtualizeCall) {
              phases.Add(new IrDevirtualizeCall(analysisRegistry));
          }
          if (StageControl.IrImproveTypes && StageControl.WholeProgram) {
              phases.Add(new IrImproveTypes(analysisRegistry));
          }
          if(StageControl.IrPeepholeNull) {
              phases.Add(new IrPeepholeNull());
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
          if (StageControl.IrImproveTypes && StageControl.WholeProgram) {
              phases.Add(new IrImproveTypes(analysisRegistry));
          }
          if(StageControl.IrPeepholeNull) {
              phases.Add(new IrPeepholeNull());
          }

          if (StageControl.IrSimpleInliner &&
              StageControl.IrInlinerDoIncreaseSize) {
              phases.Add(new IrSimpleInliner(new IrInline(), true, false, false));
          }

          if (StageControl.LazyTypeInits
              && StageControl.OptLazyTypeInits) {
              phases.Add(new TypeInit(initializerSkips, true));
          }

          // Eliminate unnecessary instanceOf/check casts.   Only makes
          // 2 passes by punting back edges.
          if (StageControl.IrTypeTestElimPunt) {
              phases.Add(new TypeTestElimPunt());
          }

          // Eliminate unnecessary instanceOf/check casts - full iterative
          // analysis.   More expensive than the above analysis, but yields
          // little improvement in practice - TODO: should be remeasured because
          // of some fixes.
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
              StageControl.SsaNullCheckGlobalThreaded ||
              StageControl.IrLoadStoreOptThreaded) {

              if (StageControl.IrTreeShake && !StageControl.BindMdil) {
                  phases.Add(new IrTreeShake(typeData.EntryPoints,
                                             dynamicLoads,
                                             StageControl.WholeProgram,
                                             analysisRegistry,
                                             false));
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

#if !LILC
          // not needed in LILC mode because ToMir-Lilc lowers InterfaceCall
          if (StageControl.IrConvertInterface && !StageControl.TargetMdil) {
              Convert.ToMir.Mask mask = Convert.ToMir.Mask.InterfaceCall;
              phases.Add(new Convert.ToMir(mask));
          }
#endif

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

          if(locks != null && !StageControl.IrLoadStoreOptThreaded) {
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

          if(StageControl.IrPeepholeNull) {
              phases.Add(new IrPeepholeNull());
          }

          if(StageControl.IrStructVectorOperations) {
              phases.Add(new IrStruct(true));
          }

          if (StageControl.IrLoadStoreOpt) {
              if (StageControl.IrLoadStoreOptThreaded) {
                  phases.Add(new IrLoadStoreOptTSGlobal(analysisRegistry,
                                                        locks));
                  locks = null;
                  StageControl.IrLoadStoreOptThreaded = false;
              } else {
                  phases.Add(new IrLoadStoreOpt(analysisRegistry));
              }
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
              && StageControl.OptLazyTypeInits
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

          if (StageControl.IrTreeShake
              && StageControl.IrTreeShakeLate
              && !StageControl.BindMdil) {
              phases.Add(new IrTreeShake(typeData.EntryPoints,
                                         dynamicLoads,
                                         StageControl.WholeProgram,
                                         analysisRegistry,
                                         false));
          }

          if (StageControl.TypedReference) {
              Convert.ToMir phase2 =
                  new Convert.ToMir(Convert.ToMir.Mask.Vararg2);
              Convert.ToMir phase1 =
                  new Convert.ToMir(Convert.ToMir.Mask.Vararg1, phase2);
              phases.Add(phase1);

              // All of vararg1 must finish before vararg2, so we wrap vararg2
              // in a typedata phase to enforce that.
              phases.Add(new TypeDataMethodPhase(phase2));
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
          //       new DynamicCount.GlobalReporting()));
          //phases.Add(new TypeDataDummyPhase("dynamiccount1-end-pipeline"));
          //

          if (StageControl.DynamicCountVirtualCalls) {
              phases.Add
                  (new DynamicCount
                      ("VirtualCallsEnd",
                       new DynamicCount.OpcodeFilter
                           (Operator.OpCodes.CallVirtual,
                            Operator.OpCodes.InterfaceCall),
                       new DynamicCount.SiteAndTargetReporting()));
          }

          if(StageControl.DynamicCountBoundsChecks) {
              phases.Add
                  (new DynamicCount
                   ("Vector Bounds Checks",
                    new DynamicCount.OpcodeFilter
                    (Operator.OpCodes.CheckVectorBounds,
                     Operator.OpCodes.CompareVectorBounds),
                    new DynamicCount.SiteReporting()));
              phases.Add(new TypeDataDummyPhase("dynamiccount2-end-pipeline"));
          }

          if(StageControl.DynamicCountNullChecks) {
              phases.Add
                  (new DynamicCount
                   ("Null Reference Checks",
                    new DynamicCount.OpcodeFilter
                    (Operator.OpCodes.CheckNonNull),
                    new DynamicCount.SiteReporting()));
              phases.Add(new TypeDataDummyPhase("dynamiccount3-end-pipeline"));

              phases.Add
                  (new DynamicCount
                   ("Null Check On Operator",
                    new DynamicCount.OpAttribsFilter
                    (OperatorAttributes.NonNullMemoryAccess),
                    new DynamicCount.SiteReporting()));
              phases.Add(new TypeDataDummyPhase("dynamiccount4-end-pipeline"));
          }

          if(StageControl.DynamicCountLoads) {
              phases.Add
                  (new DynamicCount
                   ("Loads",
                    new DynamicCount.OpcodeFilter
                    (Operator.OpCodes.ObjectField),
                    new DynamicCount.SiteReporting()));
              phases.Add(new TypeDataDummyPhase("dynamiccount5-end-pipeline"));
          }

          if(StageControl.DynamicCountStores) {
              phases.Add
                  (new DynamicCount
                   ("Stores",
                    new DynamicCount.OpcodeFilter
                    (Operator.OpCodes.StoreObjectField),
                    new DynamicCount.SiteReporting()));
              phases.Add(new TypeDataDummyPhase("dynamiccount6-end-pipeline"));
          }


          //
          //phases.Add
          //  (new DynamicCount
          //      ("ASCend",
          //       new DynamicCount.OpcodeFilter
          //           (Operator.OpCodes.CheckArrayStore,
          //            Operator.OpCodes.CheckVectorStore),
          //       new DynamicCount.SiteReporting()));
          //phases.Add(new TypeDataDummyPhase("dynamiccount7-end-pipeline"));
          //

          //
          //phases.Add
          //  (new DynamicCount
          //      ("WB",
          //       new DynamicCount.OpcodeFilter
          //           (Operator.OpCodes.LocWriteBarrier),
          //       new DynamicCount.GlobalReporting()));
          //phases.Add(new TypeDataDummyPhase("dynamiccount8-end-pipeline"));
          //

          if (StageControl.WholeProgram && StageControl.OptRuntimeData) {
              phases.Add(new RuntimeData());
          }

          if (StageControl.IrConvertArrayOpt) {
              phases.Add(new IrConvertArrayOpt());
          }

          if (StageControl.PtrAnalysis || StageControl.PtrAnalysisLate) {
              phases.Add(PtrTypeSimpleSystem.CreateAnalysis());
              phases.Add(PtrTypeHierarchySystem.CreateAnalysis());
              phases.Add(PtrTypeSetSystem.CreateAnalysis());
          }
        
#if LILC
          Verbosity.level = NoiseLevel.PerPhase;
          // The Lilc translation adds new types to typedata,
          // thus needs to happen before chooserep
          phases.Add(new Convert.ToMir(Convert.ToMir.Mask.Lilc));

          // inline polymorphic method just added by ToMir-Lilc
          if (StageControl.IrSimpleInliner) {
              phases.Add(new IrSimpleInliner(new IrInline(), false, true, 
                                             false, 0, 0, 0, true));
          }
          
          // Lower NewObject added by ToMir-Lilc and inlining
          phases.Add(new Convert.ToMir(Convert.ToMir.Mask.Constructor));
#endif

          // insert write barrier after chooserep so we know the size of
          // of objects. This is needed because we try to remove write
          // barrier when we store to the young generation, however,
          // big objects are in the old generation even though it is
          // newly created. Therefore, we need to know object size to
          // know if it is a big object.
          if (StageControl.InsertWriteBarrier ||
              StageControl.InsertAllBarrier ||
              StageControl.InsertCoCoBarrier) {
              if (StageControl.InsertCoCoBarrier) {
                  Util.Message(NoiseLevel.Silence,"Note: Using CoCo barriers!!");
                  phases.Add(new IrCoCoBarrier());
                  phases.Add(new IrJumpElim());
              } else if (StageControl.InsertAllBarrier) {
                  Util.Message(NoiseLevel.Silence,"Note: Using all-barrier");
                  phases.Add(new IrAllBarrier());
              } else {
                  Util.Message(NoiseLevel.Silence,"Note: Using ref write barrier");
                  phases.Add(new IrRefWriteBarrier());
              }
              phases.Add(new IrNoHeapAccess());
          }

          // convert type tests and sizeof effect to Mir
          Convert.ToMir.Mask typeMask = Convert.ToMir.Mask.Sizeof;

          if (!StageControl.TargetMdil) {
              typeMask |= Convert.ToMir.Mask.CheckCast;
          }

          Convert.ToMir.Mask typeMaskRC =
              Convert.ToMir.Mask.GetCurrentThread
              | Convert.ToMir.Mask.InitCopyBlock
              | Convert.ToMir.Mask.AllocStruct
              | Convert.ToMir.Mask.ConvertConvert;

          typeMaskRC |= Convert.ToMir.Mask.NewArray;
          if (!StageControl.TargetMdil) {
              typeMaskRC |= Convert.ToMir.Mask.ArrayTypeTest;

              if(StageControl.IrExposeAllocationCall) {
                  typeMaskRC |= Convert.ToMir.Mask.Allocation;
              }
          }

          bool isEitherRCCollector =
              (StageControl.GCType == StageControl.ReferenceCountingCollector)
              || (StageControl.GCType
                  == StageControl.DeferredReferenceCountingCollector);

          if (!isEitherRCCollector) {
              typeMask |= typeMaskRC;
          }
          if (StageControl.TypedReference
              && !StageControl.TargetMdil) {
              typeMask |= Convert.ToMir.Mask.TypedRef;
          }
          phases.Add(new Convert.ToMir(typeMask));

#if LILC
         if (StageControl.IrSimpleInliner) {
              phases.Add(new IrSimpleInliner(new IrInline(), false, true,
                                             true, 0, 0, 0, true));
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
  
          if (StageControl.IrTreeShake
              && StageControl.IrTreeShakeLate
              && !StageControl.BindMdil) {
              phases.Add(new IrTreeShake(typeData.EntryPoints,
                                         dynamicLoads,
                                         StageControl.WholeProgram,
                                         analysisRegistry,
                                         true));
          }
     }
#else         
          if (StageControl.IrSimpleInliner) {
              phases.Add(new IrSimpleInliner(new IrInline(), false, true,
                                             true, 0, 0, 0));
          }

          if (StageControl.TypeInitElim) {
              phases.Add(new IrTypeInitElim(analysisRegistry));
          }

          if (StageControl.IrRemoveDoubleCmp) {
              phases.Add(new IrCmpElim());
          }

          if (StageControl.IrArrayBaseLength) {
              phases.Add(new IrArrayBaseLength());
              phases.Add(new IrDeadAssignmentSimplePhase());
          }

          if (StageControl.IrInitTypeInliner
              && StageControl.LazyTypeInits
              && !StageControl.TargetMdil) {
              phases.Add(new IrInitTypeInliner(typeData, new IrInline()));
          }

          if (isEitherRCCollector) {
              AddRCPhases(phases, analysisRegistry);
          }

          if (isEitherRCCollector) {
              phases.Add(new Convert.ToMir(typeMaskRC));

              if (StageControl.IrSimpleInliner) {
                  if (StageControl.RCCollectorOptInlineRCUpdates) {
                      phases.Add(new IrSimpleInliner(new IrInline(),
                                                     true, false,
                                                     false));
                  } else {
                      phases.Add(new IrSimpleInliner(new IrInline(),
                                                     false, true, true,
                                                     0, 0, 0));
                  }
              }
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

          if (StageControl.IrTreeShake
              && StageControl.IrTreeShakeLate
              && !StageControl.BindMdil) {
              phases.Add(new IrTreeShake(typeData.EntryPoints,
                                         dynamicLoads,
                                         StageControl.WholeProgram,
                                         analysisRegistry,
                                         true));
          }
      }
#endif

      private static void AddRCPhases(Bartok.Ir.PhaseList phases,
                                      AnalysisRegistry ar) {
          bool isRC =
              StageControl.GCType ==
              StageControl.ReferenceCountingCollector;
          bool isDRC =
              StageControl.GCType ==
              StageControl.DeferredReferenceCountingCollector;

          Util.Assert(isRC || isDRC);
          String rcName = isRC ? "RC" : "DRC";

          if (StageControl.IrStructUnwrapping) {
              phases.Add(new IrStructUnwrap(RCAproposKind.Checker));
          }

          if (StageControl.RCCollectorShowStatistics) {
              String message = "Before " + rcName + " Update Injection";
              phases.Add(new IrBBStats(message));
          }
          MethodPhase insertionPhase = isRC ?
              (MethodPhase)new IrRCUpdate() : new IrDRCUpdate();
          phases.Add(insertionPhase);
          if (StageControl.RCCollectorShowStatistics) {
              String message = "After " + rcName + " Update Injection";
              phases.Add(new IrBBStats(message));
          }

          if (StageControl.RCCollectorOptImmortals) {
              phases.Add(new IrImmortalObjectRCUpdates());
          }

          if (isRC && StageControl.RCCollectorOptORoots) {
              phases.Add(new IrJumpElim());
              IrOverlookingRootsRCOpts orootsRCOpts =
                  new IrOverlookingRootsRCOpts(ar);
              phases.Add(orootsRCOpts);
          }

          if (StageControl.RCCollectorOptCoalescingUpdates) {
              phases.Add(new IrBBLocalCoalesceRCUpdates());
          }
          if (StageControl.RCCollectorOptStaticAcyclicRefTypeUpdates) {
              phases.Add(new IrAcyclicRefTypeRCUpdates());
          }
          if (StageControl.RCCollectorOptNonNullRCUpdates) {
              phases.Add(SSAPhase.NullCheckAnalysis());
          }
          if (StageControl.RCCollectorShowStatistics) {
              String message = "After " + rcName + " Optimizations";
              phases.Add(new IrBBStats(message));
          }

          phases.Add(new Convert.ToMir(Convert.ToMir.Mask.RCUpdate));
          if (StageControl.RCCollectorOptInlineRCUpdates) {
              phases.Add(new IrRCUpdateInliner());
          }
          phases.Add(new TypeDataDummyPhase("end-RC-end-pipeline"));
      }

      public static ArrayList fileNames;
      public static ArrayList mdilFileNames;
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

      private static String ComputeObjFileName(String outputName) {
          string objFileName;
          int len = outputName.Length;
          string desiredSuffix = StageControl.TargetMdil ? ".mdil" : ".obj";
          int suf = len-desiredSuffix.Length;
          if ((suf > 0)
              && (String.Compare(outputName.Substring(suf,desiredSuffix.Length),
                                 desiredSuffix, true)
                  == 0)) {
              objFileName = outputName;
          } else {
              objFileName = outputName + desiredSuffix;
          }
          return objFileName;
      }

      private static void ParseEnvVar(String envVar) {
#if !ON_SINGULARITY
          String envValue =
              Environment.GetEnvironmentVariable(envVar);
          if (envValue != null) {
              String[] envValueSplit =
                  Bartok.Utility.SharedUtil.ParseArgumentString(envValue);
              ParseStringArray(envValueSplit, false);
          }
#endif
      }

      // If isCmdLine is false, then the arguments are from an environment
      // variable.
      private static void LoadResponseFile(String filename, bool isCmdLine) {
          StreamReader sr = null;
          try {
              sr = new StreamReader(filename);
          } catch(IOException) {
              Util.UserError("Can't open response file {0}", filename);
          }

          String s;
          while((s = sr.ReadLine()) != null) {
              String[] args = Bartok.Utility.SharedUtil.sztoszv(s, true);
              ParseStringArray(args, isCmdLine);
          }
      }

      // If isCmdLine is false, then the arguments are from an environment
      // variable.
      private static void ParseStringArray(String[] args, bool isCmdLine) {
          int index = 0;
#if ON_SINGULARITY
          index = 1;
#endif
          while (index < args.Length) {
              String argument = args[index];
              if ((argument[0] == '-') || (argument[0] == '/')) {
                  String option = argument.Substring(1);
                  ProcessOption(argument, option, args, isCmdLine, ref index);
              } else if (argument[0] == '@') {
                  index++;
                  String responseFile = argument.Substring(1);
                  LoadResponseFile(responseFile, isCmdLine);
              } else {
                  index++;
                  fileNames.Add(argument);
              }
          }
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

          ParseEnvVar("BARTOK_COMPILER");
          ParseStringArray(args, true);

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
                Util.Error("Specified multiple output directories {0}",
                           new CollectionFormatter(outputDirNames));
                break;
            }
          }

          if (StageControl.BindMdil) {
              mdilFileNames = new ArrayList(fileNames.Count);
              foreach (String file in fileNames) {
                  mdilFileNames.Add(file + ".mdil");
              }
          }

          if (StageControl.TargetMdil) {
              StageControl.Finalizers = false;
              StageControl.OptLazyTypeInits = false;
              StageControl.IrInitStaticField = false;
              StageControl.ConvertArrayInitialization = false;
              StageControl.DirectWbInsertion = true;
          }

          FixDebugFlags();
          CreateMixinString();

          if(StageControl.EnableIrExposeAllocationCall
             && StageControl.DisableIrExposeAllocationCall) {
              Util.UserError("Conflicting flags EnableIrExposeAllocationCall "
                         + " and DisableIrExposeAllocationCall");
          }
          if(StageControl.EnableIrExposeAllocationCall) {
              StageControl.IrExposeAllocationCall = true;
          } else if(StageControl.DisableIrExposeAllocationCall) {
              StageControl.IrExposeAllocationCall = false;
          } else {
              StageControl.IrExposeAllocationCall =
#if PHXBRIDGE
                  //REVIEW: Need to see what CQ impact this has and fix it.
                  !StageControl.TargetMdil;
#else
                  StageControl.WholeProgram;
#endif
          }

          if((StageControl.GCType == StageControl.ReferenceCountingCollector)
             && StageControl.StructInheritance) {
              Util.UserError("RC Collector code has not been updated to "
                         + "handle struct inheritance");
          }
          if((StageControl.GCType ==
             StageControl.DeferredReferenceCountingCollector)
             && StageControl.StructInheritance) {
              Util.UserError("Deferred RC Collector code has not been "
                         + "updated to handle struct inheritance");
          }

          if(StageControl.TargetMdil) {
              if(!StageControl.GenObjFile) {
                  Util.UserError("MDIL code paths do not support asm emission");
              }
          }
          if(StageControl.TargetMdil || StageControl.BindMdil) {
              if(StageControl.LinkedStacks) {
                  Util.UserError("MDIL code paths do not support linked stacks");
              }
              if(StageControl.SymbolicDebug) {
                  Util.UserError("MDIL code paths do not support symbolic debugging");
              }
              if(StageControl.ProfileLirFunctions) {
                  Util.UserError("MDIL code paths do not support ProfileLirFunctions");
              }
          }

          int codeAlignment = StageControl.DefaultCodeAlignment;
          if (codeAlignment < 1 || codeAlignment > 16 ||
              Util.GetUnsignedPowerOf2((ulong) codeAlignment, 12) == -1) {
                  Util.UserError("Default code alignment must be a power of 2 between 1 and 16");
          }
      }

      private static void FixDebugFlags() {
          if (StageControl.SymbolicDebug) {
              if (StageControl.WholeProgram) {
                  // use shortened name for types
                  StageControl.FullSymName = false;
              } else {
                  // when not whole program, can't do shorten
                  // name since we can't detect name clashing
                  // between different obj files.
                  StageControl.FullSymName = true;
              }
          }
      }

      private static void CreateMixinString() {
          switch (StageControl.Allocator) {
            case StageControl.BumpAllocator: {
                StageControl.mixinConditionals += ",BumpAllocator";
                break;
            }
            case StageControl.FirstFitAllocator: {
                StageControl.mixinConditionals += ",FirstFitAllocator";
                break;
            }
            case StageControl.SegregatedFreeList: {
                StageControl.mixinConditionals += ",SegregatedFreeList";
                break;
            }
            default: {
                Util.Abort("Unsupported allocator type");
                break;
            }
          }
          if (StageControl.AllThreadMixins) {
              // To avoid having multiple halclass files for different
              // allocators, simply include all the allocator structs in
              // the thread objects (for now). --Bjarne
              StageControl.mixinConditionals += ",AllThreadMixins";
          }

          switch (StageControl.BumpAllocatorClear) {
            case StageControl.BumpAllocatorPageClear: {
                StageControl.mixinConditionals +=
                    ",BumpAllocatorPageClear";
                break;
            }
            case StageControl.BumpAllocatorObjectClear: {
                StageControl.mixinConditionals +=
                    ",BumpAllocatorObjectClear";
                break;
            }
            case StageControl.BumpAllocatorCacheClear: {
                StageControl.mixinConditionals +=
                    ",BumpAllocatorCacheClear";
                break;
            }
            default: {
                Util.NotReached();
                break;
            }
          }

          switch (StageControl.GCType) {
            case StageControl.ReferenceCountingCollector: {
                StageControl.mixinConditionals += ",ReferenceCountingGC";
                if (StageControl.RCCollectorVerifyRefCounts) {
                    StageControl.mixinConditionals +=
                        ",ReferenceCountingGCVerification";
                }
                break;
            }
            case StageControl.DeferredReferenceCountingCollector: {
                StageControl.mixinConditionals +=
                    ",DeferredReferenceCountingGC";
                if (StageControl.RCCollectorVerifyRefCounts) {
                  StageControl.mixinConditionals +=
                      ",DeferredReferenceCountingGCVerification";
                }
                break;
            }
            case StageControl.ConcurrentMSCollector: {
                StageControl.mixinConditionals += ",ConcurrentMSGC";
                break;
            }
            case StageControl.CoCoMSCollector: {
                StageControl.mixinConditionals += ",CoCo,ConcurrentMSGC";
                break;
            }
          }

          if (StageControl.InsertWriteBarrier == true) {
              switch (StageControl.RemSet) {
                case StageControl.RemSetSSB: {
                    StageControl.mixinConditionals += ",SSB";
                    break;
                }
              }
          }

          if (StageControl.GCEnableProfiling) {
              StageControl.mixinConditionals += ",GCProfiling";
          }

          switch (StageControl.ObjectHeaderKind) {
            case StageControl.ObjectHeaderDefault: {
                StageControl.mixinConditionals += ",ObjectHeaderDefault";
                break;
            }
            case StageControl.ObjectHeaderPostRC: {
                StageControl.mixinConditionals += ",ObjectHeaderPostRC";
                break;
            }
            default: {
                Util.InternalError("Unknown StageControl.ObjectHeaderKind");
                break;
            }
          }

          switch (StageControl.TargetArch) {
            case StageControl.X86: {
                StageControl.mixinConditionals += ",X86";
                break;
            }
            case StageControl.X64: {
                StageControl.mixinConditionals += ",X64";
                break;
            }
            case StageControl.ARM: {
                StageControl.mixinConditionals += ",ARM";
                break;
            }
            default: {
                Util.InternalError("Unknown StageControl.TargetArch value");
                break;
            }
          }
      }

      // If isCmdLine is false, then the arguments are from an environment
      // variable.
      private static void ProcessOption(String argument, String option,
                                        String[] args, bool isCmdLine,
                                        ref int index) {
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
          } else if (IsOption(args, option, loweredOption, "dynamicload:",
                              ref index, out optionValue)) {
              AddSemicolonDelimitedNames(dynamicLoads, optionValue);
          } else if (IsOption(args, option, loweredOption, "features:",
                              ref index, out optionValue)) {
              StageControl.mixinConditionals += "," + optionValue;
          } else if (IsOption(args, option, loweredOption, "verbosity:",
                              ref index, out optionValue)) {
              Verbosity.FromString(optionValue);
          } else if (IsOption(args, option, loweredOption,
                              "heapsizeconfigurable",
                              ref index, out optionValue)) {
              StageControl.HeapSizeConfigurable = true;
          } else if (IsOption(args, option, loweredOption, "marksweepgc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.MarkSweepCollector;
              StageControl.GCLargeObjectSize = 2040;
              StageControl.InsertWriteBarrier = false;
              StageControl.Allocator = StageControl.SegregatedFreeList;
          } else if (IsOption(args, option, loweredOption, "tablemarksweepgc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.SimpleMarkSweepCollector;
              StageControl.GCLargeObjectSize = 2040;
              StageControl.InsertWriteBarrier = false;
              StageControl.Allocator = StageControl.LocalCacheAllocator;
          } else if (IsOption(args, option, loweredOption, "semispacegc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.SemispaceCollector;
              StageControl.InsertWriteBarrier = true;
              StageControl.Allocator = StageControl.BumpAllocator;
          } else if (IsOption(args, option, loweredOption, "slidinggc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.SlidingCollector;
              StageControl.InsertWriteBarrier = true;
              StageControl.Allocator = StageControl.BumpAllocator;
          } else if (IsOption(args, option, loweredOption, "adaptivecopyinggc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.AdaptiveCopyingCollector;
              StageControl.InsertWriteBarrier = true;
              StageControl.Allocator = StageControl.BumpAllocator;
          } else if (IsOption(args, option, loweredOption,
                              "referencecountinggc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.ReferenceCountingCollector;
              StageControl.InsertWriteBarrier = false;
              StageControl.Allocator = StageControl.SegregatedFreeList;
              StageControl.GCInlineAllocations = false;
              if (StageControl.ObjectHeaderKind == StageControl.ObjectHeaderDefault) {
                  StageControl.ObjectHeaderKind =
                      StageControl.ObjectHeaderPostRC;
              }
              if (StageControl.RCCollectorVerifyRefCounts) {
                  StageControl.UseVTableBits = true;
              }
          } else if (IsOption
                     (args, option, loweredOption, "deferredreferencecountinggc",
                      ref index, out optionValue)) {

              StageControl.GCType = StageControl.DeferredReferenceCountingCollector;
              StageControl.InsertWriteBarrier = false;
              StageControl.Allocator = StageControl.SegregatedFreeList;
              StageControl.GCInlineAllocations = false;
              if (StageControl.ObjectHeaderKind == StageControl.ObjectHeaderDefault) {
                  StageControl.ObjectHeaderKind =
                      StageControl.ObjectHeaderPostRC;
              }
              if (StageControl.RCCollectorVerifyRefCounts) {
                  StageControl.UseVTableBits = true;
              }
          } else if (IsOption(args, option, loweredOption, "concurrentmsgc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.ConcurrentMSCollector;
              StageControl.GCLargeObjectSize = 2040;
              StageControl.Wb = StageControl.WbCMS;
              StageControl.GCInlineAllocations = false;
              StageControl.Allocator = StageControl.SegregatedFreeList;
              StageControl.PreWriteBarrier = true;
              StageControl.InsertWriteBarrier = true;
              StageControl.GCInlineWriteBarrier = false;
              StageControl.GCWriteBarrierTracksStaticFields = true;
          } else if (IsOption(args, option, loweredOption, "cocomsgc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.CoCoMSCollector;
              StageControl.GCLargeObjectSize = 2040;
              StageControl.Wb = StageControl.WbCoCoMS;
              StageControl.GCInlineAllocations = false;
              StageControl.Allocator = StageControl.SegregatedFreeList;
              StageControl.PreWriteBarrier = true;
              StageControl.InsertWriteBarrier = true;
              StageControl.InsertCoCoBarrier = true;
              StageControl.GCInlineWriteBarrier = true;
              StageControl.GCWriteBarrierTracksStaticFields = true;
              StageControl.IgnorePreInitRefCounts = true;
              // HACKHACK: allowing Bartok+CoCo to build on my computer!
              // without running out of physical memory!
              //StageControl.IrSimpleInliner = false;
          } else if (IsOption(args, option, loweredOption, "nullgc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.NullCollector;
              StageControl.InsertWriteBarrier = false;
              StageControl.Allocator = StageControl.BumpAllocator;
          } else if (IsOption(args, option, loweredOption, "atomicrcgc",
                              ref index, out optionValue)) {
              StageControl.GCType = StageControl.AtomicRCCollector;
              StageControl.GCLargeObjectSize = 2040;
              StageControl.Wb = StageControl.WbARC;
              StageControl.GCInlineAllocations = false;
              StageControl.Allocator = StageControl.SegregatedFreeList;
              StageControl.InsertWriteBarrier = true;
              StageControl.GCInlineWriteBarrier = false;
              StageControl.GCWriteBarrierTracksStaticFields = true;
          } else if (IsOption(args, option, loweredOption, "minopt",
                              ref index, out optionValue)) {
              StageControl.SsaOpts = false;
              StageControl.DevirtualizeCall = false;
              StageControl.IrFindConcrete = false;
              StageControl.IrSimpleInliner = false;
              StageControl.IrTypeTestElim = false;
              StageControl.IrTypeTestElimPunt = false;

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
              StageControl.IrFindConcrete = false;
              StageControl.IrInitStaticField = false;
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
              StageControl.MasmCompatibleSymbols = false;
              StageControl.StrictEcma = true;
              StageControl.CustomAllocatorTypes = true;
              StageControl.SurrogateBoxing = true;
              StageControl.StructInheritance = true;
              StageControl.IrTreeShakeCreatePointedToStructs = true;
              StageControl.IrTreeShakeLate = false; // not tested
              StageControl.TypeInitRemoveEmptyCctors = false; // not tested
              StageControl.CheckNoHeapAllocation = true;
              StageControl.MakeNativeHeadersUsableForSingularityLoader = true;
              StageControl.IncludeBartokFilterInXData = false;
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
              Bartok.MSIL.MetaDataUtil.Target64Bit = false;
          } else if (IsOption(args, option, loweredOption, "x64",
                              ref index, out optionValue)) {
              StageControl.TargetArch = StageControl.X64;
              StageControl.Target64Bit = true;
              Bartok.MSIL.MetaDataUtil.Target64Bit = true;
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
          } else if (isCmdLine
                     && StageControl.SetOptionFromCommandLine(args, option,
                                                              loweredOption,
                                                              ref index)) {
              // continue
          } else if (!isCmdLine
              && StageControl.SetOptionFromEnvVar(args, option,
                                                  loweredOption,
                                                  ref index)) {
              // continue
          } else if (loweredOption.StartsWith("stagecontrol")) {
              Util.UserError("/stagecontrol no longer supported; "
                               + "use the option directly");
          } else {
              Util.UserError("Unknown option: " + option);
          }
      }

      private static bool IsOption(String[] args,
                                   String option, String loweredOption,
                                   String possibleOptionName,
                                   ref int index, out String optionValue) {
          return StageControl.IsOption(args, option, loweredOption,
                                       possibleOptionName,
                                       ref index, out optionValue);
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
          Util.Message(true,
@"Usage:
    bartok [options] files

Bartok main options (case insensitive):
    @<file>                            options response file
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
    /dynamicload:<typename>            make type available for dynamic loading
    /features:<???>                    << TODO >>
    /verbosity:<noiselevel>            set output level {Silence,PerPhase,
                                        PerClass,PerMethod,PerBlock,
                                        PerInstruction} (defaults to PerPhase)
    /marksweepgc                       compile for mark-sweep collector
    /semispacegc                       compile for semispace collector
    /slidinggc                         compile for sliding collector
    /adaptivecopyinggc                 compile for semispace-sliding hybrid
                                        collector
    /referencecountinggc               compile for reference counting collector
    /deferredreferencecountinggc       compile for deferred reference counting
                                        collector
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

      public void Error(String msg)
      {
          Util.Error(msg);
      }

      public void Error(String format, params Object[] objs)
      {
          Util.Error(format, objs);
      }

      public void ErrorDetail(String msg)
      {
          Util.ErrorDetail(msg);
      }

      public void Warn(String msg)
      {
          Util.Warn(msg);
      }

      public void Warn(String format, params Object[] objs)
      {
          Util.Warn(format, objs);
      }

      public void WarnDetail(String msg)
      {
          Util.WarnDetail(msg);
      }

      public void Message(String msg)
      {
          Util.Message(msg);
      }
  }
}
