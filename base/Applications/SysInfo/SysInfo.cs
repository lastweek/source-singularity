////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Utility program to query the system information
//
using System;
using System.Diagnostics;
using System.Net.IP;
using System.Text.RegularExpressions;

using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using Microsoft.SingSharp;
using NetStack.Contracts;
using NetStack.Channels.Public;

using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Eventing;

[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{

    [ConsoleCategory(HelpMessage="Test utility application", DefaultAction=true)]
    internal class DefaultConfig
    {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter( "S", Mandatory=false, HelpMessage="Source filter")]
        internal string SourceFilter;

        [BoolParameter( "a", Default=false, HelpMessage="display all events")]
        internal bool DumpAll;

        reflective internal DefaultConfig();

        internal int AppMain() {
            return  SysInfo.DefaultMain(this);
        }
    }

    public class SysInfo
    {

        static string SourceFilter;
        static bool DumpAll;

        [CLSCompliant(false)]
        static internal bool ActiveEntryDelegate(UIntPtr sourceHandle,
                                                    int index,
                                                    EventDescriptor descriptor,
                                                    QueryBuffer entryBuffer,
                                                    ref EnumerationContext context)
        {
            if (!DumpAll) {

                return false;
            }

            if (descriptor != null) {
                Console.Write("{0:d5}", index);
                descriptor.EnumerateFields(new QueryFieldDelegate(ActiveFieldDelegate), entryBuffer, ref context);
                Console.WriteLine("");
            }

            return true;
        }
        
        static internal bool TableHeadDelegate(FieldDescriptor fieldDescriptor, 
                                                 object obj,
                                                ref EnumerationContext ctx)
        {
            if (fieldDescriptor != null) {
                Console.Write("    {0}", fieldDescriptor.Name);
            }
            return true;
        }

        static internal bool ActiveFieldDelegate(FieldDescriptor fieldDescriptor, 
                                                 object obj,
                                                 ref EnumerationContext ctx)
        {
            if (obj != null) {

                Console.Write("    {0}", obj.ToString());
            }
            return true;
        }

        static internal bool SourceDelegate(UIntPtr sourceHandle,
                                            UIntPtr storageHandle,
                                            UIntPtr eventType,
                                            UInt16 count,
                                            string bufferName,
                                            EventDescriptor descriptor,
                                            ref EnumerationContext context)
        {
            if (SourceFilter != null) {

                if (!Regex.IsMatch(bufferName, SourceFilter)) {

                    return true;
                }
            }
            
            if (descriptor != null) {
                Console.WriteLine("Source: \"{0}\". {1} entries of type {2}", 
                    bufferName, count, descriptor.GetName());

                if (DumpAll) {
                    Console.Write("Index");
                    descriptor.EnumerateFields(new QueryFieldDelegate(TableHeadDelegate), null, ref context);
                    Console.WriteLine("");
                    Console.Write("-----");

                    for (int i = 0; i < descriptor.GetFieldsCount(); i++) {
                        Console.Write("----------");
                    }
                    Console.WriteLine("");
                }

            } else {
                    Console.WriteLine("Source: \"{0}\". Storage handle ={1}", 
                                      bufferName, sourceHandle);
            }
            return true;
        }

        static internal bool fieldDelegate(FieldDescriptor fieldDescriptor, 
                                           object obj,
                                           ref EnumerationContext context)
        {
            if ((fieldDescriptor != null) && (obj != null)) {
                
                Console.WriteLine("    {0}:{1}:{2} = {3}", 
                                          fieldDescriptor.Offset, 
                                          fieldDescriptor.GetTypeName(), 
                                          fieldDescriptor.Name,
                                          obj.ToString());
            }

            return true;
        }


        static internal bool EntryDelegate(EventDescriptor currentEntry, 
                                           QueryBuffer buffer, 
                                           ref EnumerationContext context)
        {
            if (!DumpAll) {

                return false;
            }

            if ((currentEntry != null) && (buffer != null)) {

                currentEntry.EnumerateFields(new QueryFieldDelegate(fieldDelegate), buffer, ref context);
            }

            return true;
        }

        public static void ListActiveSources()
        {
            Controller hostController = Controller.GetSystemController();
            EnumerationContext ctx = new EnumerationContext();

            if ((hostController == null) || (ctx == null)) {
                return;
            }

            LoadEventTypes(hostController);

            hostController.EnumerateActiveSources(
                new QuerySourceDelegate(SourceDelegate),
                new ActiveSourceEntryDelegate(ActiveEntryDelegate),
                new QueryEntryDelegate(EntryDelegate),
                0,
                ref ctx);
        }

        public static void LoadEventTypes(Controller! hostController)
        {
            int currentSize = 100;
            UIntPtr [] eventTypeArray = new UIntPtr[currentSize];

            if (eventTypeArray != null) {

                QuerySession.FlushCaches();
                
                int eventTypeCount = hostController.QueryEventTypeList(eventTypeArray, currentSize);

                while (eventTypeCount > currentSize) {

                    eventTypeArray = new UIntPtr[eventTypeCount];
                    eventTypeCount = hostController.QueryEventTypeList(eventTypeArray, currentSize);
                }

                for (int i = 0; i < eventTypeCount; i++) {

                    
                    EventDescriptor descriptor = QuerySession.GetEventDescriptor(hostController, 
                                                                                 eventTypeArray[i]);

                    if (descriptor != null) {
                        
                        Console.WriteLine("Event type \"{0}\"", descriptor.GetName());
                    }

                }
            }
        }
        

        internal static int DefaultMain(DefaultConfig! config)
        {
            SourceFilter = config.SourceFilter;
            DumpAll = config.DumpAll;
            
            ListActiveSources();
            return 0; 
        }
    } // end class SysInfo
}
