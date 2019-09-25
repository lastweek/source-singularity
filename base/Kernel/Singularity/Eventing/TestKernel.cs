////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TestKernel.cs
//
//


using System;
using System.Threading;
using System.Runtime.CompilerServices;

using Microsoft.Singularity;
using Microsoft.Singularity.V1.Services;    
using Microsoft.Singularity.Eventing;
using System.Collections;

namespace Microsoft.Singularity.Eventing
{
    [CLSCompliant(false)]
    public class TestKernelLogging
    {

        [CLSCompliant(false)]
        static internal bool ActiveEntryDelegate(UIntPtr sourceHandle,
                                                    int index,
                                                    EventDescriptor descriptor,
                                                    QueryBuffer entryBuffer,
                                                    ref EnumerationContext context)
        {

            Console.Write("{0:d5}", index);
            descriptor.EnumerateFields(new QueryFieldDelegate(ActiveFieldDelegate), entryBuffer, ref context);
            Console.WriteLine("");
            return true;
        }
        
        static internal bool TableHeadDelegate(FieldDescriptor fieldDescriptor, 
                                                 object obj,
                                                ref EnumerationContext ctx)
        {
            Console.Write("    {0}", fieldDescriptor.Name);
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

            if (descriptor != null) {
                Console.WriteLine("Source: \"{0}\". {1} entries of type {2}", 
                    bufferName, count, descriptor.EventName);
                
                Console.Write("Index");
                descriptor.EnumerateFields(new QueryFieldDelegate(TableHeadDelegate), null, ref context);
                Console.WriteLine("");
                Console.Write("-----");

                for (int i = 0; i < descriptor.GetFieldsCount(); i++) {
                    Console.Write("----------");
                }
                Console.WriteLine("");
            } else {
                    Console.WriteLine("Source Handle={0}, Storage={1}, type={2}, name={3}, count={4}", 
                        sourceHandle, storageHandle, eventType, bufferName, count);
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

            if ((currentEntry != null) && (buffer != null)) {

                currentEntry.EnumerateFields(new QueryFieldDelegate(fieldDelegate), buffer, ref context);
            }

            return true;
        }

        public static void ListActiveSources()
        {
            Controller hostController = Controller.GetLocalController();
            EnumerationContext ctx = new EnumerationContext();

            if ((hostController == null) || (ctx == null)) {
                return;
            }

            hostController.EnumerateActiveSources(new QuerySourceDelegate(SourceDelegate),
                                                  new ActiveSourceEntryDelegate(ActiveEntryDelegate),
                                                  new QueryEntryDelegate(EntryDelegate),
                                                  0,
                                                  ref ctx);
        }
        
        public static void TestAllCases()
        {
            ListActiveSources();

        }
    }    
}


