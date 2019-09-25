// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

using System;
using System.Collections;

namespace NetStack.Runtime
{
    ///
    // Each protocol (upon initialization) should
    // register itself as a specific packet type handler.
    // The packet type must be one of: ProtocolCode
    // types (a TCP has nothing to do with this list...)
    // Notice: the ALL code is used for receiving all
    // incoming traffic.
    // 
    public class PacketTypes
    {
        public const ushort IP    = 0x0800;
        public const ushort ARP   = 0x0806;
        public const ushort RARP  = 0x8035;
        public const ushort PAUSE = 0x8808;
        public const ushort MAP   = 0x4934;
        public const ushort NLB   = 0x886F;             // Microsoft
        public const ushort LOOP  = 0x0060;             // Loopback
        public const ushort ALL   = 0xFFFF;             // All packets!

        private const int MaxTypes   = 16;
        private ushort [] key        = new ushort [MaxTypes];
        private IProtocol [] handler = new IProtocol[MaxTypes];
        private int registered = 0;

        // registers a new type's handler
        // return true if succeeded.
        public bool RegisterTypeHandler(ushort type, IProtocol protocol)
        {
            if (registered == MaxTypes) {
                Core.Log("Out of type handler space.");
                return false;
            }

            if (GetHandler(type) != null) {
                Core.Log("Handler already registered.");
                return false;
            }

            key[registered] = type;
            handler[registered] = protocol;
            registered++;
            return true;
        }

        public IProtocol GetHandler(ushort type)
        {
            for (int i = 0; i < registered; i++) {
                if (key[i] == type) {
                    return handler[i];
                }
            }
            return null;
        }
    }
}
