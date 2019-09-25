///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Resources.cs
//

using System;
using System.Collections;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity.Loader;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Hal;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced in halkd.cpp")]
    public class Resources
    {
        static public int GetWarmBootCount()
        {
            return Platform.ThePlatform.BootCount;
        }

        public struct PnpBiosInfo
        {
            public IoMemory     pnpRegion;
            public IoPort       isaReadPort;
            public uint         isaCsns;
        }

        static public PnpBiosInfo GetPnpBiosInfo()
        {
            Platform bi = Platform.ThePlatform;
            PnpBiosInfo pbi = new PnpBiosInfo();

            if (bi.PnpNodesAddr32 != UIntPtr.Zero) {
                Tracing.Log(Tracing.Debug, "PnpBiosRegion {0:x8}..{1:x8}",
                            bi.PnpNodesAddr32, bi.PnpNodesAddr32 + bi.PnpNodesSize32);
                pbi.pnpRegion = IoMemory.MapPhysicalMemory(
                    bi.PnpNodesAddr32, bi.PnpNodesSize32, true, false);
            }

            pbi.isaReadPort = new IoPort((ushort)bi.IsaReadPort, 1, Access.Read);;
            pbi.isaCsns = bi.IsaCsns;
            return pbi;
        }

        static public uint GetPciNumberOfBuses()
        {
            Platform bi = Platform.ThePlatform;

            return (uint)bi.PciBiosCX + 1;
        }

        static private unsafe FileImage GetLoadedFileImage(int image)
        {
            Platform bi = Platform.ThePlatform;
            if (image < bi.FileImageTableEntries) {
                FileImage* fi = (FileImage*) bi.FileImageTableBase32; //.ToPointer();
                return *(fi + image);
            }
            return new FileImage(UIntPtr.Zero, 0);
        }

        static public IoMemory GetLoadedImageMemory(int image)
        {
            FileImage fileImage = GetLoadedFileImage(image);
            if (fileImage.Address != UIntPtr.Zero) {
                return IoMemory.MapPhysicalMemory(fileImage.Address, fileImage.Size,
                                                  true, false);
            }
            return null;
        }

        public static IoMemory GetSystemManifest()
        {
            return Resources.GetLoadedImageMemory(1);
        }
    }
}
