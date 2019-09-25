///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Libraries\Services\Helpers.cs
//
//  Note:   
//
using System;
using System.IO;
using System.Text;

namespace FileSystem.Utils
{
    public static class DiskSizeUtils
    {
        internal struct Quantity
        {
            internal ulong Unit;
            internal string! Suffix;

            internal Quantity(ulong u, string! s)
            {
                Unit = u;
                Suffix = s;
            }

            internal static readonly Quantity[]! KnownDisplayQuantities = new Quantity[] {
                new Quantity(1152921504606846976, "EiB"),
                new Quantity(1125899906842624, "PiB"),
                new Quantity(1099511627776, "TiB"),
                new Quantity(1073741824, "GiB"),
                new Quantity(1048576, "MiB"),
                new Quantity(1024, "KiB"),
            };

            internal static readonly Quantity[]! KnownParseQuantities = new Quantity[] {
                // Binary units
                new Quantity(1152921504606846976, "EiB"),
                new Quantity(1125899906842624, "PiB"),
                new Quantity(1099511627776, "TiB"),
                new Quantity(1073741824, "GiB"),
                new Quantity(1048576, "MiB"),
                new Quantity(1024, "KiB"),

                // Metric units
                new Quantity(1000000000000000000, "EB"),
                new Quantity(1000000000000000, "PB"),
                new Quantity(1000000000000, "TB"),
                new Quantity(1000000000, "GB"),
                new Quantity(1000000, "MB"),
                new Quantity(1000, "KB"),

                // Use binary units for the casual ones like "10K"
                new Quantity(1152921504606846976, "E"),
                new Quantity(1125899906842624, "P"),
                new Quantity(1099511627776, "T"),
                new Quantity(1073741824, "G"),
                new Quantity(1048576, "M"),
                new Quantity(1024, "K"),

                // Binary units for bits, converted to bytes
                new Quantity(144115188075855872, "Eb"),
                new Quantity(140737488355328, "Pb"),
                new Quantity(137438953472, "Tb"),
                new Quantity(134217728, "Gb"),
                new Quantity(131072, "Mb"),
                new Quantity(128, "Kb"),

                new Quantity(1, "B"),
                new Quantity(1, "")
            };
        }

        public static string GetPrettySizeString(ulong diskSize)
        {
            string suffix = "B";
            ulong divisor = 1;

            Quantity[] quantities = Quantity.KnownDisplayQuantities;

            for (int i = 0; i < quantities.Length; i++) {
                if (diskSize >= 1 * quantities[i].Unit) {
                    divisor = quantities[i].Unit;
                    suffix = quantities[i].Suffix;
                    break;
                }
            }
            return String.Format("{0:F0} {1}",
                                 (float)diskSize / (float)divisor, suffix);
        }

        public static ulong ParsePrettySizeString(string! diskSizeStr)
        {
            ulong multiplier = 1, numUnits;

            Quantity[] quantities = Quantity.KnownParseQuantities;

            for (int i = 0; i < quantities.Length; i++) {
                if (diskSizeStr.EndsWith(quantities[i].Suffix)) {

                    // Would use TryParse() if we had .NET Framework 2.0
                    try {
                        numUnits = ulong.Parse(
                            diskSizeStr.Substring(0, diskSizeStr.Length -
                                                     quantities[i].Suffix.Length));
                    }
                    catch (FormatException) {
                        continue;
                    }

                    multiplier = quantities[i].Unit;

                    return multiplier * numUnits;
                }
            }

            throw new FormatException();
        }
    }
}
