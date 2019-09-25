////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;

namespace Microsoft.Singularity.Applications
{
    public class MathTest
    {
        private static void spec_zipf_setup(int size, double Z)
        {
            Console.WriteLine("spec_zipf_setup size={0}",size);
            for (int i = 1; i <= size; i++) {
                // compute zipf values for samples 1-n.

                double d0 = 1.0 / (double)i;
                double d1 = Math.Pow(d0, Z);
                Console.WriteLine("pow({0,9:f6}, {1,9:f6})={2,9:f6}", d0, Z, d1);
            }
        }

        //[ShellCommand("mathtest", "Run simple math tests.")]
        public static int Main()
        {
            double x1 = Math.PI / 4;
            double x2 = 0.50;

            Console.WriteLine("Asin ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Asin(x1), 0.903339);
            Console.WriteLine("Acos ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Acos(x1), 0.667457);
            Console.WriteLine("Sin  ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Sin(x1), 0.707107);
            Console.WriteLine("Cos  ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Cos(x1), 0.707107);
            Console.WriteLine("Tan  ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Tan(x1), 1.000000);
            Console.WriteLine("Atan ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Atan(x1), 0.665774);
            Console.WriteLine("Atan2({0,9:f6}, {1,9:f6}) = {2,9:f6} : {3,9:f6}",
                              x1, x2, Math.Atan2(x1, x2), 1.003885);
            Console.WriteLine("Abs  ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Abs(x1), 0.785398);
            Console.WriteLine("Sqrt ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Sqrt(x1), 0.886227);
            Console.WriteLine("Log  ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Log(x1), -0.241564);
            Console.WriteLine("Log10({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Log10(x1), -0.104910);
            Console.WriteLine("Pow  ({0,9:f6}, {1,9:f6}) = {2,9:f6} : {3,9:f6}",
                              x1, x2, Math.Pow(x1, x2), 0.886227);
            Console.WriteLine("Fmod ({0,9:f6}, {1,9:f6}) = {2,9:f6} : {3,9:f6}",
                              x1, x2, Math.Mod(x1, x2), 0.285398);
            Console.WriteLine("Floor({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Floor(x1), 0.000000);
            Console.WriteLine("Ceil ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Ceiling(x1), 1.000000);
            Console.WriteLine("Round({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Round(x1), 1.000000);
            Console.WriteLine("Round({0,9:f6}, {1})         = {2,9:f6} : {3,9:f6}",
                              (double)Math.PI, 2, Math.Round(Math.PI, 2), 3.14, 999, 99);
            Console.WriteLine("Sinh ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Sinh(x1), 0.868671);
            Console.WriteLine("Tanh ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Tanh(x1), 0.655794);
            Console.WriteLine("Cosh ({0,9:f6})            = {1,9:f6} : {2,9:f6}",
                              x1, Math.Cosh(x1), 1.324609);

            spec_zipf_setup(24, 1.0);

            return 0;
        }
    }
}
