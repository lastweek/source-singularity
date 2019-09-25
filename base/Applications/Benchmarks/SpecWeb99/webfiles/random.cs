#define NO_ZIPF_SPIKE

//
//  (C)1997 Standard Performance Evaluation Corporation (SPEC)
//
//  This suite contains code acquired from several sources who
//  understand and agree with SPEC's goal of creating fair and
//  objective benchmarks to measure computer performance.
//
//  This copyright notice is placed here only to protect SPEC in the
//  event the source is misused in any manner that is contrary to
//  the spirit, the goals and the intent of SPEC.
//
//  The source code is provided to the user or company under the
//  license agreement for the SPEC Benchmark Suite for this suite.
// 

//////////////////////////////////////////////////////////////////
//                                                               *
//  Copyright 1991,1992  Legato Systems, Inc.                *
//  Copyright 1991,1992  Auspex Systems, Inc.                *
//  Copyright 1991,1992  Data General Corporation            *
//  Copyright 1991,1992  Digital Equipment Corporation       *
//  Copyright 1991,1992  Interphase Corporation              *
//  Copyright 1991,1992  Sun Microsystems, Inc.              *
//                                                               *
/////////////////////////////////////////////////////////////////  

//
// ---------------------- laddis_c_rnd.c ---------------------
//
//      Random number generator.
//
//.Exported_routines
//      double  Spec_random  (RandomState *theState);
//      long    Spec_nrandom (RandomState *theState);
//      void    Spec_srandom (RandomState *theState, int seed);
//
//.Local_routines
//      None
//
//.Revision_History
//  06-Nov-05           Convert to Sing#
//  24-May-97           Re-write to make thread-safe
//  28-Nov-91           ANSI C
//  01-Aug-91           laddis_srandom() and laddis_random()
//                      now use spec_srand() and spec_rand()
//                      instead of srandom() and random().
//  17-Apr-91           Created.
// 

//
// Here's the source for the random number generator that SPEC uses.
// The function to be called is "spec_rand" which returns an integer
// between 1 and MAX_INT-1.
//
// 


//////////////////////////////////////////////////////////////////////////////
// UNIFORM Distribution                                                      *
/////////////////////////////////////////////////////////////////////////////  
using System;
using Singularity.Application.SPECWeb99;

//using Microsoft.Singularity.Math;
//using Microsoft.Singularity;
//using Microsoft.Singularity.Directory;
//using Microsoft.Singularity.V1.Services;
//using Microsoft.Singularity.Io;
#if SINGULARITY
using Microsoft.Contracts;
#endif

namespace Singularity.Application.SPECWeb99.WebFiles
{
    public class Random
    {
        public const int A_MULTIPLIER = 16807;
        public const int M_MODULUS    = 2147483647; // (2**31)-1   
        public const int Q_QUOTIENT   = 127773;     // 2147483647 / 16807   
        public const int R_REMAINDER  = 2836;       // 2147483647 % 16807   
        //
        //Compute the next random number.
          //
        public class RandomState
        {
            public int val;

            public RandomState(int val)
            {
                this.val = val;
            }
        }

        public class ZipfState
        {
            public RandomState rstate;
            public int size;
            public double []table;

#if SINGULARITY
            [NotDelayed]
#endif
            public ZipfState (RandomState rstate, int size)
            {
                this.size   = size;
                this.rstate = rstate;
                table= new double[size+1];
                if (table == null) {
                    Console.WriteLine("ZipfState constructor: can't create {0} entries for table",
                                       size+1);
                }
            }
        } // ZipfState


#if STATIC_NORMAL_DIST
        public class NormalState {
            public RandomState rstate;
            public int size;
            public int []table;
        };
#else
        public class NormalState {
            public RandomState rstate;
            public double mean, stddev, y2;
            public bool use_last;
        };
#endif

        public double Spec_random(RandomState /*!*/ theState)
        // See "Random Number Generators: Good Ones Are Hard To Find",   
        //     Park & Miller, CACM 31#10 October 1988 pages 1192-1201.   
        ///////////////////////////////////////////////////////////  
        // THIS IMPLEMENTATION REQUIRES AT LEAST 32 BIT INTEGERS !   
        ///////////////////////////////////////////////////////////  
        {
            int lo;
            int hi;
            int test;

            hi = theState.val / Q_QUOTIENT;
            lo = theState.val % Q_QUOTIENT;
            test = A_MULTIPLIER * lo - R_REMAINDER * hi;
            if (test > 0) {
                theState.val = test;
            }
            else {
                theState.val = test + M_MODULUS;
            }
            return((float) theState.val / M_MODULUS);
        }

        //
        //Seed the random number generator.
        //
        public void Spec_srandom( RandomState /*!*/ theState, int seed ) {
            theState.val = seed;
        }

        //
        //Returns a random number.
        //
        public int Spec_nrandom( RandomState/*!*/ theState ) {
            Spec_random(theState);
            return(theState.val);
        }

        //////////////////////////////////////////////////////////////////////////////
        //ZIPF Distribution                                                         *
        ////////////////////////////////////////////////////////////////////////////  

        public ZipfState spec_zipf_setup(RandomState rstate, int size, double Z)
        {
            int     i;
            double zipf_sum;

            ZipfState theState = new ZipfState(rstate,  size);
            if (theState == null) return null;

            // compute zipf values for samples 1-n   
            for (i = 1; i <= size; i++) {
                theState.table[i] = Math.Pow(((double)1.0/((double)i)), Z);
                //theState.table[i] = 1;   // SPL TOTAL HACK until POW works!!
            }

            // sum the values so we can compute probabilities.   
            // at the same time, make the values cumulative   
            zipf_sum = 0.0;
            for (i = 1; i <= size; i++) {
                zipf_sum += theState.table[i] ;
                theState.table[i] = zipf_sum;
            }
            theState.table[size] = 0.0;
            theState.table[0] = 0.0;

            // compute probability values by dividing by the sum.   
            // also reverse the table so we have values starting at 1.0   
            //  and descending to 0.0  (this is what spec_zipf needs)   
            for (i = 0; i < size; i++) {
                theState.table[i] = 1.0 - (theState.table[i]/zipf_sum);
            }


            return theState;
        }

        private void spec_zipf_free( ZipfState/*!*/ theState) {
            if (theState.table != null) {
                theState.table = null;
            }
        }

        public int spec_zipf(ZipfState/*!*/ theState) {
            double  r;
            int     i;

#if NO_ZIPF_SPIKE
            do{
#endif
                r = Spec_random(theState.rstate);
                i = 0;
                while (r < theState.table[i]) {
                    i++;
                }
#if NO_ZIPF_SPIKE
            } while (i > theState.size);
#endif
            return i-1;
        }




#if STATIC_NORMAL_DIST
// Right now, mean and stddev are ignored.  If someone has a good function to
// generate the cdf for normal distributions, let me know...   
// size=20, mean = 10, stddev = 3.5, will generate numbers from 0 to 20   
NormalState spec_normal_setup(, RandomState rstate, double mean, double stddev) {

double normal_dist[] = {
    0.002137432,
    0.005064024,
    0.011135458,
    0.022750062,
    0.043238098,
    0.076563771,
    0.126549006,
    0.19568292,
    0.283854542,
    0.387548544,
    0.5,
    0.612451456,
    0.716145458,
    0.80431708,
    0.873450994,
    0.923436229,
    0.956761902,
    0.977249938,
    0.988864542,
    0.994935976,
    1
};
    int i, index = 0;

    theState.size   = 1000;
    theState.rstate = rstate;

    theState.table=(int *)malloc(sizeof(int)*(theState.size+1));
    if (theState.table == NULL) {
    fprintf(stderr, "spec_normal_setup: can't malloc %d bytes for table\n",
        sizeof(double)*theState.size);
    exit (1);
    }

    for (i = 0; i < theState.size; i++) {
    if ((double)i / (double)theState.size > normal_dist[index]) {
        index++;
    }
    theState.table[i] = index;
    }

    return theState;
}

void spec_normal_free(NormalState theState) {
    if (theState.table) {
    free(theState.table);
    }
}

int spec_nnormal(NormalState theState) {
    int rval = spec_nrandom(theState.rstate.val);
    rval = rval % theState.size;
    return theState.table[rval];
}

#else

// Guts of this routine are based on:   
// boxmuller.c           Implements the Polar form of the Box-Muller
   //                    Transformation
//
   //                 (c) Copyright 1994, Everett F. Carter Jr.
   //                     Permission is granted by the author to use
   //                     this software for any application provided this
   //                     copyright notice is preserved.
//
  //

    private NormalState spec_normal_setup(NormalState/*!*/ theState,
                                          RandomState/*!*/ rstate,
                                          double mean,
                                          double stddev)
    {
        theState.mean = mean;
        theState.stddev = stddev;
        theState.rstate = rstate;
        theState.use_last = false;
        return null;
    }

    void spec_normal_free(NormalState theState)
    {
    }

    private double Spec_normal(NormalState/*!*/ theState)
    {
        double x1, x2, w, y1;

        if (theState.use_last) {                // use value from previous call   
            y1 = theState.y2;
        }
        else {
            do {
                x1 = 2.0 * Spec_random(theState.rstate) - 1.0;
                x2 = 2.0 * Spec_random(theState.rstate) - 1.0;
                w = x1 * x1 + x2 * x2;
            } while (w >= 1.0);

            w = Math.Sqrt( (-2.0 * Math.Log( w ) ) / w );
            y1 = x1 * w;
            theState.y2 = x2 * w;
        }
        theState.use_last = !(theState.use_last);
        return( theState.mean + y1 * theState.stddev );
    }

    private int spec_nnormal(NormalState/*!*/ theState)
    {
        return (int)(Spec_normal(theState));
    }
#endif
    } //random
} //namespace
