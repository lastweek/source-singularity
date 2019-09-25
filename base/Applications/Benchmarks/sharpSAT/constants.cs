// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Diagnostics;
//using Microsoft.Zap;
namespace SharpSAT
{
    public class SATCommon
    {
        private static void print_stack ()
        {
            // HACKHACK: unavailable on Singularity
            //Console.WriteLine("Stack Trace:");
            //StackTrace st = new StackTrace(true);
            //for (int i = 0; i < st.FrameCount; i++) {
            //  StackFrame sf = st.GetFrame(i);
            //  Console.WriteLine("\t{0}  at File: {1} Line: {2} ",
            //                      sf.GetMethod() ,
            //                      sf.GetFileName(),
            //                      sf.GetFileLineNumber());
            //}
            //
        }

        public static void sharp_assert (bool is_true)
        {
            if (!is_true) {
                Console.WriteLine("\nAssertion Failed" );
                print_stack();
                System.Environment.Exit(1);
            }

        }

        public static void warning (string msg)
        {
            Console.Write("\nWarning:" );
            Console.WriteLine(msg);
        }

        public static void fatal ()
        {
            Console.WriteLine("\nFatal Error" );
            print_stack();
            System.Environment.Exit(2);
        }

        public static void fatal (string msg)
        {
            Console.WriteLine ("Fatal Error: {0}", msg);
            print_stack();
            System.Environment.Exit(2);
        }

        public static string StatusToString(SATStatus status)
        {
            switch (status) {
                case SATStatus.UNDETERMINED: return "UNDETERMINED";
                case SATStatus.UNSATISFIABLE: return "UNSATISFIABLE";
                case SATStatus.SATISFIABLE: return "SATISFIABLE";
                case SATStatus.TIME_OUT: return "TIME";
                case SATStatus.MEM_OUT: return "MEM";
                case SATStatus.ABORTED: return "ABORTED";
            }

            return "UNKNOWN_RESULT";
        }

        public static int NEGATE (int s)            { return s^1; }
        public static int NON_NEGATED (int s)       { return s&(~1);}
        public static int SIGN (int s)              { return s & 1; }
        public static int NODE_ID (int s)           { return s >> 1; }
        public static int VID (int s)               { return s >> 1; }
        public static bool IS_NEGATED(int s)        { return (s&1) == 1; }

        public const int INVALID        = -1;
        public const int UNKNOWN        = 2;
        public const int WORD_WIDTH     = 16;
        public const int UIDSHIFT       = 27;

    }

    public enum ImpType : sbyte
    {
        NONE,
        CLAUSE,
        NODE,
        PB,
    }

    public enum ClType : sbyte
    {
        UNKNOWN,
        ORIGINAL,
        CONFLICT,
        BLOCKING,
        TEMP,
        DELETED
    }

    public enum NodeType : sbyte
    {
        UNKNOWN,
        VARIABLE,
        CONSTANT,
        PI,
        AND,
        XOR,
        FREE,
    }

    public enum SATStatus
    {
        UNDETERMINED,
        UNSATISFIABLE,
        SATISFIABLE,
        TIME_OUT,
        MEM_OUT,
        ABORTED
    }

    public struct SolverStats
    {
        public bool     been_reset              ;
        public bool     active_area_changed     ;
        public int      constraint_zero         ;
        public bool     is_solving              ;
        public SATStatus outcome                ;
        public bool     is_mem_out              ;
        public double   start_cpu_time          ;
        public double   finish_cpu_time         ;

        public double   total_cpu_time          ;
        public int      num_rounds              ;
        public int      num_free_variables      ;
        public int      num_free_branch_vars    ;
        public int      num_decisions           ;
        public int      num_conflicts           ;
        public int      num_backtracks          ;
        public int      max_dlevel              ;
        public long     num_implications        ;

        public int      num_cls_vars            ;
        public int      num_orig_clauses        ;
        public int      num_orig_literals       ;
        public int      num_learned_clauses     ;
        public long     num_learned_literals    ;
        public int      num_deleted_clauses     ;
        public long     num_deleted_literals    ;

        public int      next_restart;
        public int      next_gc;
        public int      next_decay;

        public int      num_restarts;
        public int      num_garbage_collections;

        public int      marked_current_dl;

        public SolverStats (bool do_init)
        {
            //regardless of the input, we have to init
            been_reset              = true;
            active_area_changed     = true;
            constraint_zero         = 0;
            is_solving              = false;
            outcome                 = SATStatus.UNDETERMINED;
            is_mem_out              = false;
            start_cpu_time          = 0;
            finish_cpu_time         = 0;

            total_cpu_time          = 0;
            num_rounds              = 0;
            num_free_variables      = 0;
            num_free_branch_vars    = 0;
            num_decisions           = 0;
            num_conflicts           = 0;
            num_backtracks          = 0;
            max_dlevel              = 0;
            num_implications        = 0;

            num_cls_vars            = 0;
            num_orig_clauses        = 0;
            num_orig_literals       = 0;
            num_learned_clauses     = 0;
            num_learned_literals    = 0;
            num_deleted_clauses     = 0;
            num_deleted_literals    = 0;

            next_restart            = 0;
            next_gc                 = 0;
            next_decay              = 0;

            num_restarts            = 0;
            num_garbage_collections = 0;

            marked_current_dl       = 0;
        }
    }

    public struct SolverParams
    {
        public double           time_limit;
        public long             mem_limit;

        public bool             enable_restart;
        public int              first_restart;
        public int              restart_period;

        public bool             enable_gc;
        public int              gc_period;
        public int              gc_head_threshold;
        public int              gc_tail_threshold;
        public int              gc_head_length;
        public int              gc_tail_length;
        public int              gc_head_tail_ratio;

        public int              decay_period;

        //public bool               reason_on_trans_fanin_only;

        public SolverParams (bool init)
        {
            time_limit          = 24 * 3600;
            mem_limit           = 1024 * 1024 * 512;

            enable_restart      = true;
            first_restart       = 7000;
            restart_period      = 700;

            enable_gc           = true;
            gc_period           = 600;
            gc_head_threshold   = 500;
            gc_tail_threshold   = 10;
            gc_head_length      = 6;
            gc_tail_length      = 45;
            gc_head_tail_ratio  = 16;

            decay_period        = 40;
            //reason_on_trans_fanin_only = false;
        }
    }
}
