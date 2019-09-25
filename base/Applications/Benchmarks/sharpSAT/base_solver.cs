// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//#define CHECK
#define GEN_RESOLVE_TRACE

using System;
using System.IO;
using System.Collections;
using System.Diagnostics;

//using Microsoft.Zap;
namespace SharpSAT
{
    /// <summary>
    /// Summary description for Class1.
    /// </summary>

    public class SharpSATSolver : SATCommon
    {
        public SolverStats      stats;
        internal SATHook        hook;
        internal SolverParams   parameters;

        private int             unique_id;  //the unique id seen so far for the nodes
        private IntVector       active_area;

        //private Process currentProcess          = Process.GetCurrentProcess();
        internal VarVector      variables       = new VarVector(4);
        internal ClsVector      clauses         = new ClsVector(4);
        private ObjVector       watched_clauses = new ObjVector(4);
        private IntVector       free_clauses    = new IntVector(4);

        internal IntVector      original_clauses= new IntVector(4);

        private NodeHashMap     node_hash       = new NodeHashMap();
        private FreeList        free_nodes;
        private IntVector       zero_ref_nodes  = new IntVector(4);
        private int             constant_one;

        private MyHashtable     node_to_pi_hash = new MyHashtable();
        internal IntVector      primary_inputs  = new IntVector(4);

        private ObjVector       asgn_stack      = new ObjVector(4);
        private int             dlevel          = 0;
        private Queue           implication_queue = new Queue();
        private IntVector       conflict_array  = new IntVector(4);
        private IntVector       learned_clause  = new IntVector(4);

        private IntVector       conflict_clauses= new IntVector(128);
        private IntVector       ordered_vars    = new IntVector(4);
        private int             max_score_pos   = 0;

        private IntVector       temporary_clauses= new IntVector(16);
        private ResolutionTrace rtrace          = null;

        [Microsoft.Contracts.NotDelayed]
        internal SharpSATSolver()
        {
            stats               = new SolverStats(true);
            parameters          = new SolverParams(true);
            rtrace              = new ResolutionTrace(this);
            variables           = new VarVector(4);
            asgn_stack          = new ObjVector(4);
            watched_clauses     = new ObjVector(4);
            free_nodes          = new FreeList(variables);
            //create Variable Num. 0: Constant 1
            int s               = new_node(NodeType.CONSTANT, INVALID, INVALID);
            sharp_assert (s == 0);
            asgn_stack.push_back            (new IntVector(4)); //for decision level 0
            constant_one        = s;
            primary_inputs      = new IntVector(4);

            stats.num_free_branch_vars  = 0;    //i.e. signal 0 doesn't count;
            stats.num_free_variables    = 0;
            stats.next_restart  = parameters.first_restart;
            stats.next_gc       = parameters.gc_period;
            stats.next_decay    = parameters.decay_period;

            active_area         = new IntVector(128);
            reasoning_flag  = alloc_flag();
            marked_flag     = alloc_flag();
            branchable_flag = alloc_flag();
            in_cl_flag      = alloc_flag();
            in_cl_sign_flag = alloc_flag();
            active_flag     = alloc_flag();
        }

        int canonical(int s)
        {
            bool invert = false;
            int r;
            for (r = s; variable(NODE_ID(r)).canonical != INVALID; r = variable(NODE_ID(r)).canonical)
                if (IS_NEGATED(s))
                    invert = !invert;
            if (invert)
                return NEGATE (r) ;
            else
                return r;
        }

        internal int var_value (int i)      { return variable(i).varValue; }
        internal void var_set_value (int i, short v) { variable(i).varValue = v; }
        internal int var_dlevel (int i)     { return variable(i).dlevel; }
        internal Variable variable (int i ) { return /*(Variable)*/ variables[i]; }
        internal Variable node (int sig)        { return variable(VID(sig)); }
        internal int num_variables()            { return variables.size() - 1; }
        internal int lit_value (int s)      { return var_value(VID(s)) ^ SIGN(s);}
        internal Clause clause(int idx)     { return /*(Clause)*/ clauses[idx]; }
        internal IntVector watched_by(int svar ) { return (IntVector) watched_clauses[svar]; }
        internal IntVector assignment_stack (int l) { return (IntVector) asgn_stack[l]; }
        internal ObjVector assignment_stack(){ return asgn_stack; }
        internal int num_pi()               { return primary_inputs.size(); }
        internal int pi(int n)              { return primary_inputs[n]; }
        internal bool is_pi (int n)         { return node(n).is_pi(); }
        internal bool is_gate (int n)           { return node(n).is_gate(); }
        internal int one()                  { return constant_one; }
        internal int zero()                 { return NEGATE(constant_one); }
        internal int signal_of(int vid)     { return vid + vid; }
        internal int node_to_pi(int s)      { return (int) node_to_pi_hash[NON_NEGATED(s)]; }
        internal NodeType node_type (int s) { return node(s).type; }
        internal int pi_var_value(int k)    { return variable(pi(k)).varValue; }
        internal bool is_pure_clause_based()    { return num_variables() == stats.num_cls_vars; }
        internal int d_level()              { return dlevel; }

        internal double session_cpu_time()  { return get_cpu_time() - stats.start_cpu_time; }
        internal double total_cpu_time()        { return stats.total_cpu_time; }

        internal void enable_rtrace(bool e) { rtrace.enable_trace(e); }

        #region GID_MANAGEMENT

        private int allocated_gid;

        internal int volatile_gid()         { return 0; }

        internal int alloc_gid ()
        {
            for (ushort i = 1; i <= WORD_WIDTH; ++i)
                if (is_gid_allocated(i) == false)
                {
                    allocated_gid |= (ushort) (1 << (i-1));
                    return i;
                }
            fatal();
            return volatile_gid();
        }

        internal void free_gid (int gid)
        {
            sharp_assert (gid > 0 && gid <= WORD_WIDTH);
            if (is_gid_allocated(gid) == false) {
                fatal();
            }
            allocated_gid &= (~(1<< (gid-1)));
        }

        internal bool is_gid_allocated(int gid)
        {
            if (gid == volatile_gid())
                return true;
            sharp_assert (gid<= WORD_WIDTH && gid > 0);
            if ((allocated_gid & (1 << (gid - 1))) != 0)
                return true;
            return false;
        }

        #endregion

        #region VAR_FLAG_MANAGEMENT

        private int allocated_flag = 0;

        internal int alloc_flag()
        {
            for (int i = 0; i < WORD_WIDTH; ++i) {
                if ((allocated_flag & (1 << i)) == 0) {
                    allocated_flag |= (1<<i);
                    return i;
                }
            }
            fatal();
            return 0;
        }

        internal void dealloc_flag (int idx)
        {
            sharp_assert((allocated_flag &(1<<idx)) != 0);
            allocated_flag &= (~(1<<idx));
        }

        internal void free_flag(int idx)
        {
            dealloc_flag(idx);
            clear_flag_for_all(idx);
        }

        internal void set_flag_for_all (int idx)
        {
            for (int i = 0; i < variables.size(); ++i)
                variable(i).set_flag(idx);
        }

        internal void clear_flag_for_all(int idx)
        {
            for (int i = 0; i < variables.size(); ++i)
                variable(i).clear_flag(idx);
        }
        internal bool is_flag_set (int s, int f)
        {
            return node(s).flag(f);
        }

        private int reasoning_flag  ;
        private int marked_flag     ;
        private int branchable_flag ;
        private int in_cl_flag      ;
        private int in_cl_sign_flag ;
        private int active_flag     ;

        internal bool is_reasoning(Variable v)      { return v.flag(reasoning_flag); }
        internal void set_reasoning(Variable v)     { v.set_flag(reasoning_flag); }
        internal void clear_reasoning(Variable v)   { v.clear_flag(reasoning_flag); }

        internal bool is_active(Variable v)         { return v.flag(active_flag); }
        internal void set_active(Variable v)        { v.set_flag(active_flag); }
        internal void clear_active(Variable v)      { v.clear_flag(active_flag); }

        internal bool is_branchable(Variable v)     { return v.flag(branchable_flag); }
        internal void set_branchable(Variable v)    { v.set_flag(branchable_flag); }
        internal void clear_branchable(Variable v)  { v.clear_flag(branchable_flag); }

        internal bool is_marked(Variable v)     { return v.flag(marked_flag); }
        internal void set_marked(Variable v)    { v.set_flag(marked_flag); }
        internal void clear_marked(Variable v)  { v.clear_flag(marked_flag); }
        #endregion


        private void include_cl_in_reasoning (int cl_id)
        {
            Clause cl = clause(cl_id);
            if (cl.num_lits > 1) {
                int max_idx = -1, max2_idx = -1, max_dl = -1, max2_dl = -1;
                for (int i = 0; i < cl.num_lits; ++i) {
                    int dl = var_dlevel(cl.literal(i) >> 1);
                    if (dl < 0 || (lit_value(cl.literal(i)) == 1)) //non - 0 variable, so make it the highest possible dl
                        dl = num_variables() + 1;
                    if (dl > max_dl) {
                        max2_idx = max_idx;
                        max_idx = i;
                        max2_dl = max_dl;
                        max_dl = dl;
                    }
                    else if (dl > max2_dl) {
                        max2_idx = i;
                        max2_dl = dl;
                    }
                }
                //the invariance: Literal 0 and 1 are watched
                int temp = cl.literal(0);
                cl.literals[0] = cl.literal(max_idx);
                cl.literals[max_idx] = temp;
                int svar = cl.literal(0);
                watched_by(svar).push_back ( cl_id + cl_id );
                if (max2_idx == 0)
                    max2_idx = max_idx;
                temp = cl.literal(1);
                cl.literals[1] = cl.literal(max2_idx);
                cl.literals[max2_idx] = temp;
                svar = cl.literal(1);
                watched_by(svar).push_back ( cl_id + cl_id + 1);
            }
        }

        void remove_cl_from_reasoning (int cl_id)
        {
            Clause cl = clause(cl_id);
            sharp_assert (cl.num_lits > 1);
            for (int k = 0; k < 2; ++k) {
                //two watched
                int lit = cl.literal(k);
                IntVector watch = watched_by(lit);
                int i, sz;
                for (i = 0, sz = watch.size(); i < sz; ++i) {
                    if ((watch[i] >> 1) == cl_id) {
                        //found it
                        watch[i] = watch.back;
                        watch.pop_back();
                        break;
                    }
                }
            }
        }

        private void incr_lits_count (int lit)
        {
            if ((lit & 1) == 1)
                ++ variable (VID(lit)).lits_count_1;
            else
                ++ variable (VID(lit)).lits_count_0;
        }

        private void decr_lits_count (int lit)
        {
            if ((lit & 1) == 1)
                -- variable (VID(lit)).lits_count_1;
            else
                -- variable (VID(lit)).lits_count_0;
        }

        private int get_free_clause_id()
        {
            int cl_id;
            if (!free_clauses.empty()) {
                cl_id = free_clauses.back;
                free_clauses.pop_back();
                clauses[cl_id] = new Clause();
            }
            else {
                cl_id = clauses.size();
                clauses.push_back (new Clause());
            }
            return cl_id;
        }

        private int add_clause_to_db (int [] lits, ClType tp, ushort gflag)
        {
            sharp_assert (lits.Length > 0);
            int cl_id = get_free_clause_id();
            Clause cl = clause(cl_id);
            cl.init( tp, lits, gflag, unique_id ++);

//          Console.Write("{0} :", cl_id);
//          for (int i=0; i< lits.Length; ++i)
//              Console.Write ("{0} ", lits[i]);
//          Console.WriteLine ("");

            for (int i = 0; i < cl.num_lits; ++i) {
                incr_lits_count (cl.literal(i));
                reference (cl.literal(i));
            }

            if (tp == ClType.ORIGINAL) {
                ++ stats.num_orig_clauses;
                original_clauses.push_back(cl_id);
                stats.num_orig_literals += lits.Length;
            }
            else if (tp == ClType.CONFLICT) {
                ++ stats.num_learned_clauses;
                conflict_clauses.push_back (cl_id);
                stats.num_learned_literals += lits.Length;
            }
            include_cl_in_reasoning (cl_id);

            return cl_id;
        }

        internal int add_new_implication (int [] reasons, int implied_lit)
        {
            if (reasons == null) {
                reasons = new int[dlevel];
                for (int i = 0; i < reasons.Length; ++i)
                    reasons[i] = (assignment_stack(i+1)[0]^1);
            }

            for (int i = 0; i < reasons.Length; ++i)
                sharp_assert (lit_value(reasons[i]) == 0);
            sharp_assert (var_value(VID(implied_lit)) == UNKNOWN);

            int cl_id = get_free_clause_id();

            Clause cl = clause(cl_id);
            int [] lits = new int [1 + reasons.Length];
            Array.Copy(reasons,lits,reasons.Length);
            lits[reasons.Length] = implied_lit;

            cl.init( ClType.TEMP, lits, 0, unique_id ++);
            temporary_clauses.push_back(cl_id);

            queue_implication(implied_lit, cl_id, ImpType.CLAUSE);
            return cl_id;
        }

        internal int merge_clause_group(int g2, int g1)
        {
            for (int i = 0, sz = clauses.size(); i < sz; ++i) {
                if (clause(i) != null && clause(i).gid(g1)) {
                    clause(i).clear_gid(g1);
                    clause(i).set_gid(g2);
                }
            }
            free_gid (g1);
            return g2;
        }

        internal void delete_clause_group (int g)
        {
            reset();
            bool[] remove = new bool [clauses.size()];
            for (int i = 0; i < clauses.size(); ++i) {
                remove[i] = false;
                if (clause(i) != null)
                    remove[i] = clause(i).gid(g);
            }
            delete_clauses(remove);
            free_gid (g);
        }

//      void delete_clause(int cl_id)
//      {
//          Clause cl = clause(cl_id);
//          if (cl.num_lits> 1)
//              remove_cl_from_reasoning (cl_id);
//
//
//          for (int i=0; i< cl.num_lits; ++i)
//              -- variable(cl.literal(i)>> 1).lits_count[cl.literal(i) & 1];
//
//          ++stats.num_deleted_clauses;
//          stats.num_deleted_literals += cl.num_lits;
//          if (cl.type == ClType.ORIGINAL)
//          {
//              --stats.num_orig_clauses;
//              stats.num_orig_literals -= cl.num_lits;
//              //              for (int j=0, n = clause(cl_id).num_lits; j < n ; ++j)
//              //                  deref (clause(cl_id).literal(j));
//          }
//          else
//          {
//              sharp_assert (cl.type == ClType.CONFLICT);
//              --stats.num_learned_clauses;
//              stats.num_learned_literals -= cl.num_lits;
//          }
//          //cl.type = ClType.DELETED;
//          clauses[cl_id] = null;
//          free_clauses.push_back(cl_id);
//      }

        void clean_up()
        {
            reset();
            bool [] remove = new bool [clauses.size()];
            for (int i = 0; i < clauses.size(); ++i) {
                Clause cl = clause(i);
                if (cl != null && cl.type == ClType.CONFLICT)
                    remove[i] = true; //to be deleted
                else
                    remove[i] = false;
            }
            delete_clauses(remove, false);
            rtrace.reset();
        }

        //convert all variables to primary inputs
        internal void convert_vars_to_pi ()
        {
            for (int i = 0; i < variables.size(); ++i) {
                if (variable(i).type == NodeType.VARIABLE) {
                    int id = num_pi();
                    int s = i + i;
                    node(s).type = NodeType.PI;
                    primary_inputs.push_back(s);
                    node_to_pi_hash[s] = id;
                }
            }
        }

        void delete_clauses(bool [] removes)
        {
            delete_clauses(removes, true);
//          Console.Write ("Remove : ");
//          for (int i=0; i< removes.Length; ++i)
//              if (removes[i])
//                  Console.Write("{0} ", i);
//          Console.WriteLine("");
        }

        void delete_clauses(bool[] removes, bool delete_original)
        {
            for (int i = 1; i < variables.size(); ++i) {
                //Variable var = variable(i);
                for (int k = 0; k < 2; ++k) {
                    IntVector w = watched_by(i + i + k);
                    for (int j = 0; j < w.size(); ++j)
                        if ( removes[(w[j] >> 1)])
                        {
                            w[j] = w.back;
                            w.pop_back();
                            --j;
                        }
                }
            }

            for (int i = 0; i < temporary_clauses.size(); ++i) {
                int cl_id = temporary_clauses[i];
                bool can_delete = true;
                foreach (int lit in clause(cl_id).literals) {
                    if (variable(VID(lit)).antecedent.type == ImpType.CLAUSE &&
                        variable(VID(lit)).antecedent.index == cl_id)
                    {
                        can_delete = false;
                        break;
                    }
                }
                if (can_delete) {
                    clauses[cl_id] = null;
                    temporary_clauses[i] = temporary_clauses.back;
                    temporary_clauses.pop_back();
                    --i;
                }
            }

            for (int i = 0; i < removes.Length; ++i) {
                Clause cl = clause(i);
                if (cl == null || removes[i] == false)
                    continue;

                ++ stats.num_deleted_clauses;
                stats.num_deleted_literals += cl.num_lits;

                for (int j = 0; j < cl.num_lits; ++j) {
                    decr_lits_count(cl.literal(j));
                    deref ( cl.literal(j));
                }

                if (cl.type == ClType.ORIGINAL) {
                    --stats.num_orig_clauses;
                    stats.num_orig_literals -= cl.num_lits;
                }
                else if  (cl.type == ClType.CONFLICT) {
                    --stats.num_learned_clauses;
                    stats.num_learned_literals -= cl.num_lits;
                }
                //cl.type = ClType.DELETED;
                clauses[i] = null;
                free_clauses.push_back(i);
            }

            IntVector temp = new IntVector(128);
            for (int i = 0; i < conflict_clauses.size(); ++i) {
                int cl_id = conflict_clauses[i];
                if (clause(cl_id) != null) {
                    sharp_assert (clause(cl_id).type == ClType.CONFLICT);
                    temp.push_back (cl_id);
                }
            }
            conflict_clauses = temp;

            if (delete_original) {
                stats.active_area_changed = true;
                IntVector temp1 = new IntVector(16);
                for (int i = 0; i < original_clauses.size(); ++i) {
                    int cl_id = original_clauses[i];
                    if (!removes[cl_id])
                        temp1.push_back(cl_id);
                }
                original_clauses = temp1;
            }
        }


        internal int constraint (int sig)
        {
            if (sig == one())  //don't constraint constants
                return 0;
            else if (sig == zero()) {
                stats.constraint_zero ++;
                return -1;
            }
            int gid = alloc_gid();
            int[] cls = new int[1];
            cls[0] = sig;
            add_clause(cls, gid, false);
            return gid;
        }

        internal void release_constraint (int gid)
        {
            if (gid <= 0) {
                if (gid < 0)
                    stats.constraint_zero --;
                return;
            }
            sharp_assert (is_gid_allocated(gid));
            int orig = stats.num_orig_clauses;
            delete_clause_group (gid);
            sharp_assert (orig == stats.num_orig_clauses + 1);
        }

        int find_max_dl(int cl_id) { return find_max_dl (clause(cl_id)); }

        int find_max_dl (Clause cl)
        {
            int max_dl = 0;

            for (int i = 0; i < cl.num_lits; ++i) {
                int lit = cl.literal(i);
                if (variable(lit >> 1).dlevel > max_dl)
                    max_dl = variable(lit>>1).dlevel;
            }
            return max_dl;
        }

        int find_unit_lit(int cl_id) { return find_unit_lit (clause(cl_id)); }
        int find_unit_lit (Clause cl)
        {
            if (cl == null)
                throw new Exception ("Null Clause");
            if (!is_unit(cl))
                return 0;
            int v1 = var_value(cl.literal(0)>>1);
            if (v1 == UNKNOWN)
                return cl.literal(0);
            else
                return cl.literal(1);
        }

        bool is_conflicting (int cl_id) { return is_conflicting (clause(cl_id)); }

        bool is_conflicting(Clause cl)
        {
            if (lit_value(cl.literal(0)) == 0 &&
                ( cl.num_lits == 1 || lit_value(cl.literal(1)) == 0) )
                return true;
            return false;
        }

        bool is_satisfied (int cl_id )  { return is_satisfied (clause(cl_id)); }

        bool is_satisfied(Clause cl)
        {
            for (int i = 0; i < cl.num_lits; ++i)
                if (lit_value(cl.literal(i)) == 1)
                    return true;
            return false;
        }

        bool is_unit (int cl_id) { return is_unit(clause(cl_id)); }

        bool is_unit(Clause cl)
        {
            if (cl.num_lits == 1) {
                if (var_value(cl.literal(0) >> 1) == UNKNOWN)
                    return true;
                else
                    return false;
            }
            else {
                int v1 = var_value(cl.literal(0)>>1);
                int l1 = lit_value(cl.literal(0));
                int v2 = var_value(cl.literal(1)>>1);
                int l2 = lit_value(cl.literal(1));
                if ((v1 == UNKNOWN && l2 == 0) ||
                    (v2 == UNKNOWN && l1 == 0))
                    return true;
                else
                    return false;
            }
        }

        int find_free_node_index(int i1, int i2)
        {
            //find a free node index that is larger than the index of i1 and i2
            int at_least;
            if (i1 == INVALID || i2 == INVALID) {
                sharp_assert (i1 == INVALID && i2 == INVALID);
                at_least = -1;
            }
            else
                at_least = (i1>i2)? (i1>> 1): (i2>> 1);

            int idx = free_nodes.find_greater_than (at_least);
            int vid;
            if (idx < 0) {
                //can't find it, so enlarge the node array
                variables.push_back(new Variable());
                watched_clauses.push_back (new IntVector(4));
                watched_clauses.push_back (new IntVector(4));
                vid = variables.size() - 1;
            }
            else
                vid = idx;
            sharp_assert (vid > at_least);
            return vid;
        }

        internal int add_variable()
        {
            ++ stats.num_cls_vars;
            int sig = new_node (NodeType.VARIABLE, INVALID, INVALID);
            return VID(sig);
        }

        internal void set_num_variables(int k)
        {
            while (num_variables() < k)
                add_variable();
        }

        void sort_var_score ()
        {
            int nvar = ordered_vars.size();
            int [] scores = new int [nvar];
            int [] ordered = new int [nvar];
            for (int i = 0; i < ordered_vars.size(); ++i) {
                scores[i] = variable(ordered_vars[i]).score();
                ordered[i] = ordered_vars[i];
            }

            Array.Sort(scores, ordered);
            for (int i = 0; i < nvar; ++i) //reverse it
                ordered_vars[i] = ordered[nvar - i - 1];

            for (int i = 0; i < nvar; ++i) {
                int vid = ordered_vars[i];
                variable(vid).ordered_pos = i;
            }
            max_score_pos = 0;
            for (int i = 1; i < ordered_vars.size(); ++i)
                sharp_assert (variable(ordered_vars[i]).score() <= variable(ordered_vars[i-1]).score());
        }

        void incr_score (int svar)
        {
            if (SIGN(svar) == 0)
                ++ variable(VID(svar)).score_0;
            else
                ++ variable(VID(svar)).score_1;
        }

        void incr_var_score( int svar)
        {
            int vid = VID(svar);
            //int sign = SIGN(svar);
            int old_score = variable(vid).score();
            incr_score (svar);
            int new_score = variable(vid).score();
            if (old_score == new_score)
                return;

            int pos = variable(vid).ordered_pos;
            int orig_pos = pos;
            sharp_assert (ordered_vars[pos] == vid);
            int bubble_step = 0x400;
            for (pos = orig_pos - bubble_step; pos >= 0; pos -= bubble_step)
                if (variable(ordered_vars[pos]).score() >= new_score)
                    break;
            pos += bubble_step;
            for (bubble_step = (bubble_step >> 1); bubble_step > 0; bubble_step = (bubble_step >> 1)) {
                if (pos - bubble_step >= 0) {
                    if (variable(ordered_vars[pos - bubble_step]).score() < new_score)
                        pos -= bubble_step;
                }
            }
            //now found the position, do a swap
            ordered_vars[orig_pos] = ordered_vars[pos];
            variable(ordered_vars[orig_pos]).ordered_pos = orig_pos;

            ordered_vars[pos] = vid;
            variable(ordered_vars[pos]).ordered_pos = pos;
#if CHECK
            for (int i = 0; i < ordered_vars.size(); ++i) {
                sharp_assert (i==0 || variable(ordered_vars[i]).score() <= variable(ordered_vars[i - 1]).score());
                sharp_assert (variable(ordered_vars[i]).ordered_pos == i);
            }
#endif
        }

        int new_node(NodeType tp, int i1, int i2)
        {
            int vid = find_free_node_index(i1, i2);
            Variable n = variable(vid);

            n.clear_all_flag();
            n.clear_all_gid();

            clear_marked(n);
            n.set_flag(branchable_flag);
            n.clear_flag(in_cl_flag);
            n.clear_flag(in_cl_sign_flag);
            n.clear_flag(reasoning_flag);

            n.type          = tp;
            n.left          = i1;
            n.right         = i2;
            n.canonical     = INVALID;
            n.ref_count     = 0;
            n.lits_count_0  = 0;
            n.lits_count_1  = 0;
            n.uid           = unique_id ++;

            n.score_0       = 0;
            n.score_1       = 0;
            n.asgn_pos      = -1;

            n.varValue      = UNKNOWN;
            n.antecedent    = -1;
            n.dlevel        = -1;
            n.outputs.clear();

            ++ stats.num_free_variables;
            ++ stats.num_free_branch_vars;

            if (tp == NodeType.AND || tp == NodeType.XOR) {
                set_reasoning(n);
                make_node_consistent(vid + vid);
                if (tp == NodeType.AND) {
                    n.score_0 += 1;
                    n.score_1 += 2;
                    ++node(i1).score_0;
                    ++node(i1).score_1;
                    ++node(i2).score_0;
                    ++node(i2).score_1;
                }
                else {
                    sharp_assert (tp == NodeType.XOR);
                    n.score_0 += 2;
                    n.score_1 += 2;
                    node(i1).score_0 += 2;
                    node(i1).score_1 += 2;
                    node(i2).score_0 += 2;
                    node(i2).score_1 += 2;
                }
            }
            return vid + vid;
        }

        int [] remove_dup_literals(int [] orig_lits)
        {
            bool redundant = false;
            IntVector literals = new IntVector(4);
            for (int i = 0; i < orig_lits.Length; ++i) {
                int l = orig_lits[i];
                if (l == 0) //i.e. constant 1
                {
                    redundant = true;
                    break;
                }
                else if (l == 1) //i.e. constant 0
                    continue;

                Variable var = variable(l >>1);
                if (var.flag(in_cl_flag) == false)  //never occurred
                {
                    var.set_flag(in_cl_flag);
                    if (IS_NEGATED(l))
                        var.set_flag(in_cl_sign_flag);
                    else
                        var.clear_flag(in_cl_sign_flag);
                    literals.push_back(l);
                }
                else if (var.flag(in_cl_sign_flag) == IS_NEGATED(l)) //same phase
                    continue;
                else
                    redundant = true;
            }
            //reset back
            for (int i = 0; i < orig_lits.Length; ++i) {
                variable(VID(orig_lits[i])).clear_flag(in_cl_flag);
                variable(VID(orig_lits[i])).clear_flag(in_cl_sign_flag);
            }
            if (redundant)
                return null;
            return literals.ToArray();
        }

        int add_clause_do_implication ( int [] lits, ClType tp, ushort gflag)
        {
            int cl_id = add_clause_to_db( lits, tp, gflag);

            if (stats.been_reset == false) // may cause implication
            {
                Clause cl = clause(cl_id);
                if (is_conflicting(cl)) {
                    int dl = find_max_dl(cl);
                    backtrack(dl-1);
                }
                if (dlevel >= 0) {
                    int unit = find_unit_lit(cl);
                    if (unit != 0) {
                        int l = find_max_dl(cl);
                        if (l < dlevel)
                            backtrack(l);
                        queue_implication(unit, cl_id, ImpType.CLAUSE);
                    }
                }
                else
                    stats.outcome = SATStatus.UNSATISFIABLE;
            }
            return cl_id;
        }

        int add_clause_with_gflag ( int[] orig_lits, ClType tp, ushort gflag, bool do_check )
        {
            sharp_assert (conflict_array.empty());

            int[] lits;
            if (do_check)
                lits = remove_dup_literals(orig_lits);
            else
                lits = orig_lits;

            if (lits == null)
                throw new Exception (" A clause contain a literal and its negation");
            else if (lits.Length == 0)
                throw new Exception("An empty clause occurred in the original clauses");

            int cl_id = add_clause_do_implication ( lits, tp, gflag);
            return cl_id;
        }

        int add_blocking_clause (int [] lits, int gid)
        {
            ushort gflag = 0;
            if (gid > 0)
                gflag = (ushort)(1<<(gid-1));
            foreach (int lit in lits)
                sharp_assert (is_active(node(lit)));
            return add_clause_with_gflag (lits, ClType.BLOCKING, gflag, true);
        }

        internal int add_clause (int [] lits)
        {
            return add_clause (lits, 0, true);
        }

        internal int add_clause (int [] lits, int gid)
        {
            return add_clause (lits, gid, true) ;
        }

        internal int add_clause (int [] lits, int gid, bool do_check)
        {
            ushort gflag = 0;
            if (gid > 0)
                gflag = (ushort)(1<<(gid-1));
            foreach (int lit in lits) {
                if (!is_active(node(lit))) {
                    stats.active_area_changed = true;
                    break;
                }
            }
            return add_clause_with_gflag (lits, ClType.ORIGINAL, gflag, do_check);
        }

        int add_learned_clause(int[] lits, ushort gflag)
        {
            int cl_id = add_clause_to_db( lits, ClType.CONFLICT,  gflag);
            rtrace_record_resolve_process (clause(cl_id).uid);
            return cl_id;
        }

        internal void set_branchable(int vid, bool br)
        {
            sharp_assert ( !stats.is_solving );
            Variable var = variable(vid);
            if (br && !is_branchable(var)) {
                set_branchable(var);
                if (var_value(vid) == UNKNOWN)
                    ++ stats.num_free_branch_vars;
            }
            else if (!br && is_branchable(var)) {
                clear_branchable(var);
                if (var_value(vid) == UNKNOWN)
                    -- stats.num_free_branch_vars;
            }
        }

        internal void restart()
        {
            conflict_array.clear();
            implication_queue.Clear();
            if (dlevel > 0)
                backtrack(0);
            ++stats.num_restarts;
        }

        void run_garbage_collection()
        {
            bool[] remove = new bool [clauses.size()];
            for (int i = 0; i < remove.Length; ++i)
                remove[i] = false;

            int headcount = conflict_clauses.size() / parameters.gc_head_tail_ratio;
            for (int i = 0; i < headcount; ++i) {
                int cl_id = conflict_clauses[i];
                Clause cl = clause(cl_id);
                sharp_assert (cl.type == ClType.CONFLICT);
                if (cl.activity > parameters.gc_head_threshold)
                    continue;
                int num_0 = 0;
                for (int j = 0; j < cl.num_lits; ++j)
                    if (lit_value(cl.literal(j)) == 0)
                        ++ num_0;
                if (cl.num_lits - num_0 < parameters.gc_head_length)
                    continue;
                remove[cl_id] = true;
            }
            for (int i = headcount; i < conflict_clauses.size(); ++i) {
                int cl_id = conflict_clauses[i];
                Clause cl = clause(cl_id);
                sharp_assert (cl.type == ClType.CONFLICT);
                if (cl.activity > parameters.gc_tail_threshold)
                    continue;
                int num_0 = 0;
                for (int j = 0; j < cl.num_lits; ++j)
                    if (lit_value(cl.literal(j)) == 0)
                        ++ num_0;
                if (cl.num_lits - num_0 < parameters.gc_tail_length)
                    continue;
                remove[cl_id] = true;
            }

            delete_clauses(remove, false);
            ++ stats.num_garbage_collections;
        }

        void decay_variable_score()
        {
            for (int i = 1, sz = variables.size(); i < sz; ++i) {
                Variable var = variable(i);
                var.score_0 = (short)(var.score_0 >> 1);
                var.score_1 = (short)(var.score_1 >> 1);
            }
        }

        void run_periodic_functions()
        {
            //a. restart
            if (parameters.enable_restart && stats.num_backtracks > stats.next_restart) {
                //System.Console.Write ("-");
                stats.next_restart = stats.num_backtracks + parameters.restart_period;
                restart();
            }
            //b. delete clauses
            if (parameters.enable_gc && stats.num_backtracks > stats.next_gc) {
                //System.Console.Write ("*");
                stats.next_gc = stats.num_backtracks + parameters.gc_period;
                run_garbage_collection();
            }
            //c. decay variable score
            if (stats.num_backtracks > stats.next_decay) {
                stats.next_decay = stats.num_backtracks + parameters.decay_period;
                decay_variable_score();
            }
        }

        internal void make_decision (int svar)
        {
            sharp_assert(implication_queue.Count == 0);
            sharp_assert (svar > 0 && var_value(svar>>1) == UNKNOWN);
            ++ dlevel;

            sharp_assert (stats.max_dlevel == asgn_stack.size() - 1);
            if (dlevel > stats.max_dlevel)
                stats.max_dlevel = dlevel;
            if (asgn_stack.size() <= dlevel)
                asgn_stack.push_back (new IntVector(32) );

            queue_implication(svar, -1, ImpType.NONE);
            ++ stats.num_decisions;
        }

        bool make_branch_decision()
        {
            if (implication_queue.Count != 0)
                return ((( Implication)(implication_queue.Peek())).lit > 1 );

            if (stats.num_free_branch_vars == 0)
                return false;

            int svar = 0;

            for (; max_score_pos < ordered_vars.size(); ++ max_score_pos) {
                int vid = ordered_vars[max_score_pos];
                if (variable(vid).varValue == UNKNOWN && is_branchable(variable(vid))) {
                    if (variable(vid).score_0 > variable(vid).score_1)
                        svar = vid + vid;
                    else
                        svar = vid + vid + 1;
                    break;
                }
            }
            if (svar == 0) //even if still free branch, if all clauses are satisfied, then ok.
                return false;

            if (hook != null)
                hook.OnCaseSplit(svar);

            sharp_assert (is_active(node(svar)));
            make_decision(svar);
            return true;
        }


        void real_solve()
        {
            stats.outcome = SATStatus.UNDETERMINED;

            while (true) {
                if (get_cpu_time() - stats.start_cpu_time > parameters.time_limit) {
                    stats.outcome = SATStatus.TIME_OUT;
                    return;
                }
                if (stats.is_mem_out) {
                    stats.outcome = SATStatus.MEM_OUT;
                    return;
                }

                run_periodic_functions();

                bool can_branch = make_branch_decision();
                if (!can_branch) {
                    stats.outcome = SATStatus.SATISFIABLE;
                    return;
                }

                while (deduce() == false)
                    resolve_conflicts();

                //after above loop, the solver will stabilize in a decision level
                //with no conflict and implication. If this level is -1 then unsat
                if (dlevel < 0) {
                    stats.outcome = SATStatus.UNSATISFIABLE;
                    return;
                }
                if (hook != null)
                    hook.OnBCP ();
            }
        }

        internal void reset ()
        {
            if (stats.been_reset == false) {
                if (dlevel >= 0)
                    backtrack( -1 );
                dlevel = 0;
                stats.outcome = SATStatus.UNDETERMINED;
                stats.been_reset = true;
            }
        }

        double get_cpu_time ()
        {
            //
            //currentProcess.Refresh();
            //TimeSpan cputime = currentProcess.TotalProcessorTime;
            //return cputime.Hours * 3600 + cputime.Seconds + cputime.Milliseconds / 1000.0;
            //
            return DateTime.Now.Ticks / 1e7;
        }

        void init ()
        {
            if (!stats.active_area_changed)
                return;
            //so, we need to figure out new active area
            for (int i = 0; i < active_area.size(); ++i) {
                Variable var = node(active_area[i]);
                var.clear_flag(reasoning_flag);
                clear_active(var);
            }
            active_area.clear();

            for (int i = 0; i < original_clauses.size(); ++i) {
                int cl_id = original_clauses[i];
                Clause cl = clause(cl_id);
                foreach (int lit in cl.literals) {
                    if (!node(lit).flag(active_flag)) {
                        active_area.push_back(NON_NEGATED(lit));
                        set_active(node(lit));
                    }
                }
            }
            mark_transitive_fanins(active_area, active_flag);

            ordered_vars.clear();
            for (int i = 0; i < active_area.size(); ++i) {
                int vid = VID(active_area[i]);
                Variable var = variable(vid);
                sharp_assert (var.flag(active_flag));
                if (is_branchable(var)) //add it into vars for branching
                {
                    var.score_0 = variable(i).lits_count_0;
                    var.score_1 = variable(i).lits_count_1;
                    var.ordered_pos = ordered_vars.size();
                    ordered_vars.push_back(vid);
                }
                if (var.is_gate())
                    var.set_flag(reasoning_flag);
                else
                    var.clear_flag(reasoning_flag);
            }
        }

        internal SATStatus solve()
        {
            if (stats.constraint_zero > 0) {
                stats.outcome = SATStatus.UNSATISFIABLE;
                return stats.outcome;
            }

            stats.start_cpu_time = get_cpu_time();

            init();

            //enable_rtrace(true);
            sharp_assert (stats.is_solving == false);
            stats.is_solving = true;

            if (stats.been_reset == true)
                preprocess();

            stats.been_reset = false;

            if (dlevel < 0)
                stats.outcome = SATStatus.UNSATISFIABLE;
            else
                real_solve();

            stats.finish_cpu_time = get_cpu_time();
            stats.total_cpu_time += stats.finish_cpu_time - stats.start_cpu_time;
            ++ stats.num_rounds;
            stats.is_solving = false;

            //rtrace.dump_trace("trace");
            //if (stats.outcome == SATStatus.UNSATISFIABLE)
            //  dump_unsat_core("core.cnf");
            return stats.outcome;
        }

        void preprocess()
        {
            sharp_assert (dlevel == 0);
            for (int i = 0; i < clauses.size(); ++i) {
                Clause cl = clause(i);
                if (cl == null)
                    continue;
                if (is_conflicting(cl))
                    queue_conflict(i, ImpType.CLAUSE);
                else {
                    int unit = find_unit_lit(cl);
                    if (unit != 0)
                        queue_implication(unit, i, ImpType.CLAUSE);
                }
            }

            if (deduce() == false) {
                resolve_conflicts();
                sharp_assert ( dlevel < 0);
                stats.outcome = SATStatus.UNSATISFIABLE;
            }
        }


        void mark_involved_var(int vid)
        {
            Variable var = variable(vid);
            if (is_marked(var) == false) {
                set_marked(var);
                if (var.dlevel == dlevel)
                    ++ stats.marked_current_dl;
                else
                    learned_clause.push_back(vid + vid + var_value(vid));
            }
        }

        void rtrace_add_resolvent(int uid)
        {
#if GEN_RESOLVE_TRACE
            rtrace.add_reason(uid);
#endif
        }

        void rtrace_add_resolvent(int uid, int r)
        {
#if GEN_RESOLVE_TRACE
            rtrace.add_reason(uid + (r << UIDSHIFT));
#endif
        }

        void rtrace_record_resolve_process (int uid)
        {
#if GEN_RESOLVE_TRACE
            rtrace.set_resolvent (uid);
#endif
        }

        void rtrace_gen_empty_clause(Antecedent conf)
        {
#if GEN_RESOLVE_TRACE
            sharp_assert ( stats.marked_current_dl == 0);
            sharp_assert (dlevel == 0);

            mark_conflict(conf) ;
            IntVector assignments = assignment_stack(dlevel);
            for (int i = assignments.size() - 1; i >= 0; --i) {
                int lit = assignments[i];
                int vid = (lit >> 1);
                Variable var = variable(vid);
                if (is_marked(var)) {
                    mark_reason (vid);
                    clear_marked(var);
                    -- stats.marked_current_dl;
                }
            }
            sharp_assert ( stats.marked_current_dl == 0);
            sharp_assert ( learned_clause.size() == 0);

            //now record the generation process
            rtrace.set_empty_resolvents();
#endif
        }


        ushort mark_conflict(Antecedent conf)
        {
            // return the group flag of id of type
            switch (conf.type) {
                case ImpType.CLAUSE:    //implied by a clause
                {
                    Clause cl = clause(conf.index);
                    for (int i = 0; i < cl.num_lits; ++i)
                        mark_involved_var(VID(cl.literal(i)));

                    rtrace_add_resolvent (cl.uid);
                    ++cl.activity;
                    return cl.gflag;
                }
                case ImpType.PB:    //implied by a pseudo boolean constraint
                {
                    fatal();
                    break;
                }
                case ImpType.NODE:      //implied by a combinational gate
                {
                    int r = node_mark_conflict(conf.index);
                    Variable nd = variable(conf.index);
                    rtrace_add_resolvent (nd.uid, r);
                    return nd.gflag;
                }
                default:
                    sharp_assert(false);
                    break;
            }
            return 0;
        }

        ushort mark_reason(int vid)
        {
            Variable var = variable(vid);
            Antecedent ante = var.antecedent;
            switch (ante.type) {
                case ImpType.CLAUSE:    //implied by a clause
                {
                    Clause cl = clause(ante.index);

                    for (int i = 0; i < cl.num_lits; ++i)
                        if ((cl.literal(i)>>1) != vid)
                            mark_involved_var(cl.literal(i) >> 1);
                    rtrace_add_resolvent (cl.uid);
                    ++cl.activity;
                    return cl.gflag;
                }
                case ImpType.PB:    //implied by a pseudo boolean constraint
                {
                    fatal();
                    break;
                }
                case ImpType.NODE:      //implied by a combinational gate
                {
                    int r = node_mark_reason(vid);
                    Variable nd = variable(ante.index);
                    rtrace_add_resolvent (nd.uid, r);
                    return nd.gflag;
                }
                default:
                    sharp_assert(false);
                    break;
            }
            fatal();
            return 0;
        }

        //
        // return value: which clause is responsible
        // a == i0, b == i1, c == out
        // for AND
        // 1: (a + c')
        // 2: (b + c')
        // 3: (a' + b' + c)
        // for XOR
        // 4: (a' + b + c)
        // 5: (a + b' + c)
        // 6: (a + b + c')
        // 7: (a' + b' + c')
        // 
        int node_mark_conflict(int vid)
        {
            Variable n = variable(vid);
            sharp_assert (var_value(vid) != UNKNOWN);
            mark_involved_var( vid );

            int r = 0;
            int i0 = n.left;
            int vid0 = NODE_ID(i0);
            int i1 = n.right;
            int vid1 = NODE_ID(i1);
            if (n.type == NodeType.AND) {
                if (var_value(vid) == 0) {
                    sharp_assert (lit_value(i0) == 1);
                    sharp_assert (lit_value(i1) == 1);
                    mark_involved_var( vid0 );
                    mark_involved_var( vid1 );
                    r = 3;
                }
                else {
                    //var value == 1
                    sharp_assert (lit_value(i0) == 0 || lit_value(i1) == 0);
                    if (lit_value(i0) != 0) {
                        mark_involved_var( vid1 );
                        r = 2;
                    }
                    else if (lit_value(i1) != 0) {
                        mark_involved_var( vid0 );
                        r = 1;
                    }
                    else {
                        sharp_assert (variable(vid0).dlevel == variable(vid1).dlevel);
                        if (variable(vid0).asgn_pos < variable(vid1).asgn_pos) {
                            mark_involved_var( vid0 );
                            r = 1;
                        }
                        else {
                            mark_involved_var( vid1 );
                            r = 2;
                        }
                    }
                }
            }
            else {
                sharp_assert (n.type == NodeType.XOR);
                sharp_assert (lit_value(i0) == 0 || lit_value(i0) == 1);
                sharp_assert (lit_value(i1) == 0 || lit_value(i1) == 1);
                sharp_assert ((lit_value(i0) ^ lit_value(i1)) != var_value(vid));
                mark_involved_var( vid0 );
                mark_involved_var( vid1 );
#if GEN_RESOLVE_TRACE
                int va = lit_value(i0);
                int vb = lit_value(i1);
                int vc = var_value(vid);
                if (va == 1 && vb == 0 && vc == 0)
                    r = 4;
                else if (va == 0 && vb == 1 && vc == 0)
                    r = 5;
                else if (va == 0 && vb == 0 && vc == 1)
                    r = 6;
                else {
                    sharp_assert (va == 1 && vb == 1 && vc == 1);
                    r = 7;
                }
#endif
            }
            return r;
        }

        int node_mark_reason(int vid)
        {
            sharp_assert (variable(vid).antecedent.type == ImpType.NODE);
            int ante = variable(vid).antecedent.index;

            int r = 0;
            Variable n = variable(ante);
            int i0 = n.input(0);
            int vid0 = NODE_ID(i0);
            int i1 = n.input(1);
            int vid1 = NODE_ID(i1);

            if (n.type == NodeType.AND) {
                if (vid == ante) {
                    //by itself, so it's propagation, the reason is it's input
                    if (var_value(vid) == 1) {
                        sharp_assert (lit_value(i0) == 1);
                        sharp_assert (lit_value(i1) == 1);
                        mark_involved_var( vid0 );
                        mark_involved_var( vid1 );
                        r = 3;
                    }
                    else {
                        sharp_assert (lit_value(i0) == 0 || lit_value(i1) == 0);
                        if (lit_value(i0) != 0) {
                            mark_involved_var( vid1 );
                            r = 2;
                        }
                        else if (lit_value(i1) != 0) {
                            mark_involved_var( vid0 );
                            r = 1;
                        }
                        else {
                            sharp_assert (var_dlevel(vid0) == var_dlevel(vid1));
                            if (variable(vid0).asgn_pos < variable(vid1).asgn_pos) {
                                mark_involved_var( vid0 );
                                r = 1;
                            }
                            else {
                                mark_involved_var( vid1 );
                                r = 2;
                            }
                        }
                    }
                }
                else {
                    //it's justification, the reason is it's output (ante), and maybe the other input of ante
                    int other_vid;
                    int other_input;
                    int self_input;

                    sharp_assert (vid0 == vid || vid1 == vid);
                    if (vid0 == vid) {
                        other_vid = vid1;
                        other_input = i1;
                        self_input = i0;
                        r = 1;
                    }
                    else {
                        other_vid = vid0;
                        other_input = i0;
                        self_input = i1;
                        r = 2;
                    }
                    if (lit_value(self_input) == 1) {
                        sharp_assert (var_value(ante) == 1);
                        mark_involved_var( ante );
                    }
                    else {
                        sharp_assert (var_value(ante) == 0);
                        sharp_assert (lit_value(other_input) == 1);
                        mark_involved_var( ante );
                        mark_involved_var( other_vid );
                        r = 3;
                    }
                }
            }
            else {
                sharp_assert (n.type == NodeType.XOR);
                if (ante == vid) {
                    mark_involved_var( vid0 );
                    mark_involved_var( vid1 );
#if GEN_RESOLVE_TRACE
                    int va = lit_value(i0);
                    int vb = lit_value(i1);
                    int vc = var_value(ante);
                    if (vc == 1) {
                        if (va == 1 && vb == 0)
                            r = 4;
                        else {
                            sharp_assert (va == 0 && vb == 1);
                            r = 5;
                        }
                    }
                    else {
                        if (va == 0 && vb == 0)
                            r = 6;
                        else {
                            sharp_assert (va == 1 && vb == 1);
                            r = 7;
                        }
                    }
#endif
                }
                else {
                    mark_involved_var( ante );
                    sharp_assert (vid0 == vid || vid1 == vid);
                    if (vid0 == vid)
                        mark_involved_var( vid1 );
                    else
                        mark_involved_var( vid0 );
#if GEN_RESOLVE_TRACE
                    int va = lit_value(i0);
                    //int vb = lit_value(i1);
                    int vc = var_value(ante);
                    if (vc == 0) {
                        if (va == 0)
                            r = 4;
                        else
                            r = 5;
                    }
                    else {
                        if (va == 0)
                            r = 6;
                        else
                            r = 7;
                    }
#endif
                }
            }
            return r;
        }

        void resolve_conflicts()
        {
            sharp_assert (!conflict_array.empty());
            sharp_assert (implication_queue.Count == 0);
            sharp_assert ( stats.marked_current_dl == 0 );
            sharp_assert ( learned_clause.empty() );

            ++ stats.num_conflicts;

            if (dlevel == 0) {
                rtrace_gen_empty_clause(conflict_array[0]);
                backtrack(-1);
                conflict_array.clear();
                return;
            }

            ushort gflag = 0;

            Antecedent conf = (Antecedent) conflict_array[0];

            for (int i = 1, sz = conflict_array.size(); i < sz; ++i) {
                if (((Antecedent)conflict_array[i]).type == ImpType.NODE) {
                    conf = (Antecedent) conflict_array[i];
                    break;
                }
            }

            gflag |= mark_conflict(conf);

            sharp_assert (stats.marked_current_dl > 1);

            IntVector assignments = assignment_stack(dlevel);
            for (int i = assignments.size() - 1; i >= 0; --i) {
                int lit = assignments[i];
                int vid = (lit >> 1);
                Variable var = variable(vid);

                if (!is_marked(var))
                    continue;

                if (stats.marked_current_dl == 1) {
                    learned_clause.push_back(lit^1);
                    break;
                }
                else {
                    gflag |= mark_reason (vid);
                    clear_marked(var);
                    -- stats.marked_current_dl;
                }
            }
            sharp_assert ( stats.marked_current_dl == 1);

            int sharp_assert_level = 0;
            int sharp_assert_lit = learned_clause.back;
            sharp_assert (lit_value(sharp_assert_lit) == 0);
            clear_marked(node(sharp_assert_lit));
            -- stats.marked_current_dl;

            for (int i = 0; i < learned_clause.size() - 1; ++i) {
                int lit = learned_clause[i];
                incr_var_score (lit);
                sharp_assert (lit_value(lit) == 0);

                Variable var = variable(lit>>1);
                sharp_assert (is_marked(var));
                clear_marked(var);
                if (var.dlevel > sharp_assert_level)
                    sharp_assert_level = var.dlevel;
            }
            backtrack(sharp_assert_level);

            int cl_id = add_learned_clause(learned_clause.ToArray(), gflag);
            learned_clause.clear();
            sharp_assert (is_unit(cl_id));
            queue_implication(sharp_assert_lit, cl_id, ImpType.CLAUSE);
            conflict_array.clear();
        }


        void queue_conflict (int ante, ImpType type)
        {
            Antecedent antecedent = new Antecedent(type, ante);
            conflict_array.push_back ((int) antecedent);
        }

        void queue_implication(int lit, int ante, ImpType type)
        {
            if (is_active(node(lit))) //it is in the active area
            {
                Implication imp = new Implication();
                imp.lit = lit;
                imp.ante.type = type;
                imp.ante.index = ante;
                implication_queue.Enqueue (imp);
            }
        }

        bool deduce()
        {
            while (implication_queue.Count != 0 && conflict_array.empty()) {
                Implication imp = (Implication) implication_queue.Dequeue();
                int lit = imp.lit;
                int vid = lit>> 1;
                if (var_value(vid) == UNKNOWN) {
                    propagate_implication ( imp );
                    variable(vid).asgn_pos = assignment_stack(dlevel).size();
                    assignment_stack(dlevel).push_back(lit);
                }
                else {
                    if (lit_value(lit) == 0)   //conflict
                        queue_conflict(imp.ante.index, imp.ante.type);
                }
#if CHECK
                for (int i = 0; i < clauses.size(); ++i) {
                    Clause cl = clause(i);
                    if (cl != null && is_conflicting(i))
                        sharp_assert (!conflict_array.empty());
                }
#endif
            }
            if (!conflict_array.empty()) {
                implication_queue.Clear();
                return false;
            }
            return true;
        }

        void propagate_implication (Implication imp)
        {
            int vid = imp.lit>> 1;

            Variable var = variable(vid);
            sharp_assert (var_value(vid) == UNKNOWN);

            var.dlevel = dlevel;
            var.antecedent = imp.ante;

            var_set_value (vid, (short) (1 - (imp.lit&1)));

            set_svar_value(imp.lit);

            ++ stats.num_implications ;
            -- stats.num_free_variables;
            if (is_branchable(var))
                -- stats.num_free_branch_vars;
        }

        void unset_variable(int v)
        {
            if (v == 0) return;
            Variable var = variable(v);
            var.dlevel      = -1;
            var.antecedent  = -1;
            var.asgn_pos    = -1;
            var_set_value (v, UNKNOWN);
            ++ stats.num_free_variables;
            if (is_branchable(var)) {
                ++ stats.num_free_branch_vars;
                if (var.ordered_pos < max_score_pos)
                    max_score_pos = var.ordered_pos;
            }
        }

        void backtrack(int blevel)
        {
            sharp_assert(blevel < dlevel);
            implication_queue.Clear();

            for (int i = dlevel; i > blevel; --i) {
                IntVector assignments = assignment_stack(i);
                for (int j = assignments.size() - 1; j >= 0; --j)
                    unset_variable (assignments[j]>>1);
                assignment_stack(i).clear();
            }

            dlevel = blevel;
            ++ stats.num_backtracks;

            if (hook != null)
                hook.OnBacktrack(blevel);
        }

        void set_svar_value(int s)
        {
            //Implication On the Network
            Variable var = variable(VID(s));
            //propagate forward
            for (int i = 0; i < var.outputs.size(); ++i)
                make_node_consistent(var.output(i));
            //justify backward
            make_node_consistent(s);

            //Implication On the clauses
            IntVector watched = watched_by (s ^ 1); //the neg watched
            for (int i = 0; i < watched.size(); ++i) {
                int cl_idx = (watched[i] >> 1);
                int w_idx = (watched[i] & 1);
                Clause cl = clause(cl_idx);
                int[] lits = cl.literals;
                sharp_assert (lits[w_idx] == (s ^ 1));
                int other_watch_lit = lits[1 - w_idx];
                int other_value = lit_value(other_watch_lit);
                if (other_value == 0) {
                    sharp_assert (variable(other_watch_lit>> 1).dlevel == dlevel);
                    queue_conflict(cl_idx, ImpType.CLAUSE);
                }
                else if (other_value != 1) {
                    int j;
                    for (j = 2; j < cl.num_lits; ++j)
                        if (lit_value(lits[j]) != 0)
                            break;
                    if (j < cl.num_lits) {
                        //found another non-0 lit
                        int temp = lits[j];
                        lits[j] = lits[w_idx];
                        lits[w_idx] = temp;
                        watched_by(temp).push_back(cl_idx + cl_idx + w_idx);
                        watched[i] = watched.back;
                        watched.pop_back();
                        -- i;
                    }
                    else
                        queue_implication(other_watch_lit, cl_idx, ImpType.CLAUSE);
                }
            }
        }

        internal int new_pi()
        {
            int s = new_node( NodeType.PI, INVALID, INVALID);
            primary_inputs.push_back(s);
            node_to_pi_hash[s] = primary_inputs.size() - 1;
            return s;
        }

        internal int nth_pi(int n)
        {
            while (num_pi() <= n)
                new_pi();
            return pi(n);
        }


        internal int left_child (int s) { return node(s).left; }
        internal int right_child (int s){ return node(s).right; }

        internal int band (int i1, int i2)
        {
            int l = canonical (i1);
            int r = canonical (i2);
            int result =  create( NodeType.AND, l, r );
            //          dump_file.WriteLine ("{0} = AND {1} {2}", result, i1, i2);
            return result;
        }

        internal int bxor (int i1, int i2)
        {
            int l = canonical (i1);
            int r = canonical (i2);
            int result = create( NodeType.XOR, l, r );
            //          dump_file.WriteLine ("{0} = XOR {1} {2}", result, i1, i2);
            return result;
        }

        internal int  bor  (int i1, int i2) { return NEGATE( band( NEGATE(i1), NEGATE(i2)) );}
        internal int    bequ (int i1, int i2)   { return NEGATE( bxor( i1, i2 ));}
        internal int    bimp (int i1, int i2)   { return bor (NEGATE(i1), i2);}
        internal int    bnot (int i)            { return NEGATE(i); }

        //
        //Create a node. Don't do recursive optimization. But do lookup and simplification
        //if possible.
        // 
        int create_op_node(NodeType op, int i1, int i2)
        {
            if (op == NodeType.AND) {
                if (i1 == zero() || i2 == zero() || i1 == NEGATE(i2))
                    return zero();
                if (i1 == one())
                    return i2;
                if (i2 == one())
                    return i1;
                if (i1 == i2)
                    return i1;
            }
            else {
                sharp_assert (op == NodeType.XOR);
                if (i1 == zero())
                    return i2;
                if (i1 == one())
                    return NEGATE(i2);
                if (i2 == zero())
                    return i1;
                if (i2 == one())
                    return NEGATE(i1);
                if (i1 == i2)
                    return zero();
                if (i1 == NEGATE(i2))
                    return one();
            }

            int r = node_hash.lookup(op, i1, i2);
            if (r != INVALID)
                return r;

            r = create_op_node2(op, i1, i2);

            return r;
        }

        //
        //create an op node, Do recursive optimization and other possible optimizations
        // 
        int create (NodeType op, int i1, int i2)
        {
            if (op == NodeType.AND) {
                if (i1 == zero() || i2 == zero() || i1 == NEGATE(i2))
                    return zero();
                if (i1 == one())
                    return i2;
                if (i2 == one())
                    return i1;
                if (i1 == i2)
                    return i1;
            }
            else {
                sharp_assert (op == NodeType.XOR);
                if (i1 == zero())
                    return i2;
                if (i1 == one())
                    return NEGATE(i2);
                if (i2 == zero())
                    return i1;
                if (i2 == one())
                    return NEGATE(i1);
                if (i1 == i2)
                    return zero();
                if (i1 == NEGATE(i2))
                    return one();
            }

            int r = node_hash.lookup(op, i1, i2);

            if (r != INVALID)
                return r;

            //          r = create_op_node2(op, i1, i2);
            if (is_pi(i1) && is_pi(i2))
                r = create_op_node2(op, i1, i2);
            else if (is_pi(i1) || is_pi(i2))
                r = create_op_node3(op, i1, i2);
            else
                r = create_op_node4(op, i1, i2);

            return r;
        }

        int get_signature4(NodeType op, int l, int r)
        {
            int sig = 0;
            int ll = node(l).left;
            int lr = node(l).right;

            int rl = node(r).left;
            int rr = node(r).right;

            sharp_assert ( ll < lr );
            sharp_assert ( rl < rr );
            sharp_assert ( ll < rl || ll == rl ); // to reduce lookup table size

            if (IS_NEGATED(ll))        sig |= (1 << 0);
            if (IS_NEGATED(lr))        sig |= (1 << 1);
            if (IS_NEGATED(rl))        sig |= (1 << 2);
            if (IS_NEGATED(rr))        sig |= (1 << 3);
            if (IS_NEGATED(l))         sig |= (1 << 4);
            if (IS_NEGATED(r))         sig |= (1 << 5);
            if (node(l).type == NodeType.XOR)  sig |= (1 << 6);
            if (node(r).type == NodeType.XOR)  sig |= (1 << 7);
            if (op == NodeType.XOR)        sig |= (1 << 8);

            int v_ll = NODE_ID( ll );
            int v_lr = NODE_ID( lr );
            int v_rl = NODE_ID( rl );
            int v_rr = NODE_ID( rr );

            if (v_lr < v_rl)        sig |= (0 << 9);   //a < b < c < d
            else if (v_lr == v_rl)  sig |= (1 << 9);   //a < b = c < d
            else if (v_lr < v_rr) {
                if (v_ll < v_rl)   sig |= (2 << 9);       //a < c < b < d
                else            sig |= (3 << 9);   //a = c < b < d
            }
            else if (v_lr == v_rr) {
                if (v_ll < v_rl)   sig |= (4 << 9);       //a < c < b = d
                else            sig |= (5 << 9);   //a = c < b = d
            }
            else {
                // v_lr > v_rr
                if (v_ll < v_rl)   sig |= (6 << 9);       //a < c < d < b
                else            sig |= (7 << 9);   //a = c < d < b
            }
            return sig;
        }

        int  get_signature3(NodeType op, int l, int r)
        {
            //Functions that contains 3 operands:
            //it is assumed that the structure is like this:
            //               o
            //             l    (op)  r
            //        ll (op1) lr
            int sig = 0;
            sharp_assert (!is_pi(l));
            sharp_assert (is_pi(r));
            int ll = node(l).left;
            int lr = node(l).right;

            sharp_assert (ll < lr);

            if (IS_NEGATED(ll))        sig |= (1 << 0);
            if (IS_NEGATED(lr))        sig |= (1 << 1);
            if (IS_NEGATED(l))         sig |= (1 << 2);
            if (IS_NEGATED(r))         sig |= (1 << 3);
            if (node(l).type == NodeType.XOR)  sig |= (1 << 4);
            if (op == NodeType.XOR)        sig |= (1 << 5);

            int v_r = NODE_ID(r);
            int v_ll = NODE_ID(ll);
            int v_lr = NODE_ID(lr);

            if (v_r > v_lr)        sig |= (0 << 6);   //a < b < c
            else if (v_r == v_lr)  sig |= (1 << 6);   //a < b = c
            else if (v_ll < v_r)   sig |= (2 << 6);   //a < c < b
            else if (v_ll == v_r)  sig |= (3 << 6);   //a = c < b
            else            sig |= (4 << 6);   //c < a < b

            return sig;
        }

        //
        //Create an op node and add it to hash table.
        //Just do it, don't do lookup or simplification
        // 
        int create_op_node2(NodeType op, int i1, int i2)
        {
            sharp_assert (op == NodeType.AND || op == NodeType.XOR);

            // do need to make it canonical
            //1. left input always has smaller index than right
            if (i1 > i2) {
                int temp = i1;
                i1 = i2;
                i2 = temp;
            }
            //2. For XOR gate, both of its input must be in positive phase
            bool do_NEGATE = false;
            if (op == NodeType.XOR) {
                if (IS_NEGATED(i1)) {
                    i1 = NEGATE(i1);
                    do_NEGATE = !do_NEGATE;
                }
                if (IS_NEGATED(i2)) {
                    i2 = NEGATE(i2);
                    do_NEGATE = !do_NEGATE;
                }
            }

            int o = new_node(op, i1, i2);
            sharp_assert (o > i1 && o > i2);

            node(i1).outputs.push_back(o);      //i.e. the sign is 0: Left child
            node(i2).outputs.push_back(NEGATE(o));  //i.e. the sign is 1: Right child
            reference (i1);
            reference (i2);

            //add it to the hash
            node_hash.insert( o, op, i1, i2);

            //return the actual result
            if (do_NEGATE)
                o = NEGATE(o);

            return o;
        }

        //
        //Create a node, one of its inputs is a PI
        // 
        int create_op_node3(NodeType op, int i1, int i2)
        {
            if (is_pi(i1)) {
                sharp_assert (!is_pi(i2));
                int temp = i2;
                i2 = i1;
                i1 = temp;
            }

            int sig = get_signature3(op, i1, i2);
            int r = look_up_3_input_node ( op, i1, i2, sig);
            return r;
        }

        //
        //Create a node, none of its inputs is PI
        // 
        int create_op_node4(NodeType op, int i1, int i2)
        {
            if (node(i1).left > node(i2).left) {
                int temp = i1;
                i1 = i2;
                i2 = temp;
            }

            int sig = get_signature4(op, i1, i2);
            int r = look_up_4_input_node ( op, i1, i2, sig);
            return r;
        }

        //
        //Merge two ints, always keep the one() with smaller index
        // 
        int merge (int i1, int i2)
        {
            return real_merge(canonical(i1), canonical(i2));
        }

        int real_merge(int i1, int i2)
        {
            if (i1 == i2)
                return i1;
            else if (i1 == NEGATE(i2))
                return INVALID;

            if (i1 > i2) {
                int temp = i2;
                i2 = i1;
                i1 = temp;
            }

            for (int i = 0; i < node(i2).outputs.size(); ++i) {
                int o = node(i2).output(i);
                int output = NON_NEGATED (o);
                int l_r = SIGN(o); //the left or the right input
                int other_input = node(output).input(1 - l_r);
                if (node(output).input(l_r) == i2) {
                    int r_node = create (node(output).type, i1, other_input);
                    real_merge(r_node, output);
                }
                else {
                    sharp_assert (node(output).input(l_r) == NEGATE(i2));
                    int r_node = create (node(output).type, NEGATE(i1), other_input);
                    real_merge(r_node, output);
                }
            }

            node(i2).outputs.clear();

            if (IS_NEGATED(i2))
                node(i2).canonical = NEGATE(i1);
            else
                node(i2).canonical = i1;

            return i1;
        }

        internal void reference(int lit)
        {
            variable(lit>>1).ref_count ++;
        }

        internal void deref (int lit)
        {
            //          if (--variable(VID (lit)).ref_count != 0)
            //              return;
            //
            //          IntVector to_be_processed = new IntVector(16);
            //          to_be_processed.push_back(VID (lit));
            //          for (int i=0; i< to_be_processed.size(); ++i)
            //          {
            //              int vid = to_be_processed[i];
            //              Variable var = variable(vid);
            //              if (var.is_gate())
            //              {
            //                  for (int j=0; j< 2; ++j)
            //                  {
            //                      int vin = (j==0)? VID(var.left): VID(var.right);
            //                      Variable var_in =  variable(vin);
            //                      int size = var_in.outputs.size();
            //                      for (int k=0; k< size; ++k)
            //                      {
            //                          if (VID(var_in.output(k)) == vid)
            //                          {
            //                              var_in.outputs[k] = var_in.outputs.back;
            //                              var_in.outputs.pop_back();
            //                              break;
            //                          }
            //                      }
            //                      sharp_assert (size > var_in.outputs.size());
            //                      if ( --var_in.ref_count == 0)
            //                          to_be_processed.push_back(vin);
            //                  }
            //              }
            //          }
            //          free_nodes.add (to_be_processed);
        }
        //
        //Compose: i.e. replace some ints with other ints
        //input : the output node and the replacement correspondence
        //output: the result of the composition
        // 
        internal int compose ( int output, int [] orig, int [] replace)
        {
            sharp_assert (orig.Length == replace.Length);

            if (node(output).type == NodeType.CONSTANT)
                return output;

            MyHashtable sig_map = new MyHashtable();
            for (int i = 0; i < orig.Length; ++i) {
                int s_orig = orig[i];
                int s_new = replace[i];
                if (IS_NEGATED(s_orig)) {
                    s_orig = NEGATE(s_orig);
                    s_new = NEGATE(s_new);
                }
                sig_map[s_orig] = s_new;
            }
            return real_compose(canonical(output), sig_map);
        }

        int real_compose(int old, MyHashtable sig_map )
        {
            int result;

            bool invert = false;

            if (IS_NEGATED(old)) {
                old = NEGATE(old);
                invert = true;
            }
            object item = sig_map[old];
            if (item != null)
                result = (int) item;
            else {
                if (is_pi(old))    //so, if a pi is not replaced, use it as is
                    result  = old;
                else {
                    int left = real_compose(node(old).left, sig_map);
                    int right = real_compose(node(old).right, sig_map);
                    result = create(node(old).type, left, right);
                    sig_map[old] = result;
                }
            }
            return (invert ? NEGATE(result): result);
        }

        internal int gen_interpolant_from_clauses(int gid1, int gid2)
        {
            clean_up();
            rtrace.enable_trace(true);
            SATStatus status = solve();
            rtrace.enable_trace(false);
            reset();

            if (status != SATStatus.UNSATISFIABLE)
                return -1;
            return rtrace.gen_interpolant_from_clauses (gid1, gid2);
        }

        internal int gen_interpolant_from_signals(int s1, int s2)
        {
            clean_up();

            int gid = alloc_gid();
            int [] cl1 = new int [] {s1};
            int c_1 = add_clause(cl1, gid);
            int [] cl2 = new int [] {s2};
            int c_2 = add_clause(cl2, gid);

            rtrace.enable_trace(true);
            SATStatus status = solve();
            rtrace.enable_trace(false);
            reset();

            int r;
            if (status != SATStatus.UNSATISFIABLE)
                r =  -1;
            else
                r = rtrace.gen_interpolant_from_signals (s1, c_1, s2, c_2);
            delete_clause_group(gid);
            return r;
        }

        // gretay - change start
        internal int gen_interpolant_from_signals_ex(int s1, int s2)
        {
            // don't cleanup because conflict clauses
            //clean_up();

            int gid = alloc_gid();
            int [] cl1 = new int [] {s1};
            int c_1 = add_clause(cl1, gid, false);
            int [] cl2 = new int [] {s2};
            int c_2 = add_clause(cl2, gid, false);

            rtrace.enable_trace(true);
            SATStatus status = solve();
            rtrace.enable_trace(false);
            reset();

            int r;
            if (status != SATStatus.UNSATISFIABLE)
                r =  -1;
            else
                r = rtrace.gen_interpolant_from_signals_ex (s1, c_1, s2, c_2, c_cls_id.ToArray(), c_interp.ToArray());
            return r;
        }

        Hashtable interpolants = new Hashtable();  // maps clause_uid to signal that describes the interpolant provided for that clause
        IntVector c_cls_id = new IntVector(4);
        IntVector c_interp = new IntVector(4);

        public bool has_interpolant(int cl_uid)
        {
            return interpolants.Contains(cl_uid);
        }
        public void set_interpolant(int cl_uid, int interp)
        {
            Debug.Assert(!has_interpolant(cl_uid));
            interpolants[cl_uid] = interp;
            c_cls_id.push_back(cl_uid);
            c_interp.push_back(interp);
        }
        public int  get_interpolant_by_clause_uid(int cl_uid)
        {
            Debug.Assert(has_interpolant(cl_uid));
            return (int) interpolants[cl_uid];
        }
        // end gretay - change end

        internal UnsatCore gen_unsat_core ()
        {
            clean_up();
            rtrace.enable_trace(true);
            SATStatus status = solve();
            rtrace.enable_trace(false);

            if (status != SATStatus.UNSATISFIABLE)
                return null;

            MyHashtable hash = rtrace.generate_unsat_core();
            UnsatCore core = new UnsatCore();
            IntVector core_cls = new IntVector(4);
            IntVector core_nodes = new IntVector(4);
            for (int i = 0; i < clauses.size(); ++i) {
                Clause cl = clause(i);
                if (cl == null)
                    continue;
                if (hash.Contains(cl.uid)) {
                    sharp_assert (cl.type == ClType.ORIGINAL);
                    core_cls.push_back (i);
                }
            }
            for (int i = 1; i < variables.size(); ++i) {
                Variable v = variable(i);
                if (hash.Contains(v.uid)) {
                    sharp_assert (v.type == NodeType.AND || v.type == NodeType.XOR);
                    core_nodes.push_back ( i + i);
                }
            }
            core.core_clauses = core_cls.ToArray();
            core.core_nodes = core_nodes.ToArray();
            return core;
        }

        void dump_unsat_core( string filename)
        {
            StreamWriter writer = new StreamWriter(filename);
            UnsatCore core = gen_unsat_core();

            writer.WriteLine ("p cnf {0} {1} ", num_variables() , core.core_clauses.Length);
            foreach (int cl_id in core.core_clauses) {
                foreach (int lit in clause(cl_id).literals) {
                    if ((lit & 1) == 1)
                        writer.Write("-");
                    writer.Write ("{0} ", lit>>1);
                }
                writer.WriteLine ("0");
            }
            writer.Close();
            if (core.core_nodes.Length != 0) {
                Console.WriteLine ("Warning: Contains Nodes in the UNSAT core " );
                foreach (int s in core.core_nodes) {
                    Console.Write ("{0} ", s);
                }
                Console.WriteLine("");
            }
        }

        internal void dump_node (StreamWriter wt, int s)
        {
            int flag = alloc_flag();
            mark_transitive_fanins(s, flag);
            for (int i = 1; i < variables.size(); ++i) {
                Variable var = variable(i);
                if (var.flag(flag)) {
                    switch (var.type) {
                        case NodeType.PI:
                            wt.WriteLine("{0} = PI", i + i);
                            break;
                        case NodeType.AND:
                            wt.WriteLine("{0} = AND {1} {2}", i + i, var.left, var.right);
                            break;
                        case NodeType.XOR:
                            wt.WriteLine("{0} = XOR {1} {2}", i + i, var.left, var.right);
                            break;
                    }
                }
            }
            free_flag(flag);
        }

        internal int get_structure (SharpSATSolver solver, int output)
        {
            int f = solver.alloc_flag();
            solver.mark_transitive_fanins(output,f);
            int [] lookup = new int [solver.variables.size() * 2];
            for (int i = 0; i < lookup.Length; ++i)
                lookup[i] = -1;
            for (int i = 1; i < solver.variables.size(); ++i) {
                Variable var = solver.variable(i);
                if (!var.flag(f))
                    continue;
                int l = var.left;
                int r = var.right;
                int s ;
                switch (var.type) {
                    case NodeType.AND:
                        sharp_assert (solver.node(l).flag(f));
                        sharp_assert (solver.node(r).flag(f));
                        sharp_assert (lookup[l] != -1);
                        sharp_assert (lookup[r] != -1);
                        s = band(lookup[l], lookup[r]);
                        //                      sharp_assert (node(s).left == lookup[l]);
                        //                      sharp_assert (node(s).right == lookup[r]);
                        lookup[i + i] = s;
                        lookup[i + i + 1] = s ^ 1;
                        break;
                    case NodeType.XOR:
                        sharp_assert (solver.node(l).flag(f));
                        sharp_assert (solver.node(r).flag(f));
                        sharp_assert (lookup[l] != -1);
                        sharp_assert (lookup[r] != -1);
                        s = bxor(lookup[l], lookup[r]);
                        //                      sharp_assert (node(s).left == lookup[l]);
                        //                      sharp_assert (node(s).right == lookup[r]);
                        lookup[i + i] = s;
                        lookup[i + i + 1] = s ^ 1;
                        break;
                    case NodeType.PI:
                        s = new_pi();
                        lookup[i + i] = s;
                        lookup[i + i + 1] = s ^ 1;
                        break;
                    default:
                        sharp_assert(false);
                        break;
                }
            }
            return lookup[output];
        }

        internal void dump_original_clauses ( StreamWriter wt )
        {
//          IntVector originals = new IntVector(128);
//          foreach (object k in original_clauses.Keys)
//              originals.push_back((int)k);
//          originals.sort();
            for (int i = 0; i < original_clauses.size(); ++i) {
                int cl_id = original_clauses[i];
                sharp_assert (clause(cl_id).type == ClType.ORIGINAL);
                wt.Write ("{0} = CL", i);
                foreach (int lit in clause(cl_id).literals)
                    wt.Write(" {0}", lit);
                wt.Write("\n");
            }
        }
        // =========================================================================
//
        //Simulation Etc. on the Boolean Network
//
        // =========================================================================   
        internal IntVector mark_transitive_fanouts(int s, int flag_id)
        {
            IntVector to_be_processed = new IntVector(64);
            to_be_processed.push_back(s);
            node(s).set_flag(flag_id);
            for (int i = 0; i < to_be_processed.size(); ++i) {
                Variable nd = node (to_be_processed[i]);
                for (int j = 0, sz = nd.outputs.size(); j < sz; ++j)
                    if (node(nd.output(j)).flag(flag_id) == false)
                    {
                        node(nd.output(j)).set_flag(flag_id);
                        to_be_processed.push_back(nd.output(j));
                    }
            }
            return to_be_processed;
        }

        internal IntVector find_transitive_fanins  (int s)
        {
            int flag = alloc_flag();
            IntVector result = mark_transitive_fanins(s, flag);
            free_flag(flag);
            return result;
        }

        internal IntVector mark_transitive_fanins(IntVector to_be_processed, int flag_id)
        {
            for (int i = 0, sz = to_be_processed.size(); i < sz; ++i) {
                Variable nd = node (to_be_processed[i]);
                nd.set_flag(flag_id);
            }
            for (int i = 0; i < to_be_processed.size(); ++i) {
                Variable nd = node (to_be_processed[i]);
                if (nd.left == INVALID || nd.right == INVALID) {
                    sharp_assert (nd.left == INVALID && nd.right == INVALID);
                    continue;
                }
                if (node(nd.left).flag(flag_id) == false) {
                    node(nd.left).set_flag(flag_id);
                    to_be_processed.push_back(nd.left);
                }
                if (node(nd.right).flag(flag_id) == false) {
                    node(nd.right).set_flag(flag_id);
                    to_be_processed.push_back(nd.right);
                }
            }
            return to_be_processed;
        }

        internal IntVector mark_transitive_fanins(int s, int flag_id)
        {
            sharp_assert (s != INVALID);
            if (node(s).type == NodeType.CONSTANT)
                return null;
            IntVector to_be_processed = new IntVector(4);
            to_be_processed.push_back(s);
            node(s).set_flag(flag_id);
            for (int i = 0; i < to_be_processed.size(); ++i) {
                Variable nd = node (to_be_processed[i]);
                if (nd.left == INVALID || nd.right == INVALID) {
                    sharp_assert (nd.left == INVALID && nd.right == INVALID);
                    continue;
                }

                if (node(nd.left).flag(flag_id) == false) {
                    node(nd.left).set_flag(flag_id);
                    to_be_processed.push_back(nd.left);
                }
                if (node(nd.right).flag(flag_id) == false) {
                    node(nd.right).set_flag(flag_id);
                    to_be_processed.push_back(nd.right);
                }
            }
            return to_be_processed;
        }

        public int [] find_small_model()
        {
            return find_small_model_greed();
        }

        private int [] find_small_model_greed ()
        {
            sharp_assert ( stats.outcome == SATStatus.SATISFIABLE);
            sharp_assert ( stats.num_free_branch_vars == 0);
            int f = alloc_flag();
            //1. collect all the lits that needs to be true for clauses
            for (int i = 0; i < clauses.size(); ++i) {
                if (clauses[i] == null || clauses[i].type == ClType.CONFLICT) //??? is this correct, do we need to satisfy the temp clauses?
                    continue;
                bool cls_sat = false;
                foreach (int lit in clause(i).literals) {
                    if (lit_value(lit) == 1) {
                        variable(VID(lit)).set_flag(f);
                        cls_sat = true;
                        break;
                    }
                }
                if (cls_sat == false) {
                    fatal ("A clause does not contain true lit even though formula is SAT");
                }
            }
            //now traverse the tree in reverse topological order
            for (int i = variables.size() - 1; i > 0; --i) {
                Variable var = variable(i);
                if (!var.flag(f))
                    continue;
                sharp_assert (var_value(i) != UNKNOWN);
                switch (var.type) {
                    case NodeType.AND:
                        if (var_value(i) == 1) //both inputs must be true
                        {
                            sharp_assert (lit_value(var.left) == 1);
                            sharp_assert (lit_value(var.right) == 1);
                            variable(VID(var.left)).set_flag(f);
                            variable(VID(var.right)).set_flag(f);
                        }
                        else {
                            sharp_assert (var_value(i) == 0);
                            if (lit_value(var.left) == 0)
                                variable(VID(var.left)).set_flag(f);
                            else if (lit_value(var.right) == 0)
                                variable(VID(var.right)).set_flag(f);
                            else
                                fatal ("Variable unjustifiable");
                        }
                        break;
                    case NodeType.XOR:
                        variable(VID(var.left)).set_flag(f);
                        variable(VID(var.right)).set_flag(f);
                        break;
                    default:
                        break;
                }
            }
            IntVector cube = new IntVector(16);
            for (int i = 0; i < variables.size(); ++i) {
                if (variable(i).flag(f)) {
                    sharp_assert (var_value(i) != UNKNOWN);
                    cube.push_back (i + i + 1 - var_value(i));
                }
            }
            free_flag(f);
            return cube.ToArray();
        }

        private class EnumQuantification
        {
            SharpSATSolver solver;

            IntVector visiting_queue;
            IntVector blocking_lits;
            int bound_flag;
            int visited_flag;
            int occ_flag ;
            int sign_flag ;
            IntVector involved_signals;
            Hashtable blocking_clauses;

            ObjVector cls_occurrence;

            Variable variable(int vid) { return solver.variable(vid); }
            Variable node(int lit) { return solver.node(lit); }
            Clause clause (int id) { return solver.clause(id); }
            int band (int a, int b) { return solver.band(a, b); }
            int bor (int a, int b) { return solver.bor(a, b); }
            int alloc_flag () { return solver.alloc_flag(); }

            [Microsoft.Contracts.NotDelayed]
            public EnumQuantification(SharpSATSolver sol)
            {
                solver = sol;
                visiting_queue  = new IntVector(128);
                blocking_lits   = new IntVector(64);
                involved_signals= new IntVector(128);
                cls_occurrence  = new ObjVector(128);
                blocking_clauses= new Hashtable();
                bound_flag      = solver.alloc_flag();
                visited_flag    = solver.alloc_flag();
                occ_flag        = solver.alloc_flag();
                sign_flag       = solver.alloc_flag();
            }

            void finalize_quantification ()
            {
                solver.free_flag (visited_flag);
                solver.free_flag(bound_flag);
                solver.free_flag(occ_flag);
                solver.free_flag(sign_flag);
            }

            void init_quantification (int s, int [] bounded, bool block_with_pi_only)
            {

                involved_signals = solver.find_transitive_fanins(s);
                if (block_with_pi_only) {
                    foreach (int sig in bounded) {
                        sharp_assert (node(sig).is_pi());
                        node(sig).set_flag(bound_flag);
                    }
                    for (int i = 0; i < involved_signals.size(); ++i) {
                        Variable var = node(involved_signals[i]);
                        if (!var.is_pi())
                            var.set_flag(bound_flag);
                    }
                }
                else {
                    foreach (int sig in bounded) {
                        sharp_assert (node(sig).is_pi());
                        solver.mark_transitive_fanouts(sig,bound_flag);
                    }
                }

                cls_occurrence = new ObjVector(solver.variables.size());
                for (int i = 0; i < involved_signals.size(); ++i)
                    cls_occurrence[VID(involved_signals[i])] = new IntVector(4);
            }

            int build_balanced_or (int [] signals, int start, int end)
            {
                if (signals.Length == 0)
                    return solver.zero();
                else if (start == end)
                    return signals[start];
                else {
                    int middle = (end - start) /2 + start;
                    int s1 = build_balanced_or(signals, start, middle);
                    int s2 = build_balanced_or(signals, middle + 1, end);
                    return bor (s1, s2);
                }
            }

            int build_balanced_and (int [] signals, int start, int end)
            {
                if (signals.Length == 0)
                    return solver.one();
                else if (start == end)
                    return signals[start];
                else {
                    int middle = (end - start) /2 + start;
                    int s1 = build_balanced_and(signals, start, middle);
                    int s2 = build_balanced_and(signals, middle + 1, end);
                    return band (s1, s2);
                }
            }

            int build_struct_balanced (IntVector cls_ids)
            {
                int [] cl_sigs = new int[cls_ids.size()];
                for (int i = 0; i < cls_ids.size(); ++i) {
                    int [] lits = clause(cls_ids[i]).literals;
                    cl_sigs[i] = build_balanced_or ( lits, 0, lits.Length - 1);
                }
                int result = build_balanced_and(cl_sigs, 0, cl_sigs.Length - 1);
                return result;
            }


            int build_struct (IntVector cls)
            {
                //return build_struct_simple(cls);
                return build_struct_balanced (cls);
            }

            int build_struct_simple(IntVector cls)
            {
                int sig = solver.one();
                for (int i = 0; i < cls.size(); ++i) {
                    int s = solver.zero();
                    foreach (int lit in clause(cls[i]).literals)
                        s = bor(s, lit);
                    sig = band(sig, s);
                }
                return sig;
            }

            static IntVector intersect (IntVector a, IntVector b)
            {
                IntVector result = new IntVector(4);
                for (int i = 0, j = 0; i < a.size() && j < b.size();) {
                    if (a[i] < b[j])
                        ++ i;
                    else if (a [i] > b[j])
                        ++ j;
                    else {
                        result.push_back (a[i]);
                        ++i;
                        ++j;
                    }
                }
                return result;
            }

            IntVector resolve (IntVector a, int [] b)
            {
                IntVector result = new IntVector(b.Length - 1);
                sharp_assert (a.size() == b.Length);
                foreach (int lit in b) {
                    Variable var = variable (VID(lit));
                    var.set_flag (occ_flag);
                    if (IS_NEGATED(lit))
                        var.set_flag (sign_flag);
                }
                for (int i = 0; i < a.size(); ++i) {
                    int lit = a[i];
                    Variable var = variable (VID(lit));
                    sharp_assert (var.flag(occ_flag));
                    if (var.flag(sign_flag) == IS_NEGATED(lit))
                        result.push_back(lit);
                    var.clear_flag (occ_flag);
                    var.clear_flag (sign_flag);
                }
                if (result.size() == a.size() - 1)
                    return result;
                else
                    return null;
            }

            bool subsume (IntVector a, int [] b)
            {
                sharp_assert (a.size() < b.Length);
                for (int i = 0; i < a.size(); ++i) {
                    int lit = a[i];
                    Variable var = variable (VID(lit));
                    var.set_flag (occ_flag);
                    if (IS_NEGATED(lit))
                        var.set_flag (sign_flag);
                }
                int same_lit = 0;
                int same_var = 0;
                foreach (int lit in b) {
                    Variable var = variable (VID(lit));
                    if (var.flag(occ_flag)) {
                        same_var ++;
                        if (IS_NEGATED(lit) == var.flag(sign_flag))
                            same_lit ++;
                        var.clear_flag (occ_flag);
                        var.clear_flag (sign_flag);
                    }
                }
                sharp_assert (same_var == a.size());
                return (same_lit == same_var);
            }

            void remove_blocking (int cl_id)
            {
                blocking_clauses.Remove(cl_id);
                foreach (int lit in solver.clause(cl_id).literals) {
                    int vid = VID(lit);
                    IntVector occur = (IntVector)cls_occurrence[vid];
                    int i;
                    for (i = 0; occur[i] != cl_id; ++i);
                    for (i = i + 1; i < occur.size(); ++i)
                        occur[i-1] = occur[i];
                    occur.pop_back();
                }

                Clause cl = solver.clause(cl_id);
                if (cl.num_lits > 1)
                    solver.remove_cl_from_reasoning (cl_id);


                for (int i = 0; i < cl.num_lits; ++i)
                    solver.decr_lits_count(cl.literal(i));

                ++ solver.stats.num_deleted_clauses;
                solver.stats.num_deleted_literals += cl.num_lits;
                solver.clauses[cl_id] = null;
                solver.free_clauses.push_back(cl_id);
            }

            void add_blocking (int gid)
            {
                int cl_id = solver.add_blocking_clause(blocking_lits.ToArray(), gid);
                for (int i = 0; i < blocking_lits.size(); ++i) {
                    int lit = blocking_lits[i];
                    IntVector occ_array = (IntVector) cls_occurrence[VID(lit)];
                    occ_array.push_back(cl_id);
                    //bubble down
                    for (int j = occ_array.size() - 2; j >= 0; --j) {
                        if (occ_array[j] > cl_id) {
                            occ_array[j+1] = occ_array[j];
                            occ_array[j] = cl_id;
                        }
                        else
                            break;
                    }
                }
                blocking_clauses.Add(cl_id, null);
            }

            int n_tab = 1;
            void tab () { for (int i=0; i< n_tab; ++i) Console.Write("  "); }

            void dump_lits (int [] a)
            {
                IntVector cp = new IntVector (4);
                foreach (int lit in a)
                    cp.push_back(lit);
                cp.sort();
                for (int i = 0; i < cp.size(); ++i)
                    Console.Write ("{0}{1}", IS_NEGATED(cp[i])?" -":" +", VID(cp[i]));
                Console.WriteLine("");
            }

            void dump_lits (IntVector a)
            {
                IntVector cp = new IntVector (4);
                for (int i = 0; i < a.size(); ++i)
                    cp.push_back(a[i]);
                cp.sort();
                for (int i = 0; i < cp.size(); ++i)
                    Console.Write ("{0}{1}", IS_NEGATED(cp[i])?" -":" +", VID(cp[i]));
                Console.WriteLine("");
            }

            void try_reduce()
            {
                if (blocking_lits.size() == 0)
                    return;
//              tab(); System.Console.Write ("Try to Reduce ");dump_lits(blocking_lit); ++ n_tab;

                IntVector common = new IntVector((IntVector) cls_occurrence[VID(blocking_lits[0])]);
                for (int i = 1; i < blocking_lits.size(); ++i) {
                    int vid = VID(blocking_lits[i]);
                    IntVector next = (IntVector) cls_occurrence[vid];
                    common = intersect (common, next);
                }
                bool resolved = false;
                for (int i = 0; i < common.size(); ++i) {
                    int cl_id = common[i];
                    int [] lits = solver.clause(cl_id).literals;
                    sharp_assert (lits.Length >= blocking_lits.size());
                    if (lits.Length > blocking_lits.size()) {
                        if (subsume (blocking_lits, lits)) {
//                          tab();Console.Write ("Subsume CL:{0} ->", cl_id); dump_lits(lits);
                            remove_blocking (cl_id);
                        }
                    }
                    else {
                        IntVector r = resolve (blocking_lits, lits);
                        if (r != null) {
//                          tab();Console.Write ("Resolve CL:{0} ->", cl_id); dump_lits(lits);
                            resolved = true;
                            blocking_lits = r;
                            remove_blocking (cl_id);
                            break;
                        }
                    }
                }
                if (resolved)
                    try_reduce();
                //-- n_tab;
            }

            bool find_blocking_cls (int s)
            {
                blocking_lits.clear();
                visiting_queue.clear();
                SATStatus status = solver.solve();
                if (status == SATStatus.UNSATISFIABLE)
                    return false;
                sharp_assert (status == SATStatus.SATISFIABLE);
                int vid = VID(s);
                visiting_queue.push_back( vid );
                variable(vid).set_flag(visited_flag);
                for (int i = 0; i < visiting_queue.size(); ++i) {
                    vid = visiting_queue[i];
                    Variable var = variable(vid);
                    if (!var.flag(bound_flag)) //so it doesn't depends on bounded vars.
                        blocking_lits.push_back(vid + vid + solver.var_value(vid));
                    else {
                        if (var.type == NodeType.PI)
                            continue;
                        if (var.type == NodeType.AND && solver.var_value(vid) == 0) {
                            int l;
                            if (solver.lit_value(var.left) != 0)
                                l = var.right;
                            else if (solver.lit_value(var.right) != 0)
                                l = var.left;
                            else {
                                // both inputs are 0
                                if (node(var.left).flag(visited_flag))
                                    l = var.left;
                                else if (node(var.right).flag(visited_flag))
                                    l = var.right;
                                else //neither has been visited
                                    l = var.left;
                            }
                            if (!node(l).flag(visited_flag)) {
                                node(l).set_flag(visited_flag);
                                visiting_queue.push_back(VID(l));
                            }
                        }
                        else {
                            sharp_assert (var.type == NodeType.XOR || var.type == NodeType.AND);
                            int l = var.left;
                            if (!node(l).flag(visited_flag)) {
                                node(l).set_flag(visited_flag);
                                visiting_queue.push_back(VID(l));
                            }
                            l = var.right;
                            if (!node(l).flag(visited_flag)) {
                                node(l).set_flag(visited_flag);
                                visiting_queue.push_back(VID(l));
                            }
                        }
                    }
                }
                for (int i = 0; i < visiting_queue.size(); ++i)
                    variable(visiting_queue[i]).clear_flag(visited_flag);
                return true;
            }

            public int enum_exist_quantify (int s, int [] bounded, bool block_with_pi_only)
            {
                int c = solver.constraint(s);
                int block_gid = solver.alloc_gid();
                init_quantification(s, bounded, block_with_pi_only);
                bool empty_cl = false;
                int total_solution = 0;
                //int total_clauses;
                while (find_blocking_cls(s)) {
                    //solver.restart();
                    ++ total_solution;
                    try_reduce();
                    if (blocking_lits.size() == 0) {
                        //blocking clause size 0, i.e. no literal
                        empty_cl = true;
                        break;
                    }
                    else
                        add_blocking(block_gid);
                }
                solver.release_constraint(c);
                int r;
                if (empty_cl)
                    r = solver.zero();
                else if (blocking_clauses.Count == 0)
                    r = solver.one();
                else {
                    IntVector blocking = new IntVector(4);
                    foreach (object k in blocking_clauses.Keys)
                        blocking.push_back((int)k);
                    //total_clauses = blocking.size();
                    r = build_struct (blocking);
                }
                solver.delete_clause_group(block_gid);
                finalize_quantification();
//              Console.WriteLine ("Enum {0} solutions, total blocking clauses {1}", total_solution, total_clauses);
                return solver.bnot(r);
            }

            public int enum_exist_quantify_dumb (int s, int [] bounded, bool with_pi_only)
            {
                if (node(s).type == NodeType.CONSTANT)
                    return s;

                int c = solver.constraint(s);
                int block_gid = solver.alloc_gid();
                init_quantification(s, bounded, with_pi_only);
                bool empty_cl = false;
                IntVector blocking = new IntVector(16);
                while (find_blocking_cls(s)) {
                    if (blocking_lits.size() == 0) {
                        //blocking clause size 0, i.e. no literal
                        empty_cl = true;
                        break;
                    }
                    else {
                        int cl_id = solver.add_blocking_clause(blocking_lits.ToArray(), block_gid);
                        blocking.push_back(cl_id);
                    }
                }
                solver.release_constraint(c);
                int r;
                if (empty_cl)
                    r = solver.zero();
                else if (blocking.size() == 0)
                    r = solver.one();
                else
                    r = build_struct (blocking);
                solver.delete_clause_group(block_gid);
                finalize_quantification();
                return solver.bnot(r);
            }
        }

        public int enum_exist_quantify_smart (int s, int [] bounded)
        {
            if (node(s).type == NodeType.CONSTANT)
                return s;

            EnumQuantification quant = new EnumQuantification(this);
            int r = quant.enum_exist_quantify (s, bounded, false);
            return r;
        }

        public int enum_exist_quantify_dumb (int s, int [] bounded)
        {
            EnumQuantification quant = new EnumQuantification(this);
            int r = quant.enum_exist_quantify_dumb (s, bounded, false);
            return r;
        }

        public int expand_exist_quantify (int s, int [] bounded)
        {
            int flag = alloc_flag();
            mark_transitive_fanins(s, flag);
            int result = s;
            foreach (int input in bounded) {
                sharp_assert (node(input).is_pi());
                int [] orig = { input };
                int [] replace = { zero() };
                int cofactor_i = compose(result, orig, replace);
                replace = new int [] { one () };
                int cofactor_ip = compose(result, orig, replace);
                result = bor (cofactor_i, cofactor_ip);
            }
            free_flag(flag);
            return result;
        }

        #region NODE_CONSISTENCY_LOOKUP
        void make_node_consistent (int s)
        {
            Variable n = node(s);
            if (!is_reasoning(n))
                return;

            int output = NON_NEGATED(s);
            int input0 = n.left;
            int input1 = n.right;

            int signature;
            signature = lit_value(output);
            signature = (signature << 2);
            signature |= lit_value(input0);
            signature = (signature << 2);
            signature |= lit_value(input1);

            if (n.type == NodeType.AND) {
                switch (signature) {
                    case 34:    //100010     : x0x
                    case 35:    //100011     : x0x
                    case 50:    //110010     : x0x
                    case 51:    //110011     : x0x
                    case 40:    //101000     : xx0
                    case 44:    //101100     : xx0
                    case 56:    //111000     : xx0
                    case 60:    //111100     : xx0
                    case 36:    //100100     : x10
                    case 52:    //110100     : x10
                    case 33:    //100001     : x01
                    case 49:    //110001     : x01
                    case 32:    //100000     : x00
                    case 48:    //110000     : x00
                        queue_implication(output^1, VID (output), ImpType.NODE);
                        break;
                    case 37:    //100101     : x11
                    case 53:    //110101     : x11
                        queue_implication(output, VID (output), ImpType.NODE);
                        break;
                    case 6:     //000110     : 01x
                    case 7:     //000111     : 01x
                        queue_implication(input1^1, VID (output), ImpType.NODE);
                        break;
                    case 13:    //001101     : 0x1
                    case 9:     //001001     : 0x1
                        queue_implication(input0^1, VID (output), ImpType.NODE);
                        break;
                    case 22:    //010110     : 11x
                    case 23:    //010111     : 11x
                        queue_implication(input1, VID (output), ImpType.NODE);
                        break;
                    case 29:    //011101     : 1x1
                    case 25:    //011001     : 1x1
                        queue_implication(input0, VID (output), ImpType.NODE);
                        break;
                    case 30:    //011110     : 1xx
                    case 31:    //011111     : 1xx
                    case 26:    //011010     : 1xx
                    case 27:    //011011     : 1xx
                        queue_implication(input0, VID (output), ImpType.NODE);
                        queue_implication(input1, VID (output), ImpType.NODE);
                        break;
                    case 18:    //010010     : 10x
                    case 19:    //010011     : 10x
                    case 24:    //011000     : 1x0
                    case 28:    //011100     : 1x0

                    case 17:    //010001     : 101
                    case 20:    //010100     : 110
                    case 16:    //010000     : 100
                    case 5:     //000101     : 011
                        queue_conflict(VID (output), ImpType.NODE);
                        break;
                    case 42:    //101010     : xxx
                    case 43:    //101011     : xxx
                    case 46:    //101110     : xxx
                    case 47:    //101111     : xxx

                    case 58:    //111010     : xxx
                    case 59:    //111011     : xxx
                    case 62:    //111110     : xxx
                    case 63:    //111111     : xxx
                        break;
                    case 41:    //101001     : xx1
                    case 45:    //101101     : xx1
                    case 57:    //111001     : xx1
                    case 61:    //111101     : xx1

                    case 38:    //100110     : x1x
                    case 39:    //100111     : x1x
                    case 54:    //110110     : x1x
                    case 55:    //110111     : x1x

                    case 2:     //000010     : 00x
                    case 3:     //000011     : 00x
                    case 8:     //001000     : 0x0
                    case 12:    //001100     : 0x0

                    case 10:    //001010     : 0xx
                    case 11:    //001011     : 0xx
                    case 14:    //001110     : 0xx
                    case 15:    //001111     : 0xx

                    case 21:    //010101     : 111
                    case 4:     //000100     : 010
                    case 1:     //000001     : 001
                    case 0:     //000000     : 000
                        break;
                }
            }
            else {
                sharp_assert (n.type == NodeType.XOR);
                switch (signature) {
                    case 32:    //100000     : x00
                    case 48:    //110000     : x00
                    case 37:    //100101     : x11
                    case 53:    //110101     : x11
                        queue_implication(output^1, VID (output), ImpType.NODE);
                        break;
                    case 33:    //100001     : x01
                    case 49:    //110001     : x01
                    case 36:    //100100     : x10
                    case 52:    //110100     : x10
                        queue_implication(output, VID (output), ImpType.NODE);
                        break;
                    case 3:     //000011     : 00x
                    case 2:     //000010     : 00x
                    case 23:    //010111     : 11x
                    case 22:    //010110     : 11x
                        queue_implication(input1^1, VID (output), ImpType.NODE);
                        break;
                    case 7:     //000111     : 01x
                    case 6:     //000110     : 01x
                    case 19:    //010011     : 10x
                    case 18:    //010010     : 10x
                        queue_implication(input1, VID (output), ImpType.NODE);
                        break;
                    case 13:    //001101     : 0x1
                    case 9:     //001001     : 0x1
                    case 28:    //011100     : 1x0
                    case 24:    //011000     : 1x0
                        queue_implication(input0, VID (output), ImpType.NODE);
                        break;
                    case 12:    //001100     : 0x0
                    case 8:     //001000     : 0x0
                    case 29:    //011101     : 1x1
                    case 25:    //011001     : 1x1
                        queue_implication(input0^1, VID (output), ImpType.NODE);
                        break;
                    case 1:     //000001     : 001
                    case 4:     //000100     : 010
                    case 16:    //010000     : 100
                    case 21:    //010101     : 111
                        queue_conflict(VID (output), ImpType.NODE);
                        break;
                    case 42:    //101010     : xxx
                    case 43:    //101011     : xxx
                    case 46:    //101110     : xxx
                    case 47:    //101111     : xxx
                    case 58:    //111010     : xxx
                    case 59:    //111011     : xxx
                    case 62:    //111110     : xxx
                    case 63:    //111111     : xxx
                        break;
                    case 41:    //101001     : xx1
                    case 45:    //101101     : xx1
                    case 57:    //111001     : xx1
                    case 61:    //111101     : xx1

                    case 40:    //101000     : xx0
                    case 44:    //101100     : xx0
                    case 56:    //111000     : xx0
                    case 60:    //111100     : xx0

                    case 38:    //100110     : x1x
                    case 39:    //100111     : x1x
                    case 54:    //110110     : x1x
                    case 55:    //110111     : x1x

                    case 34:    //100010     : x0x
                    case 35:    //100011     : x0x
                    case 50:    //110010     : x0x
                    case 51:    //110011     : x0x

                    case 10:    //001010     : 0xx
                    case 11:    //001011     : 0xx
                    case 14:    //001110     : 0xx
                    case 15:    //001111     : 0xx

                    case 26:    //011010     : 1xx
                    case 27:    //011011     : 1xx
                    case 30:    //011110     : 1xx
                    case 31:    //011111     : 1xx

                    case 20:    //010100     : 110
                    case 17:    //010001     : 101
                    case 5:     //000101     : 011
                    case 0:     //000000     : 000
                        break;
                }
            }
        }
        #endregion
        #region CANONICAL_TABLE_LOOKUP
        private static readonly int [] lookup_table_3_inputs =
            new int[320] {
                             /* 0 */  0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                             /* 10 */  10, 11, 12, 13, 14, 15, 16, 17, 17, 16,
                             /* 20 */  17, 16, 16, 17, 18, 19, 19, 18, 19, 18,
                             /* 30 */  18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
                             /* 40 */  24, 25, 26, 27, 20, 21, 22, 23, 28, 29,
                             /* 50 */  29, 28, 29, 28, 28, 29, 29, 28, 28, 29,
                             /* 60 */  28, 29, 29, 28, 30, 31, 32, 32, 31, 30,
                             /* 70 */  33, 33, 32, 32, 34, 35, 36, 36, 35, 34,
                             /* 80 */  31, 30, 30, 31, 30, 31, 31, 30, 34, 35,
                             /* 90 */  35, 34, 35, 34, 34, 35, 31, 30, 37, 38,
                             /* 100 */  39, 40, 35, 34, 39, 40, 35, 34, 31, 30,
                             /* 110 */  37, 38, 41, 42, 42, 41, 42, 41, 41, 42,
                             /* 120 */  42, 41, 41, 42, 41, 42, 42, 41, 43, 44,
                             /* 130 */  45, 46, 4, 5, 6, 7, 47, 48, 49, 50,
                             /* 140 */  12, 13, 14, 15, 16, 17, 17, 16, 17, 16,
                             /* 150 */  16, 17, 18, 19, 19, 18, 19, 18, 18, 19,
                             /* 160 */  20, 21, 22, 23, 24, 25, 26, 27, 24, 25,
                             /* 170 */  26, 27, 20, 21, 22, 23, 51, 52, 52, 51,
                             /* 180 */  52, 51, 51, 52, 52, 51, 51, 52, 51, 52,
                             /* 190 */  52, 51, 30, 32, 34, 32, 34, 41, 30, 41,
                             /* 200 */  32, 31, 32, 35, 42, 35, 42, 31, 34, 30,
                             /* 210 */  30, 34, 30, 34, 34, 30, 31, 35, 35, 31,
                             /* 220 */  35, 31, 31, 35, 34, 37, 30, 39, 38, 35,
                             /* 230 */  40, 31, 38, 35, 40, 31, 34, 37, 30, 39,
                             /* 240 */  33, 36, 36, 33, 36, 33, 33, 36, 36, 33,
                             /* 250 */  33, 36, 33, 36, 36, 33, 53, 54, 55, 56,
                             /* 260 */  4, 5, 6, 7, 57, 58, 59, 60, 12, 13,
                             /* 270 */  14, 15, 16, 17, 17, 16, 17, 16, 16, 17,
                             /* 280 */  18, 19, 19, 18, 19, 18, 18, 19, 20, 21,
                             /* 290 */  22, 23, 24, 25, 26, 27, 24, 25, 26, 27,
                             /* 300 */  20, 21, 22, 23, 61, 62, 62, 61, 62, 61,
                             /* 310 */  61, 62, 62, 61, 61, 62, 61, 62, 62, 61  };
        private static readonly int [] lookup_table_4_inputs =
            new int [4096] {
                               /* 0 */  0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                               /* 10 */  10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                               /* 20 */  20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
                               /* 30 */  30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
                               /* 40 */  40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
                               /* 50 */  50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
                               /* 60 */  60, 61, 62, 63, 64, 65, 65, 64, 66, 67,
                               /* 70 */  67, 66, 68, 69, 69, 68, 70, 71, 71, 70,
                               /* 80 */  65, 64, 64, 65, 67, 66, 66, 67, 69, 68,
                               /* 90 */  68, 69, 71, 70, 70, 71, 72, 73, 73, 72,
                               /* 100 */  74, 75, 75, 74, 76, 77, 77, 76, 78, 79,
                               /* 110 */  79, 78, 73, 72, 72, 73, 75, 74, 74, 75,
                               /* 120 */  77, 76, 76, 77, 79, 78, 78, 79, 80, 81,
                               /* 130 */  82, 83, 84, 85, 86, 87, 84, 85, 86, 87,
                               /* 140 */  80, 81, 82, 83, 88, 89, 90, 91, 92, 93,
                               /* 150 */  94, 95, 92, 93, 94, 95, 88, 89, 90, 91,
                               /* 160 */  84, 85, 86, 87, 80, 81, 82, 83, 80, 81,
                               /* 170 */  82, 83, 84, 85, 86, 87, 92, 93, 94, 95,
                               /* 180 */  88, 89, 90, 91, 88, 89, 90, 91, 92, 93,
                               /* 190 */  94, 95, 96, 97, 97, 96, 98, 99, 99, 98,
                               /* 200 */  98, 99, 99, 98, 96, 97, 97, 96, 97, 96,
                               /* 210 */  96, 97, 99, 98, 98, 99, 99, 98, 98, 99,
                               /* 220 */  97, 96, 96, 97, 98, 99, 99, 98, 96, 97,
                               /* 230 */  97, 96, 96, 97, 97, 96, 98, 99, 99, 98,
                               /* 240 */  99, 98, 98, 99, 97, 96, 96, 97, 97, 96,
                               /* 250 */  96, 97, 99, 98, 98, 99, 100, 101, 102, 103,
                               /* 260 */  104, 105, 106, 107, 108, 109, 110, 111, 112, 113,
                               /* 270 */  114, 115, 116, 117, 118, 119, 120, 121, 122, 123,
                               /* 280 */  124, 125, 126, 127, 128, 129, 130, 131, 116, 117,
                               /* 290 */  118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
                               /* 300 */  128, 129, 130, 131, 100, 101, 102, 103, 104, 105,
                               /* 310 */  106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
                               /* 320 */  132, 133, 133, 132, 134, 135, 135, 134, 136, 137,
                               /* 330 */  137, 136, 138, 139, 139, 138, 133, 132, 132, 133,
                               /* 340 */  135, 134, 134, 135, 137, 136, 136, 137, 139, 138,
                               /* 350 */  138, 139, 133, 132, 132, 133, 135, 134, 134, 135,
                               /* 360 */  137, 136, 136, 137, 139, 138, 138, 139, 132, 133,
                               /* 370 */  133, 132, 134, 135, 135, 134, 136, 137, 137, 136,
                               /* 380 */  138, 139, 139, 138, 140, 141, 142, 143, 144, 145,
                               /* 390 */  146, 147, 144, 145, 146, 147, 140, 141, 142, 143,
                               /* 400 */  144, 145, 146, 147, 140, 141, 142, 143, 140, 141,
                               /* 410 */  142, 143, 144, 145, 146, 147, 144, 145, 146, 147,
                               /* 420 */  140, 141, 142, 143, 140, 141, 142, 143, 144, 145,
                               /* 430 */  146, 147, 140, 141, 142, 143, 144, 145, 146, 147,
                               /* 440 */  144, 145, 146, 147, 140, 141, 142, 143, 148, 149,
                               /* 450 */  149, 148, 149, 148, 148, 149, 149, 148, 148, 149,
                               /* 460 */  148, 149, 149, 148, 149, 148, 148, 149, 148, 149,
                               /* 470 */  149, 148, 148, 149, 149, 148, 149, 148, 148, 149,
                               /* 480 */  149, 148, 148, 149, 148, 149, 149, 148, 148, 149,
                               /* 490 */  149, 148, 149, 148, 148, 149, 148, 149, 149, 148,
                               /* 500 */  149, 148, 148, 149, 149, 148, 148, 149, 148, 149,
                               /* 510 */  149, 148, 150, 151, 152, 152, 152, 152, 153, 154,
                               /* 520 */  155, 156, 152, 152, 152, 152, 157, 158, 151, 150,
                               /* 530 */  159, 159, 160, 160, 154, 153, 156, 155, 161, 161,
                               /* 540 */  162, 162, 158, 157, 155, 156, 163, 164, 165, 166,
                               /* 550 */  157, 158, 150, 151, 163, 164, 165, 166, 153, 154,
                               /* 560 */  167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
                               /* 570 */  177, 178, 179, 180, 181, 182, 151, 150, 150, 151,
                               /* 580 */  153, 154, 154, 153, 156, 155, 155, 156, 157, 158,
                               /* 590 */  158, 157, 150, 151, 151, 150, 154, 153, 153, 154,
                               /* 600 */  155, 156, 156, 155, 158, 157, 157, 158, 183, 184,
                               /* 610 */  184, 183, 185, 186, 186, 185, 187, 188, 188, 187,
                               /* 620 */  189, 190, 190, 189, 184, 183, 183, 184, 186, 185,
                               /* 630 */  185, 186, 188, 187, 187, 188, 190, 189, 189, 190,
                               /* 640 */  155, 156, 153, 154, 150, 151, 157, 158, 150, 151,
                               /* 650 */  157, 158, 155, 156, 153, 154, 191, 192, 193, 194,
                               /* 660 */  195, 196, 197, 198, 195, 196, 197, 198, 191, 192,
                               /* 670 */  193, 194, 150, 151, 157, 158, 155, 156, 153, 154,
                               /* 680 */  155, 156, 153, 154, 150, 151, 157, 158, 195, 196,
                               /* 690 */  197, 198, 191, 192, 193, 194, 191, 192, 193, 194,
                               /* 700 */  195, 196, 197, 198, 199, 200, 200, 199, 201, 202,
                               /* 710 */  202, 201, 201, 202, 202, 201, 199, 200, 200, 199,
                               /* 720 */  200, 199, 199, 200, 202, 201, 201, 202, 202, 201,
                               /* 730 */  201, 202, 200, 199, 199, 200, 201, 202, 202, 201,
                               /* 740 */  199, 200, 200, 199, 199, 200, 200, 199, 201, 202,
                               /* 750 */  202, 201, 202, 201, 201, 202, 200, 199, 199, 200,
                               /* 760 */  200, 199, 199, 200, 202, 201, 201, 202, 203, 204,
                               /* 770 */  178, 177, 180, 179, 205, 206, 204, 203, 170, 169,
                               /* 780 */  172, 171, 206, 205, 207, 208, 169, 170, 171, 172,
                               /* 790 */  209, 210, 208, 207, 177, 178, 179, 180, 210, 209,
                               /* 800 */  207, 208, 169, 170, 171, 172, 209, 210, 208, 207,
                               /* 810 */  177, 178, 179, 180, 210, 209, 203, 204, 178, 177,
                               /* 820 */  180, 179, 205, 206, 204, 203, 170, 169, 172, 171,
                               /* 830 */  206, 205, 211, 212, 212, 211, 213, 214, 214, 213,
                               /* 840 */  215, 216, 216, 215, 217, 218, 218, 217, 212, 211,
                               /* 850 */  211, 212, 214, 213, 213, 214, 216, 215, 215, 216,
                               /* 860 */  218, 217, 217, 218, 212, 211, 211, 212, 214, 213,
                               /* 870 */  213, 214, 216, 215, 215, 216, 218, 217, 217, 218,
                               /* 880 */  211, 212, 212, 211, 213, 214, 214, 213, 215, 216,
                               /* 890 */  216, 215, 217, 218, 218, 217, 219, 220, 221, 222,
                               /* 900 */  223, 224, 225, 226, 223, 224, 225, 226, 219, 220,
                               /* 910 */  221, 222, 223, 224, 225, 226, 219, 220, 221, 222,
                               /* 920 */  219, 220, 221, 222, 223, 224, 225, 226, 223, 224,
                               /* 930 */  225, 226, 219, 220, 221, 222, 219, 220, 221, 222,
                               /* 940 */  223, 224, 225, 226, 219, 220, 221, 222, 223, 224,
                               /* 950 */  225, 226, 223, 224, 225, 226, 219, 220, 221, 222,
                               /* 960 */  227, 228, 228, 227, 228, 227, 227, 228, 228, 227,
                               /* 970 */  227, 228, 227, 228, 228, 227, 228, 227, 227, 228,
                               /* 980 */  227, 228, 228, 227, 227, 228, 228, 227, 228, 227,
                               /* 990 */  227, 228, 228, 227, 227, 228, 227, 228, 228, 227,
                               /* 1000 */  227, 228, 228, 227, 228, 227, 227, 228, 227, 228,
                               /* 1010 */  228, 227, 228, 227, 227, 228, 228, 227, 227, 228,
                               /* 1020 */  227, 228, 228, 227, 229, 230, 231, 232, 233, 234,
                               /* 1030 */  235, 236, 237, 238, 239, 240, 241, 242, 243, 244,
                               /* 1040 */  16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
                               /* 1050 */  26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
                               /* 1060 */  36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
                               /* 1070 */  46, 47, 48, 49, 50, 51, 52, 53, 54, 55,
                               /* 1080 */  56, 57, 58, 59, 60, 61, 62, 63, 64, 65,
                               /* 1090 */  65, 64, 66, 67, 67, 66, 68, 69, 69, 68,
                               /* 1100 */  70, 71, 71, 70, 65, 64, 64, 65, 67, 66,
                               /* 1110 */  66, 67, 69, 68, 68, 69, 71, 70, 70, 71,
                               /* 1120 */  72, 73, 73, 72, 74, 75, 75, 74, 76, 77,
                               /* 1130 */  77, 76, 78, 79, 79, 78, 73, 72, 72, 73,
                               /* 1140 */  75, 74, 74, 75, 77, 76, 76, 77, 79, 78,
                               /* 1150 */  78, 79, 80, 81, 82, 83, 84, 85, 86, 87,
                               /* 1160 */  84, 85, 86, 87, 80, 81, 82, 83, 88, 89,
                               /* 1170 */  90, 91, 92, 93, 94, 95, 92, 93, 94, 95,
                               /* 1180 */  88, 89, 90, 91, 84, 85, 86, 87, 80, 81,
                               /* 1190 */  82, 83, 80, 81, 82, 83, 84, 85, 86, 87,
                               /* 1200 */  92, 93, 94, 95, 88, 89, 90, 91, 88, 89,
                               /* 1210 */  90, 91, 92, 93, 94, 95, 96, 97, 97, 96,
                               /* 1220 */  98, 99, 99, 98, 98, 99, 99, 98, 96, 97,
                               /* 1230 */  97, 96, 97, 96, 96, 97, 99, 98, 98, 99,
                               /* 1240 */  99, 98, 98, 99, 97, 96, 96, 97, 98, 99,
                               /* 1250 */  99, 98, 96, 97, 97, 96, 96, 97, 97, 96,
                               /* 1260 */  98, 99, 99, 98, 99, 98, 98, 99, 97, 96,
                               /* 1270 */  96, 97, 97, 96, 96, 97, 99, 98, 98, 99,
                               /* 1280 */  100, 101, 102, 103, 104, 105, 106, 107, 108, 109,
                               /* 1290 */  110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
                               /* 1300 */  120, 121, 122, 123, 124, 125, 126, 127, 128, 129,
                               /* 1310 */  130, 131, 116, 117, 118, 119, 120, 121, 122, 123,
                               /* 1320 */  124, 125, 126, 127, 128, 129, 130, 131, 100, 101,
                               /* 1330 */  102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
                               /* 1340 */  112, 113, 114, 115, 132, 133, 133, 132, 134, 135,
                               /* 1350 */  135, 134, 136, 137, 137, 136, 138, 139, 139, 138,
                               /* 1360 */  133, 132, 132, 133, 135, 134, 134, 135, 137, 136,
                               /* 1370 */  136, 137, 139, 138, 138, 139, 133, 132, 132, 133,
                               /* 1380 */  135, 134, 134, 135, 137, 136, 136, 137, 139, 138,
                               /* 1390 */  138, 139, 132, 133, 133, 132, 134, 135, 135, 134,
                               /* 1400 */  136, 137, 137, 136, 138, 139, 139, 138, 140, 141,
                               /* 1410 */  142, 143, 144, 145, 146, 147, 144, 145, 146, 147,
                               /* 1420 */  140, 141, 142, 143, 144, 145, 146, 147, 140, 141,
                               /* 1430 */  142, 143, 140, 141, 142, 143, 144, 145, 146, 147,
                               /* 1440 */  144, 145, 146, 147, 140, 141, 142, 143, 140, 141,
                               /* 1450 */  142, 143, 144, 145, 146, 147, 140, 141, 142, 143,
                               /* 1460 */  144, 145, 146, 147, 144, 145, 146, 147, 140, 141,
                               /* 1470 */  142, 143, 245, 246, 246, 245, 246, 245, 245, 246,
                               /* 1480 */  246, 245, 245, 246, 245, 246, 246, 245, 246, 245,
                               /* 1490 */  245, 246, 245, 246, 246, 245, 245, 246, 246, 245,
                               /* 1500 */  246, 245, 245, 246, 246, 245, 245, 246, 245, 246,
                               /* 1510 */  246, 245, 245, 246, 246, 245, 246, 245, 245, 246,
                               /* 1520 */  245, 246, 246, 245, 246, 245, 245, 246, 246, 245,
                               /* 1530 */  245, 246, 245, 246, 246, 245, 150, 152, 153, 152,
                               /* 1540 */  152, 151, 152, 154, 155, 152, 157, 152, 152, 156,
                               /* 1550 */  152, 158, 153, 247, 150, 247, 248, 154, 248, 151,
                               /* 1560 */  157, 249, 155, 249, 250, 158, 250, 156, 155, 166,
                               /* 1570 */  157, 164, 165, 156, 163, 158, 150, 166, 153, 164,
                               /* 1580 */  165, 151, 163, 154, 251, 252, 253, 254, 255, 256,
                               /* 1590 */  257, 258, 259, 260, 261, 262, 263, 264, 265, 266,
                               /* 1600 */  153, 150, 150, 153, 151, 154, 154, 151, 157, 155,
                               /* 1610 */  155, 157, 156, 158, 158, 156, 150, 153, 153, 150,
                               /* 1620 */  154, 151, 151, 154, 155, 157, 157, 155, 158, 156,
                               /* 1630 */  156, 158, 185, 184, 184, 185, 183, 186, 186, 183,
                               /* 1640 */  189, 188, 188, 189, 187, 190, 190, 187, 184, 185,
                               /* 1650 */  185, 184, 186, 183, 183, 186, 188, 189, 189, 188,
                               /* 1660 */  190, 187, 187, 190, 155, 151, 157, 154, 150, 156,
                               /* 1670 */  153, 158, 150, 156, 153, 158, 155, 151, 157, 154,
                               /* 1680 */  267, 268, 269, 270, 271, 272, 273, 274, 271, 272,
                               /* 1690 */  273, 274, 267, 268, 269, 270, 150, 156, 153, 158,
                               /* 1700 */  155, 151, 157, 154, 155, 151, 157, 154, 150, 156,
                               /* 1710 */  153, 158, 271, 272, 273, 274, 267, 268, 269, 270,
                               /* 1720 */  267, 268, 269, 270, 271, 272, 273, 274, 201, 200,
                               /* 1730 */  200, 201, 199, 202, 202, 199, 199, 202, 202, 199,
                               /* 1740 */  201, 200, 200, 201, 200, 201, 201, 200, 202, 199,
                               /* 1750 */  199, 202, 202, 199, 199, 202, 200, 201, 201, 200,
                               /* 1760 */  199, 202, 202, 199, 201, 200, 200, 201, 201, 200,
                               /* 1770 */  200, 201, 199, 202, 202, 199, 202, 199, 199, 202,
                               /* 1780 */  200, 201, 201, 200, 200, 201, 201, 200, 202, 199,
                               /* 1790 */  199, 202, 275, 262, 276, 260, 265, 277, 263, 278,
                               /* 1800 */  276, 254, 275, 252, 257, 278, 255, 277, 279, 252,
                               /* 1810 */  280, 254, 255, 281, 257, 282, 280, 260, 279, 262,
                               /* 1820 */  263, 282, 265, 281, 279, 252, 280, 254, 255, 281,
                               /* 1830 */  257, 282, 280, 260, 279, 262, 263, 282, 265, 281,
                               /* 1840 */  275, 262, 276, 260, 265, 277, 263, 278, 276, 254,
                               /* 1850 */  275, 252, 257, 278, 255, 277, 283, 284, 284, 283,
                               /* 1860 */  285, 286, 286, 285, 287, 288, 288, 287, 289, 290,
                               /* 1870 */  290, 289, 284, 283, 283, 284, 286, 285, 285, 286,
                               /* 1880 */  288, 287, 287, 288, 290, 289, 289, 290, 284, 283,
                               /* 1890 */  283, 284, 286, 285, 285, 286, 288, 287, 287, 288,
                               /* 1900 */  290, 289, 289, 290, 283, 284, 284, 283, 285, 286,
                               /* 1910 */  286, 285, 287, 288, 288, 287, 289, 290, 290, 289,
                               /* 1920 */  226, 221, 220, 223, 222, 225, 224, 219, 222, 225,
                               /* 1930 */  224, 219, 226, 221, 220, 223, 222, 225, 224, 219,
                               /* 1940 */  226, 221, 220, 223, 226, 221, 220, 223, 222, 225,
                               /* 1950 */  224, 219, 222, 225, 224, 219, 226, 221, 220, 223,
                               /* 1960 */  226, 221, 220, 223, 222, 225, 224, 219, 226, 221,
                               /* 1970 */  220, 223, 222, 225, 224, 219, 222, 225, 224, 219,
                               /* 1980 */  226, 221, 220, 223, 291, 292, 292, 291, 292, 291,
                               /* 1990 */  291, 292, 292, 291, 291, 292, 291, 292, 292, 291,
                               /* 2000 */  292, 291, 291, 292, 291, 292, 292, 291, 291, 292,
                               /* 2010 */  292, 291, 292, 291, 291, 292, 292, 291, 291, 292,
                               /* 2020 */  291, 292, 292, 291, 291, 292, 292, 291, 292, 291,
                               /* 2030 */  291, 292, 291, 292, 292, 291, 292, 291, 291, 292,
                               /* 2040 */  292, 291, 291, 292, 291, 292, 292, 291, 293, 294,
                               /* 2050 */  152, 152, 295, 296, 152, 152, 152, 152, 297, 298,
                               /* 2060 */  152, 152, 299, 300, 294, 293, 301, 301, 296, 295,
                               /* 2070 */  302, 302, 303, 303, 298, 297, 304, 304, 300, 299,
                               /* 2080 */  295, 296, 163, 164, 293, 294, 163, 164, 165, 166,
                               /* 2090 */  299, 300, 165, 166, 297, 298, 305, 306, 307, 308,
                               /* 2100 */  309, 310, 311, 312, 313, 314, 315, 316, 317, 318,
                               /* 2110 */  319, 320, 294, 293, 293, 294, 296, 295, 295, 296,
                               /* 2120 */  297, 298, 298, 297, 299, 300, 300, 299, 293, 294,
                               /* 2130 */  294, 293, 295, 296, 296, 295, 298, 297, 297, 298,
                               /* 2140 */  300, 299, 299, 300, 321, 322, 322, 321, 323, 324,
                               /* 2150 */  324, 323, 325, 326, 326, 325, 327, 328, 328, 327,
                               /* 2160 */  322, 321, 321, 322, 324, 323, 323, 324, 326, 325,
                               /* 2170 */  325, 326, 328, 327, 327, 328, 295, 296, 297, 298,
                               /* 2180 */  293, 294, 299, 300, 293, 294, 299, 300, 295, 296,
                               /* 2190 */  297, 298, 329, 330, 331, 332, 333, 334, 335, 336,
                               /* 2200 */  333, 334, 335, 336, 329, 330, 331, 332, 293, 294,
                               /* 2210 */  299, 300, 295, 296, 297, 298, 295, 296, 297, 298,
                               /* 2220 */  293, 294, 299, 300, 333, 334, 335, 336, 329, 330,
                               /* 2230 */  331, 332, 329, 330, 331, 332, 333, 334, 335, 336,
                               /* 2240 */  337, 338, 338, 337, 339, 340, 340, 339, 339, 340,
                               /* 2250 */  340, 339, 337, 338, 338, 337, 338, 337, 337, 338,
                               /* 2260 */  340, 339, 339, 340, 340, 339, 339, 340, 338, 337,
                               /* 2270 */  337, 338, 339, 340, 340, 339, 337, 338, 338, 337,
                               /* 2280 */  337, 338, 338, 337, 339, 340, 340, 339, 340, 339,
                               /* 2290 */  339, 340, 338, 337, 337, 338, 338, 337, 337, 338,
                               /* 2300 */  340, 339, 339, 340, 341, 342, 312, 311, 342, 341,
                               /* 2310 */  308, 307, 318, 317, 343, 344, 314, 313, 344, 343,
                               /* 2320 */  345, 346, 307, 308, 346, 345, 311, 312, 313, 314,
                               /* 2330 */  347, 348, 317, 318, 348, 347, 345, 346, 307, 308,
                               /* 2340 */  346, 345, 311, 312, 313, 314, 347, 348, 317, 318,
                               /* 2350 */  348, 347, 341, 342, 312, 311, 342, 341, 308, 307,
                               /* 2360 */  318, 317, 343, 344, 314, 313, 344, 343, 349, 350,
                               /* 2370 */  350, 349, 351, 352, 352, 351, 353, 354, 354, 353,
                               /* 2380 */  355, 356, 356, 355, 350, 349, 349, 350, 352, 351,
                               /* 2390 */  351, 352, 354, 353, 353, 354, 356, 355, 355, 356,
                               /* 2400 */  350, 349, 349, 350, 352, 351, 351, 352, 354, 353,
                               /* 2410 */  353, 354, 356, 355, 355, 356, 349, 350, 350, 349,
                               /* 2420 */  351, 352, 352, 351, 353, 354, 354, 353, 355, 356,
                               /* 2430 */  356, 355, 357, 358, 359, 360, 361, 362, 363, 364,
                               /* 2440 */  361, 362, 363, 364, 357, 358, 359, 360, 361, 362,
                               /* 2450 */  363, 364, 357, 358, 359, 360, 357, 358, 359, 360,
                               /* 2460 */  361, 362, 363, 364, 361, 362, 363, 364, 357, 358,
                               /* 2470 */  359, 360, 357, 358, 359, 360, 361, 362, 363, 364,
                               /* 2480 */  357, 358, 359, 360, 361, 362, 363, 364, 361, 362,
                               /* 2490 */  363, 364, 357, 358, 359, 360, 365, 366, 366, 365,
                               /* 2500 */  366, 365, 365, 366, 366, 365, 365, 366, 365, 366,
                               /* 2510 */  366, 365, 366, 365, 365, 366, 365, 366, 366, 365,
                               /* 2520 */  365, 366, 366, 365, 366, 365, 365, 366, 366, 365,
                               /* 2530 */  365, 366, 365, 366, 366, 365, 365, 366, 366, 365,
                               /* 2540 */  366, 365, 365, 366, 365, 366, 366, 365, 366, 365,
                               /* 2550 */  365, 366, 366, 365, 365, 366, 365, 366, 366, 365,
                               /* 2560 */  165, 152, 152, 152, 152, 166, 152, 152, 152, 152,
                               /* 2570 */  163, 152, 152, 152, 152, 164, 152, 165, 165, 165,
                               /* 2580 */  166, 152, 166, 166, 163, 163, 152, 163, 164, 164,
                               /* 2590 */  164, 152, 152, 166, 163, 164, 165, 152, 163, 164,
                               /* 2600 */  165, 166, 152, 164, 165, 166, 163, 152, 367, 368,
                               /* 2610 */  369, 370, 368, 371, 372, 373, 369, 372, 374, 375,
                               /* 2620 */  370, 373, 375, 376, 152, 165, 165, 152, 166, 152,
                               /* 2630 */  152, 166, 163, 152, 152, 163, 152, 164, 164, 152,
                               /* 2640 */  165, 152, 152, 165, 152, 166, 166, 152, 152, 163,
                               /* 2650 */  163, 152, 164, 152, 152, 164, 370, 164, 164, 370,
                               /* 2660 */  163, 372, 372, 163, 166, 372, 372, 166, 370, 165,
                               /* 2670 */  165, 370, 164, 370, 370, 164, 372, 163, 163, 372,
                               /* 2680 */  372, 166, 166, 372, 165, 370, 370, 165, 152, 166,
                               /* 2690 */  163, 152, 165, 152, 152, 164, 165, 152, 152, 164,
                               /* 2700 */  152, 166, 163, 152, 370, 163, 166, 370, 164, 372,
                               /* 2710 */  372, 165, 164, 372, 372, 165, 370, 163, 166, 370,
                               /* 2720 */  165, 152, 152, 164, 152, 166, 163, 152, 152, 166,
                               /* 2730 */  163, 152, 165, 152, 152, 164, 164, 372, 372, 165,
                               /* 2740 */  370, 163, 166, 370, 370, 163, 166, 370, 164, 372,
                               /* 2750 */  372, 165, 370, 152, 152, 370, 152, 372, 372, 152,
                               /* 2760 */  152, 372, 372, 152, 370, 152, 152, 370, 152, 370,
                               /* 2770 */  370, 152, 372, 152, 152, 372, 372, 152, 152, 372,
                               /* 2780 */  152, 370, 370, 152, 152, 372, 372, 152, 370, 152,
                               /* 2790 */  152, 370, 370, 152, 152, 370, 152, 372, 372, 152,
                               /* 2800 */  372, 152, 152, 372, 152, 370, 370, 152, 152, 370,
                               /* 2810 */  370, 152, 372, 152, 152, 372, 152, 375, 373, 372,
                               /* 2820 */  375, 152, 370, 369, 373, 370, 152, 368, 372, 369,
                               /* 2830 */  368, 152, 377, 368, 369, 370, 368, 377, 372, 373,
                               /* 2840 */  369, 372, 377, 375, 370, 373, 375, 377, 377, 368,
                               /* 2850 */  369, 370, 368, 377, 372, 373, 369, 372, 377, 375,
                               /* 2860 */  370, 373, 375, 377, 152, 375, 373, 372, 375, 152,
                               /* 2870 */  370, 369, 373, 370, 152, 368, 372, 369, 368, 152,
                               /* 2880 */  376, 164, 164, 376, 163, 374, 374, 163, 166, 371,
                               /* 2890 */  371, 166, 367, 165, 165, 367, 164, 376, 376, 164,
                               /* 2900 */  374, 163, 163, 374, 371, 166, 166, 371, 165, 367,
                               /* 2910 */  367, 165, 164, 376, 376, 164, 374, 163, 163, 374,
                               /* 2920 */  371, 166, 166, 371, 165, 367, 367, 165, 376, 164,
                               /* 2930 */  164, 376, 163, 374, 374, 163, 166, 371, 371, 166,
                               /* 2940 */  367, 165, 165, 367, 376, 163, 166, 367, 164, 374,
                               /* 2950 */  371, 165, 164, 374, 371, 165, 376, 163, 166, 367,
                               /* 2960 */  164, 374, 371, 165, 376, 163, 166, 367, 376, 163,
                               /* 2970 */  166, 367, 164, 374, 371, 165, 164, 374, 371, 165,
                               /* 2980 */  376, 163, 166, 367, 376, 163, 166, 367, 164, 374,
                               /* 2990 */  371, 165, 376, 163, 166, 367, 164, 374, 371, 165,
                               /* 3000 */  164, 374, 371, 165, 376, 163, 166, 367, 152, 377,
                               /* 3010 */  377, 152, 377, 152, 152, 377, 377, 152, 152, 377,
                               /* 3020 */  152, 377, 377, 152, 377, 152, 152, 377, 152, 377,
                               /* 3030 */  377, 152, 152, 377, 377, 152, 377, 152, 152, 377,
                               /* 3040 */  377, 152, 152, 377, 152, 377, 377, 152, 152, 377,
                               /* 3050 */  377, 152, 377, 152, 152, 377, 152, 377, 377, 152,
                               /* 3060 */  377, 152, 152, 377, 377, 152, 152, 377, 152, 377,
                               /* 3070 */  377, 152, 378, 379, 380, 381, 382, 383, 384, 385,
                               /* 3080 */  386, 387, 388, 389, 390, 391, 392, 393, 16, 17,
                               /* 3090 */  18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
                               /* 3100 */  28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
                               /* 3110 */  38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
                               /* 3120 */  48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
                               /* 3130 */  58, 59, 60, 61, 62, 63, 64, 65, 65, 64,
                               /* 3140 */  66, 67, 67, 66, 68, 69, 69, 68, 70, 71,
                               /* 3150 */  71, 70, 65, 64, 64, 65, 67, 66, 66, 67,
                               /* 3160 */  69, 68, 68, 69, 71, 70, 70, 71, 72, 73,
                               /* 3170 */  73, 72, 74, 75, 75, 74, 76, 77, 77, 76,
                               /* 3180 */  78, 79, 79, 78, 73, 72, 72, 73, 75, 74,
                               /* 3190 */  74, 75, 77, 76, 76, 77, 79, 78, 78, 79,
                               /* 3200 */  80, 81, 82, 83, 84, 85, 86, 87, 84, 85,
                               /* 3210 */  86, 87, 80, 81, 82, 83, 88, 89, 90, 91,
                               /* 3220 */  92, 93, 94, 95, 92, 93, 94, 95, 88, 89,
                               /* 3230 */  90, 91, 84, 85, 86, 87, 80, 81, 82, 83,
                               /* 3240 */  80, 81, 82, 83, 84, 85, 86, 87, 92, 93,
                               /* 3250 */  94, 95, 88, 89, 90, 91, 88, 89, 90, 91,
                               /* 3260 */  92, 93, 94, 95, 96, 97, 97, 96, 98, 99,
                               /* 3270 */  99, 98, 98, 99, 99, 98, 96, 97, 97, 96,
                               /* 3280 */  97, 96, 96, 97, 99, 98, 98, 99, 99, 98,
                               /* 3290 */  98, 99, 97, 96, 96, 97, 98, 99, 99, 98,
                               /* 3300 */  96, 97, 97, 96, 96, 97, 97, 96, 98, 99,
                               /* 3310 */  99, 98, 99, 98, 98, 99, 97, 96, 96, 97,
                               /* 3320 */  97, 96, 96, 97, 99, 98, 98, 99, 100, 101,
                               /* 3330 */  102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
                               /* 3340 */  112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
                               /* 3350 */  122, 123, 124, 125, 126, 127, 128, 129, 130, 131,
                               /* 3360 */  116, 117, 118, 119, 120, 121, 122, 123, 124, 125,
                               /* 3370 */  126, 127, 128, 129, 130, 131, 100, 101, 102, 103,
                               /* 3380 */  104, 105, 106, 107, 108, 109, 110, 111, 112, 113,
                               /* 3390 */  114, 115, 132, 133, 133, 132, 134, 135, 135, 134,
                               /* 3400 */  136, 137, 137, 136, 138, 139, 139, 138, 133, 132,
                               /* 3410 */  132, 133, 135, 134, 134, 135, 137, 136, 136, 137,
                               /* 3420 */  139, 138, 138, 139, 133, 132, 132, 133, 135, 134,
                               /* 3430 */  134, 135, 137, 136, 136, 137, 139, 138, 138, 139,
                               /* 3440 */  132, 133, 133, 132, 134, 135, 135, 134, 136, 137,
                               /* 3450 */  137, 136, 138, 139, 139, 138, 140, 141, 142, 143,
                               /* 3460 */  144, 145, 146, 147, 144, 145, 146, 147, 140, 141,
                               /* 3470 */  142, 143, 144, 145, 146, 147, 140, 141, 142, 143,
                               /* 3480 */  140, 141, 142, 143, 144, 145, 146, 147, 144, 145,
                               /* 3490 */  146, 147, 140, 141, 142, 143, 140, 141, 142, 143,
                               /* 3500 */  144, 145, 146, 147, 140, 141, 142, 143, 144, 145,
                               /* 3510 */  146, 147, 144, 145, 146, 147, 140, 141, 142, 143,
                               /* 3520 */  394, 395, 395, 394, 395, 394, 394, 395, 395, 394,
                               /* 3530 */  394, 395, 394, 395, 395, 394, 395, 394, 394, 395,
                               /* 3540 */  394, 395, 395, 394, 394, 395, 395, 394, 395, 394,
                               /* 3550 */  394, 395, 395, 394, 394, 395, 394, 395, 395, 394,
                               /* 3560 */  394, 395, 395, 394, 395, 394, 394, 395, 394, 395,
                               /* 3570 */  395, 394, 395, 394, 394, 395, 395, 394, 394, 395,
                               /* 3580 */  394, 395, 395, 394, 396, 152, 397, 152, 152, 398,
                               /* 3590 */  152, 399, 400, 152, 401, 152, 152, 402, 152, 403,
                               /* 3600 */  397, 247, 396, 247, 248, 399, 248, 398, 401, 249,
                               /* 3610 */  400, 249, 250, 403, 250, 402, 400, 166, 401, 164,
                               /* 3620 */  165, 402, 163, 403, 396, 166, 397, 164, 165, 398,
                               /* 3630 */  163, 399, 404, 405, 406, 407, 408, 409, 410, 411,
                               /* 3640 */  412, 413, 414, 415, 416, 417, 418, 419, 397, 396,
                               /* 3650 */  396, 397, 398, 399, 399, 398, 401, 400, 400, 401,
                               /* 3660 */  402, 403, 403, 402, 396, 397, 397, 396, 399, 398,
                               /* 3670 */  398, 399, 400, 401, 401, 400, 403, 402, 402, 403,
                               /* 3680 */  420, 421, 421, 420, 422, 423, 423, 422, 424, 425,
                               /* 3690 */  425, 424, 426, 427, 427, 426, 421, 420, 420, 421,
                               /* 3700 */  423, 422, 422, 423, 425, 424, 424, 425, 427, 426,
                               /* 3710 */  426, 427, 400, 398, 401, 399, 396, 402, 397, 403,
                               /* 3720 */  396, 402, 397, 403, 400, 398, 401, 399, 428, 429,
                               /* 3730 */  430, 431, 432, 433, 434, 435, 432, 433, 434, 435,
                               /* 3740 */  428, 429, 430, 431, 396, 402, 397, 403, 400, 398,
                               /* 3750 */  401, 399, 400, 398, 401, 399, 396, 402, 397, 403,
                               /* 3760 */  432, 433, 434, 435, 428, 429, 430, 431, 428, 429,
                               /* 3770 */  430, 431, 432, 433, 434, 435, 436, 437, 437, 436,
                               /* 3780 */  438, 439, 439, 438, 438, 439, 439, 438, 436, 437,
                               /* 3790 */  437, 436, 437, 436, 436, 437, 439, 438, 438, 439,
                               /* 3800 */  439, 438, 438, 439, 437, 436, 436, 437, 438, 439,
                               /* 3810 */  439, 438, 436, 437, 437, 436, 436, 437, 437, 436,
                               /* 3820 */  438, 439, 439, 438, 439, 438, 438, 439, 437, 436,
                               /* 3830 */  436, 437, 437, 436, 436, 437, 439, 438, 438, 439,
                               /* 3840 */  440, 415, 441, 413, 418, 442, 416, 443, 441, 407,
                               /* 3850 */  440, 405, 410, 443, 408, 442, 444, 405, 445, 407,
                               /* 3860 */  408, 446, 410, 447, 445, 413, 444, 415, 416, 447,
                               /* 3870 */  418, 446, 444, 405, 445, 407, 408, 446, 410, 447,
                               /* 3880 */  445, 413, 444, 415, 416, 447, 418, 446, 440, 415,
                               /* 3890 */  441, 413, 418, 442, 416, 443, 441, 407, 440, 405,
                               /* 3900 */  410, 443, 408, 442, 283, 284, 284, 283, 285, 286,
                               /* 3910 */  286, 285, 287, 288, 288, 287, 289, 290, 290, 289,
                               /* 3920 */  284, 283, 283, 284, 286, 285, 285, 286, 288, 287,
                               /* 3930 */  287, 288, 290, 289, 289, 290, 284, 283, 283, 284,
                               /* 3940 */  286, 285, 285, 286, 288, 287, 287, 288, 290, 289,
                               /* 3950 */  289, 290, 283, 284, 284, 283, 285, 286, 286, 285,
                               /* 3960 */  287, 288, 288, 287, 289, 290, 290, 289, 226, 221,
                               /* 3970 */  220, 223, 222, 225, 224, 219, 222, 225, 224, 219,
                               /* 3980 */  226, 221, 220, 223, 222, 225, 224, 219, 226, 221,
                               /* 3990 */  220, 223, 226, 221, 220, 223, 222, 225, 224, 219,
                               /* 4000 */  222, 225, 224, 219, 226, 221, 220, 223, 226, 221,
                               /* 4010 */  220, 223, 222, 225, 224, 219, 226, 221, 220, 223,
                               /* 4020 */  222, 225, 224, 219, 222, 225, 224, 219, 226, 221,
                               /* 4030 */  220, 223, 448, 449, 449, 448, 449, 448, 448, 449,
                               /* 4040 */  449, 448, 448, 449, 448, 449, 449, 448, 449, 448,
                               /* 4050 */  448, 449, 448, 449, 449, 448, 448, 449, 449, 448,
                               /* 4060 */  449, 448, 448, 449, 449, 448, 448, 449, 448, 449,
                               /* 4070 */  449, 448, 448, 449, 449, 448, 449, 448, 448, 449,
                               /* 4080 */  448, 449, 449, 448, 449, 448, 448, 449, 449, 448,
                               /* 4090 */  448, 449, 448, 449, 449, 448  };

        int look_up_3_input_node (NodeType op, int i1, int i2, int signature)
        {
            int ll_nn = NON_NEGATED( node(i1).left );
            int lr_nn = NON_NEGATED( node(i1).right );
            int r_nn = NON_NEGATED( i2 );

            int result = INVALID;
            int idx = lookup_table_3_inputs[signature];

            switch (idx) {
                case 0: // i1 i2 and i3 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, r_nn );
                    result = temp1;
                    break;
                }
                case 1: // i1 neg i2 and i3 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, r_nn );
                    result = temp1;
                    break;
                }
                case 2: // i1 i2 neg and i3 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, r_nn );
                    result = temp1;
                    break;
                }
                case 3: // i1 neg i2 neg and i3 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, r_nn );
                    result = temp1;
                    break;
                }
                case 4: // i1 i2 and neg i3 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), r_nn );
                    result = temp1;
                    break;
                }
                case 5: // i1 neg i2 and neg i3 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), r_nn );
                    result = temp1;
                    break;
                }
                case 6: // i1 i2 neg and neg i3 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), r_nn );
                    result = temp1;
                    break;
                }
                case 7: // i1 neg i2 neg and neg i3 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), r_nn );
                    result = temp1;
                    break;
                }
                case 8: // i1 i2 and i3 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( r_nn ) );
                    result = temp1;
                    break;
                }
                case 9: // i1 neg i2 and i3 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( r_nn ) );
                    result = temp1;
                    break;
                }
                case 10: // i1 i2 neg and i3 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( r_nn ) );
                    result = temp1;
                    break;
                }
                case 11: // i1 neg i2 neg and i3 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( r_nn ) );
                    result = temp1;
                    break;
                }
                case 12: // i1 i2 and neg i3 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( r_nn ) );
                    result = temp1;
                    break;
                }
                case 13: // i1 neg i2 and neg i3 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( r_nn ) );
                    result = temp1;
                    break;
                }
                case 14: // i1 i2 neg and neg i3 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( r_nn ) );
                    result = temp1;
                    break;
                }
                case 15: // i1 neg i2 neg and neg i3 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( r_nn ) );
                    result = temp1;
                    break;
                }
                case 16: // i1 i2 xor i3 and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, r_nn );
                    result = temp1;
                    break;
                }
                case 17: // i1 i2 xor neg i3 and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), r_nn );
                    result = temp1;
                    break;
                }
                case 18: // i1 i2 xor i3 neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( r_nn ) );
                    result = temp1;
                    break;
                }
                case 19: // i1 i2 xor neg i3 neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( r_nn ) );
                    result = temp1;
                    break;
                }
                case 20: // i1 i2 and i3 xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, r_nn );
                    result = temp1;
                    break;
                }
                case 21: // i1 neg i2 and i3 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, r_nn );
                    result = temp1;
                    break;
                }
                case 22: // i1 i2 neg and i3 xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, r_nn );
                    result = temp1;
                    break;
                }
                case 23: // i1 neg i2 neg and i3 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, r_nn );
                    result = temp1;
                    break;
                }
                case 24: // i1 i2 and i3 xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, r_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 25: // i1 neg i2 and i3 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, r_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 26: // i1 i2 neg and i3 xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, r_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 27: // i1 neg i2 neg and i3 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, r_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 28: // i1 i2 xor i3 xor
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, r_nn );
                    result = temp1;
                    break;
                }
                case 29: // i1 i2 xor i3 xor neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, r_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 30: // i1 i2 and
                {
                    int temp0 = create_op_node (NodeType.AND, ll_nn, lr_nn );
                    result = temp0;
                    break;
                }
                case 31: // i1 neg i2 and
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    result = temp0;
                    break;
                }
                case 32: // neg
                {
                    result = zero();
                    break;
                }
                case 33: // i2
                {
                    result = lr_nn;
                    break;
                }
                case 34: // i1 i2 neg and
                {
                    int temp0 = create_op_node (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    result = temp0;
                    break;
                }
                case 35: // i1 neg i2 neg and
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    result = temp0;
                    break;
                }
                case 36: // i2 neg
                {
                    result = NEGATE( lr_nn );
                    break;
                }
                case 37: // i1 neg i2 neg and neg
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    result = NEGATE( temp0 );
                    break;
                }
                case 38: // i1 i2 neg and neg
                {
                    int temp0 = create_op_node (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    result = NEGATE( temp0 );
                    break;
                }
                case 39: // i1 neg i2 and neg
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    result = NEGATE( temp0 );
                    break;
                }
                case 40: // i1 i2 and neg
                {
                    int temp0 = create_op_node (NodeType.AND, ll_nn, lr_nn );
                    result = NEGATE( temp0 );
                    break;
                }
                case 41: // i1
                {
                    result = ll_nn;
                    break;
                }
                case 42: // i1 neg
                {
                    result = NEGATE( ll_nn );
                    break;
                }
                case 43: // i1 i3 and i2 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, r_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 44: // i1 neg i3 and i2 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), r_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 45: // i1 i3 and i2 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, r_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 46: // i1 neg i3 and i2 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), r_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 47: // i1 i3 neg and i2 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( r_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 48: // i1 neg i3 neg and i2 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( r_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 49: // i1 i3 neg and i2 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( r_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 50: // i1 neg i3 neg and i2 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( r_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 51: // i1 i3 xor i2 xor
                {
                    int temp0 = create (NodeType.XOR, ll_nn, r_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 52: // i1 i3 xor i2 xor neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, r_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 53: // i3 i1 and i2 and
                {
                    int temp0 = create (NodeType.AND, r_nn, ll_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 54: // i3 i1 neg and i2 and
                {
                    int temp0 = create (NodeType.AND, r_nn, NEGATE( ll_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 55: // i3 i1 and i2 neg and
                {
                    int temp0 = create (NodeType.AND, r_nn, ll_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 56: // i3 i1 neg and i2 neg and
                {
                    int temp0 = create (NodeType.AND, r_nn, NEGATE( ll_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 57: // i3 neg i1 and i2 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( r_nn ), ll_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 58: // i3 neg i1 neg and i2 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( r_nn ), NEGATE( ll_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 59: // i3 neg i1 and i2 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( r_nn ), ll_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 60: // i3 neg i1 neg and i2 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( r_nn ), NEGATE( ll_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 61: // i3 i1 xor i2 xor
                {
                    int temp0 = create (NodeType.XOR, r_nn, ll_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 62: // i3 i1 xor i2 xor neg
                {
                    int temp0 = create (NodeType.XOR, r_nn, ll_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                default:
                    throw new Exception ("Unknown Cases");
            }
            return result;
        }

        int look_up_4_input_node (NodeType op, int i1, int i2, int signature)
        {
            int ll_nn = NON_NEGATED( node(i1).input(0) );
            int lr_nn = NON_NEGATED( node(i1).input(1) );
            int rl_nn = NON_NEGATED( node(i2).input(0) );
            int rr_nn = NON_NEGATED( node(i2).input(1) );

            int result = INVALID;
            int idx = lookup_table_4_inputs[signature];

            switch (idx) {
                case 0: // i1 i2 and i3 i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 1: // i1 neg i2 and i3 i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 2: // i1 i2 neg and i3 i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 3: // i1 neg i2 neg and i3 i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 4: // i1 i2 and i3 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 5: // i1 neg i2 and i3 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 6: // i1 i2 neg and i3 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 7: // i1 neg i2 neg and i3 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 8: // i1 i2 and i3 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 9: // i1 neg i2 and i3 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 10: // i1 i2 neg and i3 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 11: // i1 neg i2 neg and i3 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 12: // i1 i2 and i3 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 13: // i1 neg i2 and i3 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 14: // i1 i2 neg and i3 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 15: // i1 neg i2 neg and i3 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 16: // i1 i2 and neg i3 i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 17: // i1 neg i2 and neg i3 i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 18: // i1 i2 neg and neg i3 i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 19: // i1 neg i2 neg and neg i3 i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 20: // i1 i2 and neg i3 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 21: // i1 neg i2 and neg i3 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 22: // i1 i2 neg and neg i3 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 23: // i1 neg i2 neg and neg i3 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 24: // i1 i2 and neg i3 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 25: // i1 neg i2 and neg i3 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 26: // i1 i2 neg and neg i3 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 27: // i1 neg i2 neg and neg i3 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 28: // i1 i2 and neg i3 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 29: // i1 neg i2 and neg i3 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 30: // i1 i2 neg and neg i3 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 31: // i1 neg i2 neg and neg i3 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 32: // i1 i2 and i3 i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 33: // i1 neg i2 and i3 i4 and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 34: // i1 i2 neg and i3 i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 35: // i1 neg i2 neg and i3 i4 and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 36: // i1 i2 and i3 neg i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 37: // i1 neg i2 and i3 neg i4 and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 38: // i1 i2 neg and i3 neg i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 39: // i1 neg i2 neg and i3 neg i4 and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 40: // i1 i2 and i3 i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 41: // i1 neg i2 and i3 i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 42: // i1 i2 neg and i3 i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 43: // i1 neg i2 neg and i3 i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 44: // i1 i2 and i3 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 45: // i1 neg i2 and i3 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 46: // i1 i2 neg and i3 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 47: // i1 neg i2 neg and i3 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 48: // i1 i2 and neg i3 i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 49: // i1 neg i2 and neg i3 i4 and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 50: // i1 i2 neg and neg i3 i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 51: // i1 neg i2 neg and neg i3 i4 and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 52: // i1 i2 and neg i3 neg i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 53: // i1 neg i2 and neg i3 neg i4 and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 54: // i1 i2 neg and neg i3 neg i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 55: // i1 neg i2 neg and neg i3 neg i4 and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 56: // i1 i2 and neg i3 i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 57: // i1 neg i2 and neg i3 i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 58: // i1 i2 neg and neg i3 i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 59: // i1 neg i2 neg and neg i3 i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 60: // i1 i2 and neg i3 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 61: // i1 neg i2 and neg i3 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 62: // i1 i2 neg and neg i3 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 63: // i1 neg i2 neg and neg i3 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 64: // i1 i2 xor i3 i4 and and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 65: // i1 i2 xor neg i3 i4 and and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 66: // i1 i2 xor i3 neg i4 and and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 67: // i1 i2 xor neg i3 neg i4 and and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 68: // i1 i2 xor i3 i4 neg and and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 69: // i1 i2 xor neg i3 i4 neg and and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 70: // i1 i2 xor i3 neg i4 neg and and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 71: // i1 i2 xor neg i3 neg i4 neg and and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 72: // i1 i2 xor i3 i4 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 73: // i1 i2 xor neg i3 i4 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 74: // i1 i2 xor i3 neg i4 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 75: // i1 i2 xor neg i3 neg i4 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 76: // i1 i2 xor i3 i4 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 77: // i1 i2 xor neg i3 i4 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 78: // i1 i2 xor i3 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 79: // i1 i2 xor neg i3 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 80: // i1 i2 and i3 i4 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 81: // i1 neg i2 and i3 i4 xor and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 82: // i1 i2 neg and i3 i4 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 83: // i1 neg i2 neg and i3 i4 xor and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 84: // i1 i2 and i3 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 85: // i1 neg i2 and i3 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 86: // i1 i2 neg and i3 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 87: // i1 neg i2 neg and i3 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 88: // i1 i2 and neg i3 i4 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 89: // i1 neg i2 and neg i3 i4 xor and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 90: // i1 i2 neg and neg i3 i4 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 91: // i1 neg i2 neg and neg i3 i4 xor and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 92: // i1 i2 and neg i3 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 93: // i1 neg i2 and neg i3 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 94: // i1 i2 neg and neg i3 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 95: // i1 neg i2 neg and neg i3 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 96: // i1 i2 xor i3 i4 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 97: // i1 i2 xor neg i3 i4 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 98: // i1 i2 xor i3 i4 xor neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 99: // i1 i2 xor neg i3 i4 xor neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 100: // i1 i2 and i3 i4 and xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 101: // i1 neg i2 and i3 i4 and xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 102: // i1 i2 neg and i3 i4 and xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 103: // i1 neg i2 neg and i3 i4 and xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 104: // i1 i2 and i3 neg i4 and xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 105: // i1 neg i2 and i3 neg i4 and xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 106: // i1 i2 neg and i3 neg i4 and xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 107: // i1 neg i2 neg and i3 neg i4 and xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 108: // i1 i2 and i3 i4 neg and xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 109: // i1 neg i2 and i3 i4 neg and xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 110: // i1 i2 neg and i3 i4 neg and xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 111: // i1 neg i2 neg and i3 i4 neg and xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 112: // i1 i2 and i3 neg i4 neg and xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 113: // i1 neg i2 and i3 neg i4 neg and xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 114: // i1 i2 neg and i3 neg i4 neg and xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 115: // i1 neg i2 neg and i3 neg i4 neg and xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 116: // i1 i2 and i3 i4 and xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 117: // i1 neg i2 and i3 i4 and xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 118: // i1 i2 neg and i3 i4 and xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 119: // i1 neg i2 neg and i3 i4 and xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 120: // i1 i2 and i3 neg i4 and xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 121: // i1 neg i2 and i3 neg i4 and xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 122: // i1 i2 neg and i3 neg i4 and xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 123: // i1 neg i2 neg and i3 neg i4 and xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 124: // i1 i2 and i3 i4 neg and xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 125: // i1 neg i2 and i3 i4 neg and xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 126: // i1 i2 neg and i3 i4 neg and xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 127: // i1 neg i2 neg and i3 i4 neg and xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 128: // i1 i2 and i3 neg i4 neg and xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 129: // i1 neg i2 and i3 neg i4 neg and xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 130: // i1 i2 neg and i3 neg i4 neg and xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 131: // i1 neg i2 neg and i3 neg i4 neg and xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 132: // i1 i2 xor i3 i4 and xor
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 133: // i1 i2 xor i3 i4 and xor neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 134: // i1 i2 xor i3 neg i4 and xor
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 135: // i1 i2 xor i3 neg i4 and xor neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 136: // i1 i2 xor i3 i4 neg and xor
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 137: // i1 i2 xor i3 i4 neg and xor neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 138: // i1 i2 xor i3 neg i4 neg and xor
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 139: // i1 i2 xor i3 neg i4 neg and xor neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 140: // i1 i2 and i3 i4 xor xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 141: // i1 neg i2 and i3 i4 xor xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 142: // i1 i2 neg and i3 i4 xor xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 143: // i1 neg i2 neg and i3 i4 xor xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 144: // i1 i2 and i3 i4 xor xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 145: // i1 neg i2 and i3 i4 xor xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 146: // i1 i2 neg and i3 i4 xor xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 147: // i1 neg i2 neg and i3 i4 xor xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 148: // i1 i2 xor i3 i4 xor xor
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 149: // i1 i2 xor i3 i4 xor xor neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 150: // i1 i2 and i4 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, rr_nn );
                    result = temp1;
                    break;
                }
                case 151: // i1 neg i2 and i4 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, rr_nn );
                    result = temp1;
                    break;
                }
                case 152: // neg
                {
                    result = zero();
                    break;
                }
                case 153: // i1 i2 neg and i4 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, rr_nn );
                    result = temp1;
                    break;
                }
                case 154: // i1 neg i2 neg and i4 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, rr_nn );
                    result = temp1;
                    break;
                }
                case 155: // i1 i2 and i4 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( rr_nn ) );
                    result = temp1;
                    break;
                }
                case 156: // i1 neg i2 and i4 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( rr_nn ) );
                    result = temp1;
                    break;
                }
                case 157: // i1 i2 neg and i4 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( rr_nn ) );
                    result = temp1;
                    break;
                }
                case 158: // i1 neg i2 neg and i4 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( rr_nn ) );
                    result = temp1;
                    break;
                }
                case 159: // i2 i4 and
                {
                    int temp0 = create_op_node (NodeType.AND, lr_nn, rr_nn );
                    result = temp0;
                    break;
                }
                case 160: // i2 neg i4 and
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    result = temp0;
                    break;
                }
                case 161: // i2 i4 neg and
                {
                    int temp0 = create_op_node (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    result = temp0;
                    break;
                }
                case 162: // i2 neg i4 neg and
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    result = temp0;
                    break;
                }
                case 163: // i1 i2 neg and
                {
                    int temp0 = create_op_node (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    result = temp0;
                    break;
                }
                case 164: // i1 neg i2 neg and
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    result = temp0;
                    break;
                }
                case 165: // i1 i2 and
                {
                    int temp0 = create_op_node (NodeType.AND, ll_nn, lr_nn );
                    result = temp0;
                    break;
                }
                case 166: // i1 neg i2 and
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    result = temp0;
                    break;
                }
                case 167: // i1 neg i4 neg and neg i2 and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 168: // i1 i4 neg and neg i2 and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 169: // i1 i2 neg and neg i2 i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 170: // i1 i2 neg and neg i2 i4 neg and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 171: // i1 i2 and neg i2 neg i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 172: // i1 i2 and neg i2 neg i4 neg and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 173: // i1 neg i4 neg and neg i2 neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 174: // i1 i4 neg and neg i2 neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 175: // i1 neg i4 and neg i2 and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 176: // i1 i4 and neg i2 and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 177: // i1 i2 neg and neg i2 i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 178: // i1 i2 neg and neg i2 i4 and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 179: // i1 i2 and neg i2 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 180: // i1 i2 and neg i2 neg i4 and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 181: // i1 neg i4 and neg i2 neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 182: // i1 i4 and neg i2 neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 183: // i1 i2 xor i2 i4 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 184: // i1 i2 xor neg i1 i4 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 185: // i1 i2 xor i1 i4 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 186: // i1 i2 xor neg i1 neg i4 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 187: // i1 i2 xor i2 i4 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 188: // i1 i2 xor neg i1 i4 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 189: // i1 i2 xor i1 i4 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 190: // i1 i2 xor neg i1 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 191: // i1 i2 and neg i2 i4 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 192: // i1 neg i2 and neg i2 i4 xor and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 193: // i1 i4 and neg i2 i4 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 194: // i1 neg i4 and neg i2 i4 xor and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 195: // i1 i2 and neg i2 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 196: // i1 neg i2 and neg i2 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 197: // i1 i2 neg and neg i2 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 198: // i1 neg i2 neg and neg i2 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 199: // i1 i2 xor i2 i4 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 200: // i1 i4 xor i2 i4 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 201: // i1 i2 xor i1 i4 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 202: // i1 i2 xor neg i1 i4 xor neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 203: // i1 i4 xor i2 and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 204: // i1 i4 xor neg i2 and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = temp1;
                    break;
                }
                case 205: // i1 i4 xor i2 neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 206: // i1 i4 xor neg i2 neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 207: // i1 i4 xor i2 and neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 208: // i1 i4 xor neg i2 and neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 209: // i1 i4 xor i2 neg and neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 210: // i1 i4 xor neg i2 neg and neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 211: // i2 i4 neg and i1 xor
                {
                    int temp0 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = temp1;
                    break;
                }
                case 212: // i2 i4 neg and i1 xor neg
                {
                    int temp0 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 213: // i2 neg i4 neg and i1 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 214: // i2 neg i4 neg and i1 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = temp1;
                    break;
                }
                case 215: // i2 i4 and i1 xor
                {
                    int temp0 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = temp1;
                    break;
                }
                case 216: // i2 i4 and i1 xor neg
                {
                    int temp0 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 217: // i2 neg i4 and i1 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 218: // i2 neg i4 and i1 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = temp1;
                    break;
                }
                case 219: // i1 neg i2 and i4 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rr_nn );
                    result = temp1;
                    break;
                }
                case 220: // i1 i2 and i4 xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rr_nn );
                    result = temp1;
                    break;
                }
                case 221: // i1 neg i2 neg and i4 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 222: // i1 i2 neg and i4 xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 223: // i1 neg i2 and i4 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 224: // i1 i2 and i4 xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 225: // i1 neg i2 neg and i4 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rr_nn );
                    result = temp1;
                    break;
                }
                case 226: // i1 i2 neg and i4 xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rr_nn );
                    result = temp1;
                    break;
                }
                case 227: // i1 i4 xor
                {
                    int temp0 = create_op_node (NodeType.XOR, ll_nn, rr_nn );
                    result = temp0;
                    break;
                }
                case 228: // i1 i4 xor neg
                {
                    int temp0 = create_op_node (NodeType.XOR, ll_nn, rr_nn );
                    result = NEGATE( temp0 );
                    break;
                }
                case 229: // i1 i3 and i2 i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 230: // i1 neg i3 and i2 i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 231: // i1 i3 and i2 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 232: // i1 neg i3 and i2 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 233: // i1 i3 neg and i2 i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 234: // i1 neg i3 neg and i2 i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 235: // i1 i3 neg and i2 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 236: // i1 neg i3 neg and i2 neg i4 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 237: // i1 i3 and i2 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 238: // i1 neg i3 and i2 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 239: // i1 i3 and i2 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 240: // i1 neg i3 and i2 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 241: // i1 i3 neg and i2 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 242: // i1 neg i3 neg and i2 i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 243: // i1 i3 neg and i2 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 244: // i1 neg i3 neg and i2 neg i4 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 245: // i1 i3 xor i2 i4 xor xor
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 246: // i1 i3 xor i2 i4 xor xor neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 247: // i1 i4 and
                {
                    int temp0 = create_op_node (NodeType.AND, ll_nn, rr_nn );
                    result = temp0;
                    break;
                }
                case 248: // i1 neg i4 and
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    result = temp0;
                    break;
                }
                case 249: // i1 i4 neg and
                {
                    int temp0 = create_op_node (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    result = temp0;
                    break;
                }
                case 250: // i1 neg i4 neg and
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    result = temp0;
                    break;
                }
                case 251: // i2 neg i4 neg and neg i1 and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 252: // i1 neg i2 and neg i1 i4 and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 253: // i2 i4 neg and neg i1 and neg
                {
                    int temp0 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 254: // i1 neg i2 and neg i1 i4 neg and neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 255: // i1 i2 and neg i1 neg i4 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 256: // i2 neg i4 neg and neg i1 neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( lr_nn ), NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 257: // i1 i2 and neg i1 neg i4 neg and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 258: // i2 i4 neg and neg i1 neg and neg
                {
                    int temp0 = create (NodeType.AND, lr_nn, NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 259: // i2 neg i4 and neg i1 and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 260: // i1 neg i2 and neg i1 i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 261: // i2 i4 and neg i1 and neg
                {
                    int temp0 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 262: // i1 neg i2 and neg i1 i4 and neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 263: // i1 i2 and neg i1 neg i4 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 264: // i2 neg i4 and neg i1 neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 265: // i1 i2 and neg i1 neg i4 and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 266: // i2 i4 and neg i1 neg and neg
                {
                    int temp0 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 267: // i1 i2 and neg i1 i4 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 268: // i1 i4 xor i2 i4 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, lr_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 269: // i1 i2 neg and neg i1 i4 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 270: // i1 i4 xor i2 neg i4 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( lr_nn ), rr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 271: // i1 i2 and neg i1 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 272: // i1 neg i2 and neg i1 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 273: // i1 i2 neg and neg i1 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 274: // i1 neg i2 neg and neg i1 i4 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 275: // i2 i4 xor i1 and
                {
                    int temp0 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, ll_nn );
                    result = temp1;
                    break;
                }
                case 276: // i2 i4 xor neg i1 and
                {
                    int temp0 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = temp1;
                    break;
                }
                case 277: // i2 i4 xor i1 neg and
                {
                    int temp0 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( ll_nn ) );
                    result = temp1;
                    break;
                }
                case 278: // i2 i4 xor neg i1 neg and
                {
                    int temp0 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = temp1;
                    break;
                }
                case 279: // i2 i4 xor i1 and neg
                {
                    int temp0 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 280: // i2 i4 xor neg i1 and neg
                {
                    int temp0 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 281: // i2 i4 xor i1 neg and neg
                {
                    int temp0 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 282: // i2 i4 xor neg i1 neg and neg
                {
                    int temp0 = create (NodeType.XOR, lr_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 283: // i1 i4 neg and i2 xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 284: // i1 i4 neg and i2 xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 285: // i1 neg i4 neg and i2 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 286: // i1 neg i4 neg and i2 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 287: // i1 i4 and i2 xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 288: // i1 i4 and i2 xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 289: // i1 neg i4 and i2 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 290: // i1 neg i4 and i2 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 291: // i2 i4 xor
                {
                    int temp0 = create_op_node (NodeType.XOR, lr_nn, rr_nn );
                    result = temp0;
                    break;
                }
                case 292: // i2 i4 xor neg
                {
                    int temp0 = create_op_node (NodeType.XOR, lr_nn, rr_nn );
                    result = NEGATE( temp0 );
                    break;
                }
                case 293: // i1 i3 and i2 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 294: // i1 neg i3 and i2 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 295: // i1 i3 neg and i2 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 296: // i1 neg i3 neg and i2 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 297: // i1 i3 and i2 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 298: // i1 neg i3 and i2 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 299: // i1 i3 neg and i2 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 300: // i1 neg i3 neg and i2 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 301: // i3 i2 and
                {
                    int temp0 = create_op_node (NodeType.AND, rl_nn, lr_nn );
                    result = temp0;
                    break;
                }
                case 302: // i3 neg i2 and
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( rl_nn ), lr_nn );
                    result = temp0;
                    break;
                }
                case 303: // i3 i2 neg and
                {
                    int temp0 = create_op_node (NodeType.AND, rl_nn, NEGATE( lr_nn ) );
                    result = temp0;
                    break;
                }
                case 304: // i3 neg i2 neg and
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( rl_nn ), NEGATE( lr_nn ) );
                    result = temp0;
                    break;
                }
                case 305: // i1 neg i3 neg and neg i2 and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 306: // i1 i3 neg and neg i2 and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 307: // i1 i2 neg and neg i3 i2 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 308: // i1 i2 neg and neg i3 neg i2 and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 309: // i1 neg i3 and neg i2 and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 310: // i1 i3 and neg i2 and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 311: // i1 i2 neg and neg i3 neg i2 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 312: // i1 i2 neg and neg i3 i2 and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create (NodeType.AND, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 313: // i1 i2 and neg i3 i2 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 314: // i1 i2 and neg i3 neg i2 neg and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 315: // i1 neg i3 neg and neg i2 neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 316: // i1 i3 neg and neg i2 neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 317: // i1 i2 and neg i3 neg i2 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 318: // i1 i2 and neg i3 i2 neg and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 319: // i1 neg i3 and neg i2 neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 320: // i1 i3 and neg i2 neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 321: // i1 i2 xor i3 i2 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 322: // i1 i3 and neg i1 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 323: // i1 i2 xor i3 neg i2 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rl_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 324: // i1 i3 neg and neg i1 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 325: // i1 i3 and neg i1 i2 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 326: // i1 neg i3 and neg i1 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 327: // i1 i3 neg and neg i1 i2 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 328: // i1 neg i3 neg and neg i1 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 329: // i1 i2 and neg i3 i2 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 330: // i1 neg i2 and neg i3 i2 xor and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 331: // i1 i3 and neg i3 i2 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 332: // i1 neg i3 and neg i3 i2 xor and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 333: // i1 i3 and neg i3 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 334: // i1 neg i3 and neg i3 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 335: // i1 i3 neg and neg i3 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 336: // i1 neg i3 neg and neg i3 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.XOR, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 337: // i1 i2 xor i3 i2 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 338: // i1 i3 xor i3 i2 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, rl_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 339: // i1 i3 xor i1 i2 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 340: // i1 i3 xor neg i1 i2 xor neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 341: // i1 i3 xor i2 and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 342: // i1 i3 xor neg i2 and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = temp1;
                    break;
                }
                case 343: // i1 i3 xor i2 neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 344: // i1 i3 xor neg i2 neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 345: // i1 i3 xor i2 and neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 346: // i1 i3 xor neg i2 and neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), lr_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 347: // i1 i3 xor i2 neg and neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 348: // i1 i3 xor neg i2 neg and neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( lr_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 349: // i3 neg i2 and i1 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( rl_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = temp1;
                    break;
                }
                case 350: // i3 neg i2 and i1 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( rl_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 351: // i3 i2 and i1 xor
                {
                    int temp0 = create (NodeType.AND, rl_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = temp1;
                    break;
                }
                case 352: // i3 i2 and i1 xor neg
                {
                    int temp0 = create (NodeType.AND, rl_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 353: // i3 neg i2 neg and i1 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 354: // i3 neg i2 neg and i1 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( rl_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = temp1;
                    break;
                }
                case 355: // i3 i2 neg and i1 xor neg
                {
                    int temp0 = create (NodeType.AND, rl_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 356: // i3 i2 neg and i1 xor
                {
                    int temp0 = create (NodeType.AND, rl_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, ll_nn );
                    result = temp1;
                    break;
                }
                case 357: // i1 neg i2 and i3 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rl_nn );
                    result = temp1;
                    break;
                }
                case 358: // i1 i2 and i3 xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rl_nn );
                    result = temp1;
                    break;
                }
                case 359: // i1 neg i2 neg and i3 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rl_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 360: // i1 i2 neg and i3 xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rl_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 361: // i1 neg i2 and i3 xor neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rl_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 362: // i1 i2 and i3 xor neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rl_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 363: // i1 neg i2 neg and i3 xor
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rl_nn );
                    result = temp1;
                    break;
                }
                case 364: // i1 i2 neg and i3 xor
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.XOR, temp0, rl_nn );
                    result = temp1;
                    break;
                }
                case 365: // i1 i3 xor
                {
                    int temp0 = create_op_node (NodeType.XOR, ll_nn, rl_nn );
                    result = temp0;
                    break;
                }
                case 366: // i1 i3 xor neg
                {
                    int temp0 = create_op_node (NodeType.XOR, ll_nn, rl_nn );
                    result = NEGATE( temp0 );
                    break;
                }
                case 367: // i1 i2 and neg
                {
                    int temp0 = create_op_node (NodeType.AND, ll_nn, lr_nn );
                    result = NEGATE( temp0 );
                    break;
                }
                case 368: // i2 neg
                {
                    result = NEGATE( lr_nn );
                    break;
                }
                case 369: // i1 neg
                {
                    result = NEGATE( ll_nn );
                    break;
                }
                case 370: // i1 i2 xor
                {
                    int temp0 = create_op_node (NodeType.XOR, ll_nn, lr_nn );
                    result = temp0;
                    break;
                }
                case 371: // i1 neg i2 and neg
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    result = NEGATE( temp0 );
                    break;
                }
                case 372: // i1 i2 xor neg
                {
                    int temp0 = create_op_node (NodeType.XOR, ll_nn, lr_nn );
                    result = NEGATE( temp0 );
                    break;
                }
                case 373: // i1
                {
                    result = ll_nn;
                    break;
                }
                case 374: // i1 i2 neg and neg
                {
                    int temp0 = create_op_node (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    result = NEGATE( temp0 );
                    break;
                }
                case 375: // i2
                {
                    result = lr_nn;
                    break;
                }
                case 376: // i1 neg i2 neg and neg
                {
                    int temp0 = create_op_node (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    result = NEGATE( temp0 );
                    break;
                }
                case 377: //
                {
                    result = one();
                    break;
                }
                case 378: // i1 i3 and i4 i2 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.AND, rr_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 379: // i1 neg i3 and i4 i2 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.AND, rr_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 380: // i1 i3 and i4 i2 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.AND, rr_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 381: // i1 neg i3 and i4 i2 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.AND, rr_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 382: // i1 i3 neg and i4 i2 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, rr_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 383: // i1 neg i3 neg and i4 i2 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, rr_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 384: // i1 i3 neg and i4 i2 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, rr_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 385: // i1 neg i3 neg and i4 i2 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, rr_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 386: // i1 i3 and i4 neg i2 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rr_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 387: // i1 neg i3 and i4 neg i2 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rr_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 388: // i1 i3 and i4 neg i2 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rl_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rr_nn ), NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 389: // i1 neg i3 and i4 neg i2 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rl_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rr_nn ), NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 390: // i1 i3 neg and i4 neg i2 and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rr_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 391: // i1 neg i3 neg and i4 neg i2 and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rr_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 392: // i1 i3 neg and i4 neg i2 neg and and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rr_nn ), NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 393: // i1 neg i3 neg and i4 neg i2 neg and and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rl_nn ) );
                    int temp1 = create (NodeType.AND, NEGATE( rr_nn ), NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 394: // i1 i3 xor i4 i2 xor xor
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 395: // i1 i3 xor i4 i2 xor xor neg
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rl_nn );
                    int temp1 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.XOR, temp0, temp1 );
                    result = NEGATE( temp2 );
                    break;
                }
                case 396: // i1 i4 and i2 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 397: // i1 i4 and i2 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 398: // i1 neg i4 and i2 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 399: // i1 neg i4 and i2 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 400: // i1 i4 neg and i2 and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 401: // i1 i4 neg and i2 neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 402: // i1 neg i4 neg and i2 and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, lr_nn );
                    result = temp1;
                    break;
                }
                case 403: // i1 neg i4 neg and i2 neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( lr_nn ) );
                    result = temp1;
                    break;
                }
                case 404: // i4 neg i2 neg and neg i1 and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( rr_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 405: // i1 i4 and neg i1 neg i2 and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 406: // i4 neg i2 and neg i1 and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( rr_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 407: // i1 i4 and neg i1 neg i2 neg and neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 408: // i1 neg i4 and neg i1 i2 and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 409: // i4 neg i2 neg and neg i1 neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( rr_nn ), NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 410: // i1 neg i4 and neg i1 i2 neg and neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 411: // i4 neg i2 and neg i1 neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( rr_nn ), lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 412: // i4 i2 neg and neg i1 and neg
                {
                    int temp0 = create (NodeType.AND, rr_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 413: // i1 i4 and neg i1 neg i2 neg and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 414: // i4 i2 and neg i1 and neg
                {
                    int temp0 = create (NodeType.AND, rr_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 415: // i1 i4 and neg i1 neg i2 and neg and neg
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 416: // i1 neg i4 and neg i1 i2 neg and neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 417: // i4 i2 neg and neg i1 neg and neg
                {
                    int temp0 = create (NodeType.AND, rr_nn, NEGATE( lr_nn ) );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 418: // i1 neg i4 and neg i1 i2 and neg and neg
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = NEGATE( temp2 );
                    break;
                }
                case 419: // i4 i2 and neg i1 neg and neg
                {
                    int temp0 = create (NodeType.AND, rr_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 420: // i1 i4 and neg i1 i2 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 421: // i1 i4 and neg i1 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, rr_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 422: // i1 i2 xor i4 i2 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, rr_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 423: // i1 neg i4 and neg i1 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), rr_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 424: // i1 i4 neg and neg i1 i2 xor and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), temp1 );
                    result = temp2;
                    break;
                }
                case 425: // i1 i4 neg and neg i1 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, ll_nn, NEGATE( rr_nn ) );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 426: // i1 i2 xor i4 neg i2 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( rr_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 427: // i1 neg i4 neg and neg i1 i2 xor neg and
                {
                    int temp0 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( rr_nn ) );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 428: // i1 i4 xor i1 i2 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 429: // i1 i4 xor i4 i2 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, rr_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 430: // i1 i4 xor i1 i2 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 431: // i1 i4 xor i4 i2 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, rr_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, temp0, NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 432: // i1 i4 xor neg i1 i2 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 433: // i1 i4 xor neg i1 neg i2 and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 434: // i1 i4 xor neg i1 i2 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, ll_nn, NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 435: // i1 i4 xor neg i1 neg i2 neg and neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.AND, NEGATE( ll_nn ), NEGATE( lr_nn ) );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 436: // i1 i4 xor i1 i2 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 437: // i1 i4 xor i4 i2 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 438: // i1 i2 xor i4 i2 xor and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp1 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, temp0, temp1 );
                    result = temp2;
                    break;
                }
                case 439: // i1 i4 xor neg i1 i2 xor neg and
                {
                    int temp0 = create (NodeType.XOR, ll_nn, rr_nn );
                    int temp1 = create (NodeType.XOR, ll_nn, lr_nn );
                    int temp2 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( temp1 ) );
                    result = temp2;
                    break;
                }
                case 440: // i4 i2 xor i1 and
                {
                    int temp0 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, ll_nn );
                    result = temp1;
                    break;
                }
                case 441: // i4 i2 xor neg i1 and
                {
                    int temp0 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = temp1;
                    break;
                }
                case 442: // i4 i2 xor i1 neg and
                {
                    int temp0 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( ll_nn ) );
                    result = temp1;
                    break;
                }
                case 443: // i4 i2 xor neg i1 neg and
                {
                    int temp0 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = temp1;
                    break;
                }
                case 444: // i4 i2 xor i1 and neg
                {
                    int temp0 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 445: // i4 i2 xor neg i1 and neg
                {
                    int temp0 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), ll_nn );
                    result = NEGATE( temp1 );
                    break;
                }
                case 446: // i4 i2 xor i1 neg and neg
                {
                    int temp0 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, temp0, NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 447: // i4 i2 xor neg i1 neg and neg
                {
                    int temp0 = create (NodeType.XOR, rr_nn, lr_nn );
                    int temp1 = create_op_node (NodeType.AND, NEGATE( temp0 ), NEGATE( ll_nn ) );
                    result = NEGATE( temp1 );
                    break;
                }
                case 448: // i4 i2 xor
                {
                    int temp0 = create_op_node (NodeType.XOR, rr_nn, lr_nn );
                    result = temp0;
                    break;
                }
                case 449: // i4 i2 xor neg
                {
                    int temp0 = create_op_node (NodeType.XOR, rr_nn, lr_nn );
                    result = NEGATE( temp0 );
                    break;
                }
                default:
                    throw new Exception ("Unknown Cases");

            }
            return result;
        }
        #endregion

    }
}

