// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Text;
using System.IO;
//using Microsoft.Zap;
namespace SharpSAT
{
    //This class implements the C# interface for a SAT solver
    public class SATSolver : SharpSATSolver
    {
        [Microsoft.Contracts.NotDelayed]
        public SATSolver() {}

        //
        // This part is the conventional clause based SAT solver
        // formula is represented in Conjunctive Normal Form (CNF)
        // which is a conjunction of clauses, each of which is a
        // disjunction of literals
        //
        // Variables are indexed from 1 up to NumVariables.
        // The number of variables can be set upfront using
        // SetNumVariables or dynamically increased in the
        // solving process.   
        public double SessionCpuTime ()         { return base.session_cpu_time();}

        public double TotalCpuTime()            { return base.total_cpu_time(); }


        #region Managing Clause Database

        #region Managing Clause Groups

        public int AllocGID ()                  { return base.alloc_gid(); }

        public void FreeGID (int gid)           { base.free_gid(gid);}

        public int  MergeGroup (int g1, int g2) { return base.merge_clause_group (g1, g2); }

        public void DeleteGroup (int gid)       { base.delete_clause_group(gid); }

        #endregion

        public void SetNumVariables(int a)      { base.set_num_variables(a); }

        public int GetNumVariables()            { return base.num_variables(); }

        public int AddVariable()                { return base.add_variable(); }

        public int AddClause( int[] lits, int gid, bool do_check)   { return base.add_clause (lits, gid, do_check); }

        public int AddClause ( int[] lits )                         { return base.add_clause (lits, 0, true /*check */); }

        public int AddClause (int[] lits, int gid)                  { return base.add_clause (lits, gid, true /*check */); }

        public int AddClauseNoCheck ( int[] lits )                  { return base.add_clause (lits, 0, false /*check */); }

        public int AddClauseNoCheck ( int[] lits, int gid )         { return base.add_clause (lits, gid, false /*check */);}
        #endregion

        #region Solving Instance

        public void SetBranchable(int vid)      { base.set_branchable(vid, true); }

        public void UnsetBranchable(int vid)    { base.set_branchable(vid, false); }

        public int VariableValue(int vid)       { return base.var_value(vid); }

        public int LiteralValue(int lit)        { int v = base.lit_value( lit ); return ((v&1) == v)? v: 2; }

        public SATStatus Solve()                { return base.solve(); }

        public SATStatus ContinueSolve()        { return base.solve(); }

        public void Reset()                     { base.reset(); }

        public void Restart()                   { base.restart();}
        #endregion

        #region Unsat Core and Interpolants
        //public void EnableTraceGen()          { base.enable_rtrace(true); }

        //public void DisableProofGen()             { base.enable_rtrace(false);}

        // return null if instance is SAT
        public UnsatCore GenUnsatCore()         { return base.gen_unsat_core(); }

        // return -1 if instance is SAT
        public int GenInterpolantFromClauseGroups (int a_gid, int b_gid)
                                                { return base.gen_interpolant_from_clauses(a_gid, b_gid); }
        // return -1 if and(a,b) is SAT
        public int GenInterpolantFromSignals    ( int signal_a, int signal_b)
        {
            if (signal_a == zero() || signal_b == zero())
                throw new Exception("One of the Input is Zero for Interpolation");
            return base.gen_interpolant_from_signals(signal_a, signal_b);
        }

        // gretay - change start
        // return -1 if and(a,b) is SAT
        public int GenInterpolantFromSignalsEx( int signal_a, int signal_b)
        {
            if (signal_a == zero() || signal_b == zero())
                throw new Exception("One of the Input is Zero for Interpolation");
            return base.gen_interpolant_from_signals_ex(signal_a, signal_b);
        }
        public void SetInterpolant(int cl_uid, int i)
        {
            base.set_interpolant(cl_uid, i);
        }
        // gretay - change end

        #endregion

        // given two Boolean formulas represented by s1 and s2, return the logic formula
        // corresponding to AND(s1,s2), OR(s1,s2)... etc
        // 
        public int  Constraint (int s)          { return base.constraint(s); }

        public void ReleaseConstraint(int c)    { base.release_constraint(c); }

        #region Structure Interface
        public int  GetOne ()                   { return base.one() ; }

        public int  GetZero ()                  { return base.zero(); }

        public int  CreatePI()                  { return base.new_pi(); }

        public int  NthPI(int n)                { return base.nth_pi(n); }

        public void ConvertVarsToPI()           { base.convert_vars_to_pi(); }

        public int  And(int a, int b)           { return base.band(a, b); }

        public int  Or(int a, int b)            { return base.bor(a, b); }

        public int  Not(int a)                  { return base.bnot(a); }

        public int  Xor(int a, int b)           { return base.bxor(a, b); }

        public int  Equ(int a, int b)           { return base.bequ(a, b); }

        public int  Imp(int a, int b)           { return base.bimp(a, b); }

        public bool IsNegated(int s)            { return IS_NEGATED(s); }

        public int  NonNegated(int s)           { return NON_NEGATED(s); }

        public void Reference(int a)            { base.reference(a); }

        public void Deref(int a)                { base.deref(a); }

        public int  NumPI()                     { return base.num_pi(); }

        public int  PiVarValue (int k)          { return base.pi_var_value(k); }

        //note: start from 0, up to NumPI - 1
        public int  PrimaryInput(int k)         { return base.nth_pi(k); }

        public int  LeftChild(int sig)          { return base.left_child(sig); }

        public int  RightChild(int sig)         { return base.right_child(sig); }

        public NodeType NdType (int sig)        { return base.node_type(sig); }

        public int  NodeToPI (int sig)          { return base.node_to_pi(sig); }

        public int  AllocFlag ()                        { return base.alloc_flag(); }

        public void ClearFlag(int flag_id)              { base.clear_flag_for_all(flag_id); }

        public bool IsNodeFlagSet(int s, int flag_id)   { return base.is_flag_set(s, flag_id); }

        // orig[] and replace[] should have the same size. Given a Boolean formula
        // represented by s, function compose will generate a new Boolean formula
        // that rename all orig[i] to replace[i] in s.
        // 
        public int Compose (int s, int [] orig, int [] replace )
        {
            return base.compose(s, orig, replace);
        }

        // Mark the transitive fanins and fanouts of a signal s. After marking
        // nodes belong to the fanin/fanout set are marked for the flag. A node
        // can be tested for whether it belongs to the set using IsNodeFlagSet()
        // 

        public void MarkTransitiveFanins(int s, int flag)
        {
            base.mark_transitive_fanins(s, flag);
        }

        public void MarkTransitiveOuts(int s, int flag)
        {
            base.mark_transitive_fanouts(s, flag);
        }
        #endregion

        #region TestSAT
        //two examples of how to use the interface

        // Test if logic formula represented by s is satisfiable (i.e. exist a
        // primary inputs assignment such that s evaluate to true.
        // 

        public SATStatus TestSAT (int s)
        {
            if (s == GetZero())
                return SATStatus.UNSATISFIABLE;
            else if (s == GetOne())
                return SATStatus.SATISFIABLE;

            int c = Constraint(s);
            SATStatus status = Solve();
            ReleaseConstraint (c);
            return status;
        }

        // Test if logic formula represented by s is satisfiable. If it is,
        // return the satisfiable primary input assignments, otherwise return
        // null. Notice this function has about the same complexity as
        // TestSAT(), so you should avoid calling testSAT first and then based
        // on the result call FindSATAssignment. If you don't know whether s is
        // satisfiable, call FindSatAssignment directly, and based on the return
        // value you should know if s is satisfiable or not.
        // 
        public int[] FindSatAssignment (int s)
        {
            int[] pi_values = null;

            if (s == GetZero())
                return null;
            else if (s == GetOne()) {
                pi_values = new int[NumPI()];
                for (int i = 0; i < pi_values.Length; ++i)
                    pi_values[i] = 2;
                return pi_values;
            }
            else {
                int c = Constraint(s);
                SATStatus status = Solve();
                if (status == SATStatus.SATISFIABLE) {
                    pi_values = new int[NumPI()];
                    for (int i = 0; i < NumPI(); ++i) {
                        int l = LiteralValue(PrimaryInput(i));
                        if (l != 0 && l != 1)
                            pi_values[i] = 2;
                        else
                            pi_values[i] = l;
                    }
                }
                ReleaseConstraint(c);
                return pi_values;
            }
        }
        #endregion

        public int DecisionLevel()                  { return d_level(); }

        public int [] AssignmentAtLevel(int l ) { return assignment_stack(l).ToArray(); }

        public ObjVector AssignmentStack()          { return assignment_stack(); }

        public void MakeDecision (int svar)     { base.make_decision(svar); }

        public void SetHookObject (SATHook hk)      { base.hook = hk; }

        //(a & b & c => d)   reasons[!a, !b, !c] imply=d
        // reasons can be null
        public void AddImplication (int [] reasons, int imply) { base.add_new_implication(reasons, imply); }

        public int EnumExistQuantify (int s, int [] bound) { return base.enum_exist_quantify_smart (s, bound); }

        public int [] FindSmallModel () { return base.find_small_model(); }

        #region ToString Methods
        // return the string representation of this particular node
        // 
        public string ToString (int sig, MyHashtable nameMap)
        {
            string result = sig.ToString() + "\t= ";
            if (IsNegated(sig)) {
                int t = NonNegated(sig);
                result +=  "Not(" +
                    t.ToString() + ")\n" +
                    ToString (t, nameMap);
            }
            else {
                NodeType tp = NdType(sig);
                switch (tp) {
                    case NodeType.UNKNOWN:
                    case NodeType.FREE:
                    case NodeType.CONSTANT:
                    case NodeType.VARIABLE:
                        result += "ERROR";
                        break;
                    case NodeType.AND:
                    case NodeType.XOR:
                        int l = LeftChild(sig);
                        int r = RightChild(sig);
                        string lstr, rstr;
                        lstr = l.ToString();
                        rstr = r.ToString();

                        if (tp == NodeType.AND)
                            result += "AND (" + lstr + ", " + rstr + ")";
                        else
                            result += "XOR (" + lstr + ", " + rstr + ")";
                        break;
                    case NodeType.PI:
                        int sig_pi = NodeToPI(sig);
                        if (sig_pi != -1) {
                            if (nameMap.Contains(sig_pi))
                                result += nameMap[sig_pi];
                            else
                                result += "PI" + sig_pi.ToString();
                        }
                        else
                            result += "ERROR";
                        break;
                }
                result += "\n";
            }
            return result;
        }

        // return the string representation of the whole
        // tree rooted at this particular node
        // 
        public string TreeToString (int sig, MyHashtable nameMap)
        {
            MyHashtable inqueue = new MyHashtable();
            Queue todo = new Queue();
            todo.Enqueue (sig);
            StringBuilder result = new StringBuilder();
            while (todo.Count != 0) {
                int nd = (int)todo.Dequeue();
                int l = LeftChild(nd);
                int r = RightChild(nd);
                NodeType tp = NdType(nd);
                if (tp == NodeType.AND || tp == NodeType.XOR) {
                    if (!inqueue.Contains(l)) {
                        todo.Enqueue(l);
                        inqueue.Add (l, null);
                    }
                    if (!inqueue.Contains(r)) {
                        todo.Enqueue(r);
                        inqueue.Add (r, null);
                    }
                }
                result.Append (ToString(nd, nameMap));
            }
            return result.ToString();
        }
    }
    #endregion
}
