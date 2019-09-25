// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Text;
using System.IO;
using SharpSAT;
using Microsoft.Singularity;

//using Microsoft.Zap;

namespace SharpSATTest
{
    public class SATSolverTests : SATCommon
    {
        // a helper function   
        static private string getToken(string [] tokens, ref int index)
        {
            for (; index < tokens.Length;) {
                ++index;
                if (tokens[index - 1] != String.Empty)
                    return tokens[index -1];
            }
            return null;
        }

        // this demonstrate the structure interface   
        static void test_structure_solver (string[] args)
        {
            SATSolver solver = new SATSolver();
            int a = solver.CreatePI();
            int b = solver.CreatePI();
            int c = solver.CreatePI();
            //int d = solver.CreatePI();
            int xor_a_b = solver.Xor(a, b);
            int not_a = solver.Not(a);
            int not_b = solver.Not(b);
            int and_a_not_b = solver.And (a, not_b);
            int and_b_not_a = solver.And (b, not_a);
            int xor_a_b_p = solver.Or(and_a_not_b, and_b_not_a);
            int miter = solver.Xor(xor_a_b, xor_a_b_p);
            SATStatus r = solver.TestSAT(miter);
            WriteLine(String.Format("Test Right {0}", r.ToString()));

            int and_a_b = solver.And (a, b);
            int xor_a_b_wrong = solver.Or (and_a_not_b, and_a_b);
            int miter1 = solver.Xor(xor_a_b, xor_a_b_wrong);
            r = solver.TestSAT(miter1);
            WriteLine(String.Format("Test Wrong {0}", r.ToString()));

            int and_a_b_c = solver.And (solver.And(a,b), c);

            int flag = solver.AllocFlag ();
            solver.MarkTransitiveFanins(and_a_b_c, flag);
            for (int i = 0, sz = solver.NumPI(); i < sz; ++i) {
                int node_id = solver.NthPI(i);
                bool flagset = solver.IsNodeFlagSet (node_id, flag);
                if (flagset)
                    WriteLine(String.Format("PI {0} is in the transitive fanin", i));
                else
                    WriteLine(String.Format("PI {0} is NOT in the transitive fanin", i));
            }
            solver.ClearFlag(flag);


            MyHashtable nameMap = new MyHashtable();
            nameMap.Add(0, "PrimaryIn 0");
            WriteLine(solver.TreeToString(miter1, nameMap));
            WriteLine(solver.TreeToString(xor_a_b, nameMap));

            WriteLine("Press Return...");
            System.Console.ReadLine();
        }

        // this demonstrate the clause interface, it reads in a CNF file and
        // Solve it, just as a regular SAT solver should do   
        static void test_clause_solver (string[] args)
        {
            SATSolver solver = new SATSolver();

            // NB: on Singularity, args[0] is the exe image name
            if (args.Length != 2) {
                WriteLine("Simple SAT Solver using the C# interface");
                WriteLine("Usage: sharpSat CNF_file ");
                return;
            }
            StreamReader input = null;
            try {
                input = new StreamReader(args[1]);
            }
            catch (Exception e) {
                WriteLine("Error opening file '" + args[1] + "' :" + e.ToString());
                return;
            }

            string line;
            WriteLine(String.Format("Solving {0}", args[1]));
            while (true) {
                try{
                    line = input.ReadLine();
                }
                catch (Exception e){
                    WriteLine("Error reading file '" + args[1] + "' :" + e.ToString());
                    line = null;
                }
                if (line == null)
                    break;
                string [] tokens = line.Split(new char[] {' ','\t'});
                int index = 0;
                string token = getToken (tokens, ref index);
                if (token == "c")
                    continue;
                if (token == "p") {
                    token = getToken (tokens, ref index);
                    if (token != "cnf") {
                        WriteLine("Unrecognized Header");
                        return;
                    }
                    else {
                        token = getToken (tokens, ref index);
                        solver.SetNumVariables (int.Parse(token));
                        continue;
                    }
                }
                else {
                    ArrayList lits = new ArrayList();
                    while (token != null && int.Parse(token) != 0) {
                        lits.Add (int.Parse(token));
                        token = getToken (tokens, ref index);
                    }


                    if (lits.Count > 0) {
                        int [] clause = new int [lits.Count];
                        for (int k = 0; k < lits.Count; ++k) {
                            clause[k] = (int)lits[k];
                            if (clause[k] > 0)
                                clause[k] += clause[k];
                            else
                                clause[k] = 1 - clause[k] - clause[k];
                        }
                        solver.AddClause ( clause );
                    }
                }
            }
            input.Close();
            SATStatus result = solver.Solve();
            StringBuilder sb = new StringBuilder();
            if (result == SATStatus.SATISFIABLE) {
                WriteLine("SAT");
                for (int i = 1; i <= solver.GetNumVariables(); ++i) {
                    if (solver.VariableValue(i) == 1) {
                        sb.Append(String.Format("{0} ", i));
                    }
                    else if (solver.VariableValue(i) == 0) {
                        sb.Append(String.Format("-{0} ", i));
                    }
                    else {
                        sb.Append(String.Format("({0}) ", i));
                    }
                    if (i % 10 == 0) {
                        WriteLine(sb.ToString());
                        sb.Length = 0;
                    }
                }
                WriteLine(sb.ToString());
            }
            else if (result == SATStatus.UNSATISFIABLE)
                WriteLine("UNSAT");

            WriteLine(String.Format("Num Variables            {0}", solver.num_variables()));
            WriteLine(String.Format("Num Orig. Clauses        {0}", solver.stats.num_orig_clauses ));
            WriteLine(String.Format("Num Learned Clauses      {0}", solver.stats.num_learned_clauses));
            WriteLine(String.Format("Num Learned Literals     {0}", solver.stats.num_learned_literals));
            WriteLine(String.Format("Num Garbage Collection   {0}", solver.stats.num_garbage_collections));
            WriteLine(String.Format("Num Deleted Clauses      {0}", solver.stats.num_deleted_clauses ));
            WriteLine(String.Format("Num Deleted Literals     {0}", solver.stats.num_deleted_literals ));
            WriteLine(String.Format("Num Decisions            {0}", solver.stats.num_decisions ));
            WriteLine(String.Format("Num Backtracks           {0}", solver.stats.num_backtracks ));
            WriteLine(String.Format("Num Implications         {0}", solver.stats.num_implications ));
            WriteLine(String.Format("Total Runtime            {0}", solver.stats.total_cpu_time ));
            WriteLine(String.Format("Instance is              {0}", SATCommon.StatusToString(result)));
        }

        public static void log_execution(string [] args)
        {
            SATSolver solver = new SATSolver();
            if (args.Length != 1) {
                WriteLine("Simple SAT Solver using the C# interface");
                WriteLine("Usage: sharpSat CNF_file ");
                return;
            }
            FileInfo file = new FileInfo (args[0]);
            StreamReader input = file.OpenText();
            string line;
            IntVector nodes = new IntVector(4);
            while (true) {
                line = input.ReadLine();
                if (line == null)
                    break;
                string [] tokens = line.Split(new char[] {' ','\t'});
                int index = 0;
                string token = getToken (tokens, ref index);
                int k = int.Parse (token);
                token = getToken (tokens, ref index);
                sharp_assert (token == "=");
                token = getToken (tokens, ref index);
                if (token == "INIT_VARS") {
                    solver.SetNumVariables(k);
                    solver.ConvertVarsToPI();
                    nodes.resize ( k + k + 2);
                    for (int i = 0; i < k + k + 2; ++i)
                        nodes[i] = i;
                }
                else if (token == "CONSTRAINT") {
                    solver.Constraint(nodes[k]);
                    SATStatus status = solver.Solve();
                    if (status == SATStatus.UNSATISFIABLE)
                        WriteLine("UNSAT");
                    else
                        WriteLine("SAT");
                }
                else if (token == "PI") {
                    continue;
                }
                else if (token == "CL") {
                    IntVector lits = new IntVector(4);
                    token = getToken(tokens, ref index);
                    while (token != null) {
                        lits.push_back (int.Parse(token));
                        token = getToken(tokens, ref index);
                    }
                    solver.AddClause(lits.ToArray());
                }
                else if (token == "AND") {
                    token = getToken (tokens, ref index);
                    int i1 = int.Parse (token);
                    token = getToken (tokens, ref index);
                    int i2 = int.Parse (token);
                    int r = solver.And (nodes[i1], nodes[i2]);
                    if (nodes.size() < k + 2)
                        nodes.resize (k + 2);
                    nodes[k] = r;
                    nodes [k ^ 1] = (r^1);
                }
                else if (token == "XOR") {
                    token = getToken (tokens, ref index);
                    int i1 = int.Parse (token);
                    token = getToken (tokens, ref index);
                    int i2 = int.Parse (token);
                    int r = solver.Xor (nodes[i1], nodes[i2]);
                    if (nodes.size() < k + 1)
                        nodes.resize (k + 1);
                    nodes[k] = r;
                    nodes [k ^ 1] = (r^1);
                }
                else
                    fatal ("Unrecognized Symbol");
            }
        }

        static Random rand;

        static int [] randclause (int begin, int end)
        {
            IntVector cls = new IntVector(4);
            while (cls.empty()) {
                double r = rand.NextDouble();
                int a = (int) (r * (end - begin)) + begin;
                r = rand.NextDouble();
                if (r < 0.5)
                    a = a + a;
                else
                    a = a + a + 1;

                r = rand.NextDouble();
                int b = (int) (r * (end - begin)) + begin;
                r = rand.NextDouble();
                if (r < 0.5)
                    b = b + b;
                else
                    b = b + b + 1;

                r = rand.NextDouble();
                int c = (int) (r * (end - begin)) + begin;
                r = rand.NextDouble();
                if (r < 0.5)
                    c = c + c;
                else
                    c = c + c + 1;

                if ((a >> 1) != (b >> 1)) {
                    cls.push_back (a);
                    cls.push_back (b);
                    if ((a >> 1) != (c >> 1) && (b >> 1) != (c >> 1))
                        cls.push_back (c);
                }
                else {
                    cls.push_back (b);
                    if ((b >> 1) != (c >> 1))
                        cls.push_back (c);
                }
            }
            return cls.ToArray();
        }

        static bool test_interpolant_clauses (int n_vars, int n_cls, int span, int randseed)
        {
            rand = new Random(randseed);
            int [] [] a_clauses;
            int [] [] b_clauses;
            a_clauses = new int [n_cls][];
            b_clauses = new int [n_cls][];
            for (int i = 0; i < n_cls; ++i)
                a_clauses[i] = randclause ( 1, n_vars/2 + span);
            for (int i = 0; i < n_cls; ++i)
                b_clauses[i] = randclause ( n_vars/2 - span, n_vars + 1);

            SATSolver solver = new SATSolver();
            solver.SetNumVariables(n_vars);
            int a_gid = solver.AllocGID();
            int b_gid = solver.AllocGID();
            //1. Test if A is satisfiable
            for (int i = 0; i < n_cls; ++i)
                solver.AddClause (a_clauses[i], a_gid);
            if (solver.Solve() != SATStatus.SATISFIABLE) {
                Write("A SAT");
                return false;
            }
            solver.DeleteGroup(a_gid);
            //1. Test if B is satisfiable
            for (int i = 0; i < n_cls; ++i)
                solver.AddClause (b_clauses[i], b_gid);
            if (solver.Solve() != SATStatus.SATISFIABLE) {
                Write("B SAT");
                return false;
            }
            //3. Generate Interpolant
            a_gid = solver.AllocGID();
            for (int i = 0; i < n_cls; ++i)
                solver.AddClause (a_clauses[i], a_gid);
            Write("Interpolant ");
            int interpolant = solver.GenInterpolantFromClauseGroups ( a_gid, b_gid);
            if (interpolant == -1) {
                Write("AB SAT" );
                return false;
            }
            solver.Reference(interpolant);
            //now test IB Unsatisfiable
            Write("IB ");
            solver.DeleteGroup (a_gid);
            sharp_assert (solver.stats.num_orig_clauses ==  n_cls);
            int c = solver.Constraint(interpolant);
            SATStatus status = solver.Solve();
            if (status != SATStatus.UNSATISFIABLE)
                sharp_assert (false);

            //4. test AI Satisfiable
            Write("AI ");
            solver.DeleteGroup (b_gid);
            a_gid = solver.AllocGID();
            for (int i = 0; i < n_cls; ++i)
                solver.AddClause (a_clauses[i], a_gid);
            status = solver.Solve();
            if (status != SATStatus.SATISFIABLE)
                assert(false);
            //5. test AI' Unsat (i.e. A=>I)
            Write("AI' ");
            solver.ReleaseConstraint (c);
            c = solver.Constraint(solver.Not(interpolant));
            status = solver.Solve();
            if (status != SATStatus.UNSATISFIABLE)
                sharp_assert (false);
            solver.ReleaseConstraint (c);
            return true;
        }

        static int build_struct (SATSolver solver, int [][] clauses)
        {
            int sig = solver.one();
            for (int i = 0; i < clauses.Length; ++i) {
                int s = solver.zero();
                foreach (int lit in clauses[i])
                    s = solver.Or(s, lit);
                sig = solver.And(sig, s);
            }
            return sig;
        }

        static bool test_interpolant_structure (int n_vars, int n_cls, int span, int randseed)
        {
            rand = new Random(randseed);
            int [] [] a_clauses;
            int [] [] b_clauses;
            a_clauses = new int [n_cls][];
            b_clauses = new int [n_cls][];
            for (int i = 0; i < n_cls; ++i)
                a_clauses[i] = randclause ( 1, n_vars/2 + span);
            for (int i = 0; i < n_cls; ++i)
                b_clauses[i] = randclause ( n_vars/2 - span, n_vars + 1);

            SATSolver solver = new SATSolver();
            solver.SetNumVariables(n_vars);
            solver.ConvertVarsToPI();
            int s_a = build_struct(solver, a_clauses);
            int s_b = build_struct(solver, b_clauses);
            solver.Reference(s_a);
            solver.Reference(s_b);
            //1. Test if A is satisfiable
            int c_a = solver.Constraint(s_a);
            if (solver.Solve() != SATStatus.SATISFIABLE) {
                Write("A SAT");
                return false;
            }
            solver.ReleaseConstraint(c_a);
            //2. Test if B is satisfiable
            int c_b = solver.Constraint(s_b);
            if (solver.Solve() != SATStatus.SATISFIABLE) {
                Write("B SAT");
                return false;
            }
            solver.ReleaseConstraint(c_b);
            //now get interpolant I
            Write("Interpolant ");
            int interpolant = solver.GenInterpolantFromSignals ( s_a, s_b);
            if (interpolant == -1) {
                Write("AB SAT");
                return false;
            }
            solver.Reference (interpolant);
            //3. test IB Unsatisfiable
            Write("IB ");
            c_b = solver.Constraint(s_b);
            int c_i = solver.Constraint(interpolant);
            SATStatus status = solver.Solve();
            if (status != SATStatus.UNSATISFIABLE)
                sharp_assert (false);
            solver.ReleaseConstraint (c_b);
            //4. test AI Satisfiable
            Write("AI ");
            c_a = solver.Constraint (s_a);
            status = solver.Solve();
            if (status != SATStatus.SATISFIABLE)
                assert(false);
            //5. test AI' Unsat (i.e. A=>I)
            Write("AI' ");
            solver.ReleaseConstraint (c_i);
            solver.Constraint(solver.Not(interpolant));
            status = solver.Solve();
            if (status != SATStatus.UNSATISFIABLE)
                sharp_assert (false);
            return true;
        }

        static int build_irregular_struct (SATSolver solver, int [][] clauses,int randseed)
        {
            Random rand = new Random(randseed);

            int sig = solver.one();
            for (int i = 0; i < clauses.Length; ++i) {
                int s = solver.zero();
                foreach (int lit in clauses[i]) {
                    if (rand.NextDouble() > 0.2)
                        s = solver.Or(s, lit);
                    else
                        s = solver.Xor(s, lit);
                }

                if (rand.NextDouble() > 0.15)
                    sig = solver.And(sig, s);
                else
                    sig = solver.Xor(sig, s);
            }
            return sig;
        }

        static bool test_existential_quantification ( int n_cls, int n_vars, int n_qvar, int rseed)
        {
            rand = new Random(rseed);
            int [] [] clauses = new int [n_cls][];
            for (int i = 0; i < n_cls; ++i)
                clauses[i] = randclause ( 1, n_vars + 1);
            int [] qvars = new int [n_qvar];
            for (int i = 1; i <= n_qvar; ++i)
                qvars[i-1] = i + i;

            SATSolver solver = new SATSolver();
            solver.SetNumVariables(n_vars);
            solver.ConvertVarsToPI();
            int s = build_irregular_struct(solver, clauses, 1);
            int q1 = solver.expand_exist_quantify(s, qvars);
            //int q2 = solver.enum_exist_quantify(s, qvars);
            int q2 = solver.enum_exist_quantify_smart(s, qvars);

            SATStatus status = solver.solve();
            sharp_assert (status == SATStatus.SATISFIABLE);
            int notequ = solver.Xor(q1, q2);
            solver.Constraint(notequ);
            status = solver.Solve();
            sharp_assert (status == SATStatus.UNSATISFIABLE);
            return true;
        }

        public static bool UnitTest()
        {
            SATSolver solver = new SATSolver();

            int ab = solver.NthPI(0);
            int bc = solver.NthPI(1);
            int ac = solver.NthPI(2);

            int not_ab = solver.Not(ab);
            int not_bc = solver.Not(bc);
            solver.Not(ac);

            int fafb = solver.NthPI(3);
            int not_fafb = solver.Not(fafb);

            int fbfc = solver.NthPI(4);
            int not_fbfc = solver.Not(fbfc);

            // ((a=b && b != c) || (a!=b && b=c) || (a!=b && a=c)) && f(a)!=f(b) && f(b)!=f(c)
            int d1 = solver.And(ab, not_bc);
            int d2 = solver.And(bc, not_ab);
            int d3 = solver.And(ac, not_ab);

            int c1 = solver.Or(d1,d2);
            int c2 = solver.Or(c1,d3);

            int c3 = solver.And(c2,not_fafb);
            int c4 = solver.And(c3, not_fbfc);

            int formula = c4;
            int[] ret = solver.FindSatAssignment(formula);
            if (ret == null) return false;

            int[] clause = new int[2];
            clause[0] = solver.Not(ab);
            clause[1] = fafb;
            solver.AddClause(clause);
            ret = solver.FindSatAssignment(formula);
            if (ret == null) return false;
            return true;
        }

        public static void print_model(int [] m)
        {
            WriteLine("Model Is " );
            foreach (int e in m) {
                if ((e & 1) == 1)
                    Write("-");
                Write( (e/2) + " ");
            }
            WriteLine("");
        }

        public static bool test_small_model()
        {
            SATSolver solver = new SATSolver();

            int a = solver.NthPI(0);
            int b = solver.NthPI(1);
            int c = solver.NthPI(2);
            int d = solver.NthPI(3);

            int ab = solver.And(a, b);
            int cd = solver.And(c, d);
            int abcd = solver.And(ab, cd);
            int constraint = solver.Constraint(abcd);
            solver.Solve();
            int [] model = solver.FindSmallModel();
            print_model (model);
            solver.ReleaseConstraint(constraint);

            int not_abcd = solver.Not(abcd);
            constraint = solver.Constraint(not_abcd);
            solver.Solve();
            model = solver.FindSmallModel();
            print_model (model);
            solver.ReleaseConstraint(constraint);

            int e = solver.CreatePI();
            int f = solver.CreatePI();
            int exf = solver.Xor (e, f);
            int and_exf_abcd = solver.And(exf, abcd);
            constraint = solver.Constraint(and_exf_abcd);
            solver.Solve();
            model = solver.FindSmallModel();
            print_model (model);
            solver.ReleaseConstraint(constraint);

            int not_and_exf_abcd = solver.Not(and_exf_abcd);
            constraint = solver.Constraint(not_and_exf_abcd);
            solver.Solve();
            model = solver.FindSmallModel();
            print_model (model);
            solver.ReleaseConstraint(constraint);
            return true;
        }

        public static void test_quantification_edge_case ()
        {
            int n_cls = 100;
            int n_vars = 50;
            int n_qvar = 10;
            rand = new Random(10);
            int [] [] clauses = new int [n_cls][];
            for (int i = 0; i < n_cls; ++i)
                clauses[i] = randclause ( 1, n_vars + 1);
            int [] qvars = new int [n_qvar];
            for (int i = 1; i <= n_qvar; ++i)
                qvars[i-1] = i + i;

            SATSolver solver = new SATSolver();
            solver.SetNumVariables(n_vars);
            solver.ConvertVarsToPI();
            build_irregular_struct(solver, clauses, 1);

            int t = solver.GetOne();
            int f = solver.GetZero();
            int s1 = solver.And (t, 10);
            int s2 = solver.And (f, 10);
            int [] bounded = new int[2];
            bounded[0] = 2;
            bounded[1] = 3;
            int result = solver.EnumExistQuantify (s1, bounded);
            result = solver.EnumExistQuantify (s2, bounded);
            WriteLine(result.ToString());
        }

        private static void Write(string s)
        {
            Console.Write(s);
            DebugStub.Print(s);
        }
        private static void WriteLine(string s)
        {
            Console.WriteLine(s);
            DebugStub.WriteLine(s);
        }

        public static void Main(string [] args)
        {
//          bool r = UnitTest();
//          sharp_assert (r == true);
//
//          NetList net = new NetList();
//          net.read_blif(args[0]);
//          net.write_blif(args[0] + ".out");

//          test_clause_solver(args);
//          return;
//            WriteLine("Test Clause and Structure Based Interpolant Generation");
//            for (int i=0; i< 100; ++i)
//            {
//                Write(String.Format("Test {0}\tCLAUSE: ", i));
//                r = test_interpolant_clauses (100, 200, 45, i) ;
//                if (r == false)
//                    Write("*");
//                Write("\t STURCT:");
//                r = test_interpolant_structure (100, 200, 45, i) ;
//                if (r == false)
//                    Write("*");
//                WriteLine("");
//            }
//            for (int i=0 ; i < 100; ++i)
//            {
//                WriteLine("Test {0} ", i);
//                test_existential_quantification(50, 30, 20, i);
//            }
//            test_small_model();
//            test_quantification_edge_case();
            test_clause_solver (args);
        }
    }
}
