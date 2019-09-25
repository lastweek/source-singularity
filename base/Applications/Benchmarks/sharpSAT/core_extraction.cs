// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
using System.Collections;
using System.Diagnostics;
//using Microsoft.Zap;
namespace SharpSAT
{
    sealed class ResolveNode : SATCommon
    {
        public int  uid;
        public int [] reasons;

        public ResolveNode () {}
        public ResolveNode (int r, int [] antes)
        {
            uid = r;
            reasons = antes;
        }

        public int footprint()
        {
            return (3 + reasons.Length) * 4;
        }

        public void Serialize (Stream stream)
        {
            stream.Seek (0, SeekOrigin.End);
            BinaryWriter bw = new BinaryWriter ( stream );
            bw.Write (uid);
            bw.Write (reasons.Length);
            for (int i = 0; i < reasons.Length; ++i)
                bw.Write (reasons[i]);
            bw.Write ( - reasons.Length);
            bw.Flush();
        }

        static public ResolveNode DeSerializeForward (Stream stream)
        {
            BinaryReader br = new BinaryReader ( stream );
            ResolveNode r = new ResolveNode();
            r.uid = br.ReadInt32();
            int len = br.ReadInt32();
            r.reasons = new int [len];
            for (int i = 0; i < r.reasons.Length; ++i)
                r.reasons[i] = br.ReadInt32();
            int mlen = br.ReadInt32();
            sharp_assert (mlen == - len);
            return r;
        }

        static public ResolveNode DeSerializeBackward (Stream stream)
        {
            BinaryReader br = new BinaryReader ( stream );
            ResolveNode r = new ResolveNode();
            stream.Seek( -4, SeekOrigin.Current );
            int l = br.ReadInt32();
            sharp_assert (l < 0);
            stream.Seek( - (-l + 3) * 4, SeekOrigin.Current );

            r.uid = br.ReadInt32();
            int len = br.ReadInt32();
            r.reasons = new int [len];
            for (int i = 0; i < r.reasons.Length; ++i)
                r.reasons[i] = br.ReadInt32();
            int mlen = br.ReadInt32();
            sharp_assert (mlen == - len);
            stream.Seek( - (-l + 3) * 4, SeekOrigin.Current );
            return r;
        }
    }

    class ResolutionTrace : SATCommon
    {
        const int A_LOCAL = 1;
        const int B_LOCAL = 2;
        const int GLOBAL = (A_LOCAL | B_LOCAL);

        private SharpSATSolver  solver      = null;
        private bool            enable      = false;
        private int             cache_limit = 1024 * 1024 * 4; // 4 meg
        private ResolveNode     empty       = null;
        private Stream          storage     = new MemoryStream();
        private string          filename    = "resolution.trace";
        private IntVector       reasons     = new IntVector(4);

        public ResolutionTrace (SharpSATSolver s )
        {
            solver = s;
        }
        public void enable_trace (bool e)
        {
            enable = e;
        }

        public void reset()
        {
            empty       = null;
            if (storage != null)
                storage.Close();
            storage     = new MemoryStream();
            reasons     = new IntVector(4);
        }

        public void set_cache_limit (int sz)
        {
            cache_limit = sz;
        }
        public void set_temp_file (string fname)
        {
            filename = fname;
        }
        public void add_reason (int uid)
        {
            reasons.push_back(uid);
        }
        public void set_resolvent (int uid)
        {
            if (enable) {
                ResolveNode nd = new ResolveNode (uid, reasons.ToArray());

                if (storage is MemoryStream &&
                    storage.Length + nd.footprint() > cache_limit) //out of cache, so use file
                {
                    Stream newstream = new FileStream (filename, FileMode.Create);
                    MemoryStream memstream = storage as MemoryStream;
                    byte [] buffer = memstream.ToArray();
                    newstream.Write (buffer, 0, buffer.Length);
                    storage = newstream;
                }
                nd.Serialize(storage);
            }
            reasons.clear();
        }
        public void set_empty_resolvents()
        {
            empty = new ResolveNode(-1, reasons.ToArray());
        }

        Clause clause(int cl_id) {
            return solver.clause(cl_id);
        }

        public void dump_trace (string fname)
        {
            StreamWriter output = new StreamWriter (fname, false);
            long oldpos = storage.Position;
            storage.Seek(0, SeekOrigin.Begin);
            while (storage.Position < storage.Length) {
                ResolveNode nd = ResolveNode.DeSerializeForward (storage);
                output.Write ("{0} <== ", nd.uid);
                foreach (int r in nd.reasons) {
                    if (is_node(r))
                        output.Write(" {0}({1)}", node_uid(r), cls_idx(r));
                    else
                        output.Write (" {0}", r);
                }
                output.Write("\n");
            }
            output.Close();
            storage.Seek (oldpos, SeekOrigin.Begin);
        }

        public MyHashtable generate_unsat_core()
        {
            if (empty == null)
                fatal ("Not UNSAT, Cannot Generate Core");

            MyHashtable hash = new MyHashtable();
            foreach (int uid in empty.reasons)
                hash.Add (uid, null);

            long oldpos = storage.Position;
            storage.Seek(0, SeekOrigin.End);
            while (storage.Position > 0) {
                ResolveNode nd = ResolveNode.DeSerializeBackward (storage);
                sharp_assert (!is_node(nd.uid));
                if (hash.Contains (nd.uid)) {
                    foreach (int id in nd.reasons) {
                        int uid = id;
                        if (is_node(id))
                            uid = node_uid(id);
                        if (!hash.Contains(uid))
                            hash.Add (uid, null);
                    }
                    hash.Remove (nd.uid);
                }
            }
            storage.Seek (oldpos, SeekOrigin.Begin);
            return hash;
        }

        int find_pivot (int [] cl1, int [] cl2)
        {
            int [] combined = new int [ cl1.Length + cl2.Length ];
            Array.Copy (cl1, 0, combined, 0, cl1.Length);
            Array.Copy (cl2, 0, combined, cl1.Length, cl2.Length);
            Array.Sort (combined);
            for (int i = 1; i < combined.Length; ++ i)
                if (combined[i] == (combined[i-1]^1))
                    return VID(combined[i]);
            fatal ("No pivot variable? ");
            return 0;
        }

        int [] resolve (int [] cl1, int [] cl2)
        {
            IntVector result = new IntVector(4);
            int [] combined = new int [ cl1.Length + cl2.Length ];
            Array.Copy (cl1, 0, combined, 0, cl1.Length);
            Array.Copy (cl2, 0, combined, cl1.Length, cl2.Length);
            Array.Sort (combined);

            for (int i = 0; i < combined.Length; ++ i) {
                if (result.empty())
                    result.push_back (combined[i]);
                else if (result.back == combined[i])
                    continue;
                else if (result.back == (combined[i] ^ 1))
                    result.pop_back();
                else
                    result.push_back (combined[i]);
            }
            return result.ToArray();
        }

        int distance (int [] cl1, int [] cl2)
        {
            int [] combined = new int [ cl1.Length + cl2.Length ];
            Array.Copy (cl1, 0, combined, 0, cl1.Length);
            Array.Copy (cl2, 0, combined, cl1.Length, cl2.Length);
            Array.Sort (combined);
            int distance = 0;
            for (int i = 1; i < combined.Length; ++ i) {
                if (combined[i] == (combined[i - 1] ^ 1)) {
                    distance ++;
                    i++;
                }
            }
            return distance;
        }

        int [][] gen_gate_clause (int vid)
        {
            Variable var = solver.variable(vid);
            int a = var.input(0);
            int b = var.input(1);
            int o = vid + vid;
            sharp_assert (a != INVALID && b != INVALID);
            int [][] result;
            if (var.type == NodeType.AND) {
                result = new int [3][];
                result[0] = new int [] { a, NEGATE(o)};
                result[1] = new int [] { b, NEGATE(o)};
                result[2] = new int [] { NEGATE(a), NEGATE(b), o};
            }
            else {
                sharp_assert (var.type == NodeType.XOR);
                result = new int [4][];
                result[0] = new int [] { NEGATE(a), b, o};
                result[1] = new int [] { a, NEGATE(b), o};
                result[2] = new int [] { a, b, NEGATE(o)};
                result[3] = new int [] { NEGATE(a), NEGATE(b), NEGATE(o)};
            }
            return result;
        }

        MyHashtable find_all_involved()
        {
            if (empty == null)
                fatal ("Not UNSAT, Cannot Generate Core");

            MyHashtable hash = new MyHashtable();
            foreach (int uid in empty.reasons)
                hash.Add (uid, 1);

            long oldpos = storage.Position;
            storage.Seek(0, SeekOrigin.End);
            while (storage.Position > 0) {
                ResolveNode nd = ResolveNode.DeSerializeBackward (storage);
                if (hash.Contains (nd.uid))
                    foreach (int uid in nd.reasons)
                    {
                        if (!hash.Contains(uid))
                            hash[uid] = 1;
                        else
                            hash[uid] = (int)hash[uid] + 1;
                    }
            }
            storage.Seek (oldpos, SeekOrigin.Begin);
            return hash;
        }

        void prepare_original_clauses (int a_gid, int b_gid, MyHashtable uid2lits, MyHashtable uid2sig, MyHashtable involved, int[] var_flag)
        {
            for (int i = 0; i < var_flag.Length; ++i)
                var_flag[i] = 0;
            for (int i = 0; i < solver.clauses.size(); ++i) {
                Clause cl = clause(i);
                if (cl == null || !involved.Contains(cl.uid))
                    continue;

                if (cl.type == ClType.ORIGINAL) {
                    if (cl.gid(a_gid)) {
                        sharp_assert (!cl.gid(b_gid));
                        foreach (int lit in cl.literals)
                            var_flag [VID(lit)] |= A_LOCAL;
                    }
                    else {
                        sharp_assert (cl.gid(b_gid));
                        foreach (int lit in cl.literals)
                            var_flag [VID(lit)] |= B_LOCAL;
                    }
                }
                uid2lits[cl.uid] = cl.literals;
            }

            for (int i = 0; i < solver.original_clauses.size(); ++i) {
                Clause cl = clause(solver.original_clauses[i]);
                sharp_assert (cl != null);
                sharp_assert (cl.type == ClType.ORIGINAL);

                if (!involved.Contains(cl.uid))
                    continue;

                int signal;
                if (cl.gid(a_gid)) {
                    sharp_assert (!cl.gid(b_gid));
                    signal = solver.zero();
                    foreach (int lit in cl.literals) {
                        if (var_flag[VID(lit)] == GLOBAL)
                            signal = solver.bor (signal, lit);
                    }
                }
                else {
                    sharp_assert (cl.gid(b_gid));
                    signal = solver.one();
                }
                uid2sig[cl.uid] = signal;
            }
        }

        public int gen_interpolant_from_clauses (int a_gid, int b_gid)
        {
            //solver.dump_file = new StreamWriter ("dump_file");
            //solver.dump_file.WriteLine ("{0} = INIT_VARS", solver.num_variables());

            sharp_assert (solver.is_pure_clause_based());
            solver.convert_vars_to_pi();

            MyHashtable uid2lits    = new MyHashtable();
            MyHashtable uid2sig = new MyHashtable();
            MyHashtable involved    = find_all_involved();
            int [] var_flag = new int [ solver.variables.size() ];
            prepare_original_clauses ( a_gid, b_gid, uid2lits, uid2sig, involved, var_flag);

            long oldpos = storage.Position;
            storage.Seek(0, SeekOrigin.Begin);
            while (storage.Position < storage.Length) {
                ResolveNode nd = ResolveNode.DeSerializeForward (storage);
                if (!involved.Contains (nd.uid))
                    continue;

                int uid = nd.reasons[0];
                sharp_assert (involved.Contains(uid));
                sharp_assert (uid2lits.Contains(uid));
                sharp_assert (uid2sig.Contains(uid));
                int [] lits = (int[])uid2lits[uid];
                int signal = (int)uid2sig[uid];

                int count = (int)involved[uid] - 1 ;
                if (count == 0) {
                    uid2lits.Remove(uid);
                    uid2sig.Remove(uid);
                    involved.Remove(uid);
                }
                else
                    involved[uid] = count;

                for (int i = 1; i < nd.reasons.Length; ++i) {
                    uid = nd.reasons[i];
                    sharp_assert (uid < (1 << 29));
                    sharp_assert (involved.Contains(uid));
                    sharp_assert (uid2lits.Contains(uid));
                    sharp_assert (uid2sig.Contains(uid));
                    int [] lits1 = (int[]) uid2lits[uid];
                    int signal1 = (int)uid2sig[uid];

                    count = (int)involved[uid] - 1 ;
                    if (count == 0) {
                        uid2lits.Remove(uid);
                        uid2sig.Remove(uid);
                        involved.Remove(uid);
                    }
                    else
                        involved[uid] = count;

                    int pivot = find_pivot (lits, lits1);
                    lits = resolve(lits, lits1);
                    if (var_flag[pivot] == A_LOCAL)
                        signal = solver.bor (signal, signal1);
                    else
                        signal = solver.band (signal, signal1);
                }
                if (!uid2lits.Contains(nd.uid))
                    uid2lits[nd.uid] = lits;
                sharp_assert (!uid2sig.Contains(nd.uid));
                uid2sig[nd.uid] = signal;

            }
            storage.Seek (oldpos, SeekOrigin.Begin);
        {
            int uid = empty.reasons[0];
            sharp_assert (involved.Contains(uid));
            sharp_assert (uid2lits.Contains(uid));
            sharp_assert (uid2sig.Contains(uid));
            int [] lits = (int[])uid2lits[uid];
            int signal = (int)uid2sig[uid];

            int count = (int)involved[uid] - 1 ;
            if (count == 0) {
                uid2lits.Remove(uid);
                uid2sig.Remove(uid);
                involved.Remove(uid);
            }
            else
                involved[uid] = count;

            for (int i = 1; i < empty.reasons.Length; ++i) {
                uid = empty.reasons[i];
                sharp_assert (involved.Contains(uid));
                sharp_assert (uid2lits.Contains(uid));
                sharp_assert (uid2sig.Contains(uid));
                int [] lits1 = (int[]) uid2lits[uid];
                int signal1 = (int)uid2sig[uid];

                count = (int)involved[uid] - 1 ;
                if (count == 0) {
                    uid2lits.Remove(uid);
                    uid2sig.Remove(uid);
                    involved.Remove(uid);
                }
                else
                    involved[uid] = count;

                int pivot = find_pivot (lits, lits1);
                lits = resolve(lits, lits1);
                if (var_flag[pivot] == A_LOCAL)
                    signal = solver.bor (signal, signal1);
                else
                    signal = solver.band (signal, signal1);
            }
            sharp_assert (lits.Length == 0);
            sharp_assert (involved.Count == 0);
            sharp_assert (uid2lits.Count == 0);
            sharp_assert (uid2sig.Count == 0);
            //solver.dump_file.WriteLine ("{0} = CONSTRAINT", signal);
            //solver.dump_file.Close();
            return signal;
        }
        }

        bool is_node (int uid)
        {
            return (uid > (1<<UIDSHIFT));
        }
        int node_uid (int uid)
        {
            sharp_assert (is_node(uid));
            return (~(3 << UIDSHIFT)) & uid;
        }
        int cls_idx(int uid)
        {
            sharp_assert (is_node(uid));
            return uid >> UIDSHIFT;
        }

        int not (int s) { return s ^ 1; }

        // for AND
        //1: (a + c')
        //2: (b + c')
        //3: (a' + b' + c)
        //for XOR
        //4: (a' + b + c)
        //5: (a + b' + c)
        //6: (a + b + c')
        //7: (a' + b' + c')
        //

        int [] get_cls (int vid, int cl_idx)
        {
            int [] result;
            sharp_assert (solver.is_gate(vid + vid));
            int a = solver.variable(vid).input(0);
            int b = solver.variable(vid).input(1);
            int c = vid + vid;
            switch (cl_idx) {
                case 1:
                    result = new int[]{a, not(c)};
                    break;
                case 2:
                    result = new int[]{b, not(c)};
                    break;
                case 3:
                    result = new int[]{not(a), not(b), c};
                    break;
                case 4:
                    result = new int[]{not(a), b, c};
                    break;
                case 5:
                    result = new int[]{a, not(b), c};
                    break;
                case 6:
                    result = new int[]{a, b, not(c)};
                    break;
                case 7:
                    result = new int[]{not(a), not(b), not(c)};
                    break;
                default:
                    sharp_assert (false);
                    result = null;
                    break;
            }
            return result;
        }

        void prepare_original_nodes (int a_flag, int b_flag, MyHashtable uid2lits, MyHashtable uid2sig, MyHashtable involved)
        {
            MyHashtable uid2vid = new MyHashtable();

            for (int i = 1; i < solver.variables.size(); ++i) {
                Variable var = solver.variable(i);
                if (var != null && (var.flag(a_flag) || var.flag(b_flag)))
                    uid2vid[var.uid] = i;
            }

            foreach (object obj in involved) {
                int uid = (int)((DictionaryEntry) obj).Key;
                if (!is_node(uid) || !uid2vid.Contains(node_uid(uid)))
                    continue;
                int nid = node_uid (uid);
                int cls_id = cls_idx (uid);
                int vid = (int) uid2vid[nid];
                int [] lits = get_cls(vid, cls_id);
                int sig;
                sharp_assert (solver.variable(vid).flag(a_flag) || solver.variable(vid).flag(b_flag));
                if (solver.variable(vid).flag(b_flag))
                    sig = solver.one();
                else {
                    sig = solver.zero();
                    foreach (int lit in lits) {
                        sharp_assert (solver.node(lit).flag(a_flag));
                        if (solver.node(lit).flag(b_flag))
                            sig = solver.bor(sig, lit);
                    }
                }
                uid2lits[uid] = lits;
                uid2sig[uid] = sig;
            }
        }

        public int gen_interpolant_from_signals (int a_node, int a_cls_id, int b_node, int b_cls_id)
        {
            //solver.dump_file = new StreamWriter ("dump_file");
            //solver.dump_file.WriteLine ("{0} = INIT_VARS", solver.num_variables());

            int a_flag = solver.alloc_flag();
            int b_flag = solver.alloc_flag();
            solver.mark_transitive_fanins(a_node, a_flag);
            solver.mark_transitive_fanins(b_node, b_flag);

            MyHashtable uid2lits    = new MyHashtable();
            MyHashtable uid2sig = new MyHashtable();
            MyHashtable involved    = find_all_involved();
            prepare_original_nodes (a_flag, b_flag, uid2lits, uid2sig, involved);
            uid2lits[solver.clause(a_cls_id).uid] = solver.clause(a_cls_id).literals;
            uid2lits[solver.clause(b_cls_id).uid] = solver.clause(b_cls_id).literals;
            if (solver.node(a_node).flag(b_flag))
                uid2sig[solver.clause(a_cls_id).uid] = a_node;
            else
                uid2sig[solver.clause(a_cls_id).uid] = solver.zero();
            uid2sig[solver.clause(b_cls_id).uid] = solver.one();

            long oldpos = storage.Position;
            storage.Seek(0, SeekOrigin.Begin);
            while (storage.Position < storage.Length) {
                ResolveNode nd = ResolveNode.DeSerializeForward (storage);
                if (!involved.Contains (nd.uid))
                    continue;

                int [] lits;
                int signal;
                int uid = nd.reasons[0];
                sharp_assert (involved.Contains(uid));
                sharp_assert (uid2sig.Contains(uid));
                lits = (int[])uid2lits[uid];
                signal = (int)uid2sig[uid];

                int count = (int)involved[uid] - 1 ;
                if (count == 0) {
                    uid2lits.Remove(uid);
                    uid2sig.Remove(uid);
                    involved.Remove(uid);
                }
                else
                    involved[uid] = count;

                for (int i = 1; i < nd.reasons.Length; ++i) {
                    uid = nd.reasons[i];
                    sharp_assert (uid < (1 << 29));
                    sharp_assert (involved.Contains(uid));
                    sharp_assert (uid2lits.Contains(uid));
                    sharp_assert (uid2sig.Contains(uid));
                    int [] lits1 = (int[]) uid2lits[uid];
                    int signal1 = (int)uid2sig[uid];

                    count = (int)involved[uid] - 1 ;
                    if (count == 0) {
                        uid2lits.Remove(uid);
                        uid2sig.Remove(uid);
                        involved.Remove(uid);
                    }
                    else
                        involved[uid] = count;

                    int pivot = find_pivot (lits, lits1);
                    lits = resolve(lits, lits1);
                    if (!solver.variable(pivot).flag(b_flag)) {
                        sharp_assert (solver.variable(pivot).flag(a_flag));
                        signal = solver.bor (signal, signal1);
                    }
                    else
                        signal = solver.band (signal, signal1);
                }
                if (!uid2lits.Contains(nd.uid))
                    uid2lits[nd.uid] = lits;
                sharp_assert (!uid2sig.Contains(nd.uid));
                uid2sig[nd.uid] = signal;
            }
            storage.Seek (oldpos, SeekOrigin.Begin);
        {
            int uid = empty.reasons[0];
            sharp_assert (involved.Contains(uid));
            sharp_assert (uid2lits.Contains(uid));
            sharp_assert (uid2sig.Contains(uid));
            int [] lits = (int[])uid2lits[uid];
            int signal = (int)uid2sig[uid];

            int count = (int)involved[uid] - 1 ;
            if (count == 0) {
                uid2lits.Remove(uid);
                uid2sig.Remove(uid);
                involved.Remove(uid);
            }
            else
                involved[uid] = count;

            for (int i = 1; i < empty.reasons.Length; ++i) {
                uid = empty.reasons[i];
                sharp_assert (involved.Contains(uid));
                sharp_assert (uid2lits.Contains(uid));
                sharp_assert (uid2sig.Contains(uid));
                int [] lits1 = (int[]) uid2lits[uid];
                int signal1 = (int)uid2sig[uid];

                count = (int)involved[uid] - 1 ;
                if (count == 0) {
                    uid2lits.Remove(uid);
                    uid2sig.Remove(uid);
                    involved.Remove(uid);
                }
                else
                    involved[uid] = count;

                int pivot = find_pivot (lits, lits1);
                lits = resolve(lits, lits1);
                if (!solver.variable(pivot).flag(b_flag)) {
                    sharp_assert (solver.variable(pivot).flag(a_flag));
                    signal = solver.bor (signal, signal1);
                }
                else
                    signal = solver.band (signal, signal1);
            }
            sharp_assert (lits.Length == 0);
            sharp_assert (involved.Count == 0);
            sharp_assert (uid2lits.Count == 0);
            sharp_assert (uid2sig.Count == 0);
            //solver.dump_file.WriteLine ("{0} = CONSTRAINT", signal);
            //solver.dump_file.Close();

            solver.free_flag(a_flag);
            solver.free_flag(b_flag);
            return signal;
        }
        }
        // gretay -- change start
        public int gen_interpolant_from_signals_ex (int a_node, int a_cls_id, int b_node, int b_cls_id, int[] c_cls_id, int[] c_interp)
        {
            //solver.dump_file = new StreamWriter ("dump_file");
            //solver.dump_file.WriteLine ("{0} = INIT_VARS", solver.num_variables());

            int a_flag = solver.alloc_flag();
            int b_flag = solver.alloc_flag();
            solver.mark_transitive_fanins(a_node, a_flag);
            solver.mark_transitive_fanins(b_node, b_flag);

            assert(c_cls_id.Length == c_interp.Length);

            MyHashtable uid2lits    = new MyHashtable();
            MyHashtable uid2sig = new MyHashtable();
            MyHashtable involved    = find_all_involved();
            prepare_original_nodes (a_flag, b_flag, uid2lits, uid2sig, involved);

            // init A info
            int a_uid = solver.clause(a_cls_id).uid;
            if (involved.Contains(a_uid)) {
                uid2lits[a_uid] = solver.clause(a_cls_id).literals;
                int s = solver.zero();
                foreach (int lit in solver.clause(a_cls_id).literals) {
                    sharp_assert (solver.node(lit).flag(a_flag));
                    if (solver.node(lit).flag(b_flag))
                        s = solver.bor(s, lit);
                }
                uid2sig[a_uid] = s;
                //uid2sig[a_uid] = a_node;
            }
            // init B info
            int b_uid = solver.clause(b_cls_id).uid;
            if (involved.Contains(b_uid)) {
                uid2lits[b_uid] = solver.clause(b_cls_id).literals;
                uid2sig[b_uid] = solver.one();
            }
            // init C info
            for (int i = 0; i < c_cls_id.Length; i++) {
                Clause cl = solver.clause(c_cls_id[i]);
                if (involved.Contains(cl.uid)) {
                    uid2lits[cl.uid] = cl.literals;
                    uid2sig[cl.uid] = c_interp[i];
                }
            }

            long oldpos = storage.Position;
            storage.Seek(0, SeekOrigin.Begin);
            while (storage.Position < storage.Length) {
                ResolveNode nd = ResolveNode.DeSerializeForward (storage);
                if (!involved.Contains (nd.uid))
                    continue;

                int [] lits;
                int signal;
                int uid = nd.reasons[0];
                sharp_assert (involved.Contains(uid));
                sharp_assert (uid2sig.Contains(uid));
                lits = (int[])uid2lits[uid];
                signal = (int)uid2sig[uid];

                int count = (int)involved[uid] - 1 ;
                if (count == 0) {
                    uid2lits.Remove(uid);
                    uid2sig.Remove(uid);
                    involved.Remove(uid);
                }
                else
                    involved[uid] = count;

                for (int i = 1; i < nd.reasons.Length; ++i) {
                    uid = nd.reasons[i];
                    sharp_assert (uid < (1 << 29));
                    sharp_assert (involved.Contains(uid));
                    sharp_assert (uid2lits.Contains(uid));
                    sharp_assert (uid2sig.Contains(uid));
                    int [] lits1 = (int[]) uid2lits[uid];
                    int signal1 = (int)uid2sig[uid];

                    count = (int)involved[uid] - 1 ;
                    if (count == 0) {
                        uid2lits.Remove(uid);
                        uid2sig.Remove(uid);
                        involved.Remove(uid);
                    }
                    else
                        involved[uid] = count;

                    int pivot = find_pivot (lits, lits1);
                    lits = resolve(lits, lits1);
                    if ((solver.variable(pivot).flag(a_flag))
                        && (!solver.variable(pivot).flag(b_flag)))
                    {
                        signal = solver.bor (signal, signal1);
                    }
                    else {
                        signal = solver.band (signal, signal1);
                    }
                }
                if (!uid2lits.Contains(nd.uid))
                    uid2lits[nd.uid] = lits;
                sharp_assert (!uid2sig.Contains(nd.uid));
                uid2sig[nd.uid] = signal;

            }
            storage.Seek (oldpos, SeekOrigin.Begin);
        {
            int uid = empty.reasons[0];
            sharp_assert (involved.Contains(uid));
            sharp_assert (uid2lits.Contains(uid));
            sharp_assert (uid2sig.Contains(uid));
            int [] lits = (int[])uid2lits[uid];
            int signal = (int)uid2sig[uid];

            int count = (int)involved[uid] - 1 ;
            if (count == 0) {
                uid2lits.Remove(uid);
                uid2sig.Remove(uid);
                involved.Remove(uid);
            }
            else
                involved[uid] = count;

            for (int i = 1; i < empty.reasons.Length; ++i) {
                uid = empty.reasons[i];
                sharp_assert (involved.Contains(uid));
                sharp_assert (uid2lits.Contains(uid));
                sharp_assert (uid2sig.Contains(uid));
                int [] lits1 = (int[]) uid2lits[uid];
                int signal1 = (int)uid2sig[uid];

                count = (int)involved[uid] - 1 ;
                if (count == 0) {
                    uid2lits.Remove(uid);
                    uid2sig.Remove(uid);
                    involved.Remove(uid);
                }
                else
                    involved[uid] = count;

                int pivot = find_pivot (lits, lits1);
                lits = resolve(lits, lits1);

                if ((solver.variable(pivot).flag(a_flag))
                    && (!solver.variable(pivot).flag(b_flag)))
                {
                    signal = solver.bor (signal, signal1);
                }
                else {
                    signal = solver.band (signal, signal1);
                }
            }
            sharp_assert (lits.Length == 0);
            sharp_assert (involved.Count == 0);
            sharp_assert (uid2lits.Count == 0);
            sharp_assert (uid2sig.Count == 0);
            //solver.dump_file.WriteLine ("{0} = CONSTRAINT", signal);
            //solver.dump_file.Close();

            solver.free_flag(a_flag);
            solver.free_flag(b_flag);
            //solver.free_flag(c_flag);
            return signal;
        }
        }
        // gretay -- change end

    }
}
