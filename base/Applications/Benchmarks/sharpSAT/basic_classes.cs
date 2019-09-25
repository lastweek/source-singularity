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
    public class Variable : SATCommon
    {

        //public bool       branchable  = true;
        //public bool       reasoning   = true;
        private ushort  flags       = 0;
        public ushort   gflag       = 0;

        public NodeType type        = NodeType.UNKNOWN;
        public IntVector outputs    = new IntVector(2);
        public int      left        = INVALID;
        public int      right       = INVALID;
        public int      canonical   = INVALID;
        public int      ref_count   = 0;
        public short    lits_count_0= 0;
        public short    lits_count_1= 0;
        public int      uid         = 0;

        public short    score_0     = 0;
        public short    score_1     = 0;
        public int      asgn_pos    = -1;
        public int      ordered_pos = 0;

        public short    varValue    = UNKNOWN;
        public Antecedent antecedent= -1;
        public int      dlevel      = -1;

        public void set_gid (int i)     { gflag |= (ushort) (1<<(i-1));     }
        public void clear_gid(int i)    { gflag &= (ushort) ~(1<<(i-1));   }
        public void clear_all_gid()     { gflag = 0; }
        public bool gid (int i)         { return (( gflag & (ushort) (1<<(i-1))) != 0);   }

        public void clear_all_flag()    { flags = 0; }
        public void set_flag(int idx)   { flags |= (ushort) (1 << idx); }
        public void clear_flag(int idx) { flags &= (ushort) (~(1<<idx));}
        public bool flag(int idx)       { return (flags & (ushort) (1<< idx)) != 0; }

        public int score()              { return (score_0 > score_1? score_0 : score_1); }
        public int lits_count()         { return lits_count_0 + lits_count_1; }
        public bool is_pi()             { return type == NodeType.PI; }
        public bool is_gate()           { return (type == NodeType.AND || type == NodeType.XOR); }
        public int output(int i)        { return outputs[i];}
        public int input(int k)         { return (k==0 ? left: right); }
    }


    public class Clause : SATCommon
    {
        public ClType   type            = ClType.UNKNOWN;       //indicates the clause type
        public ushort   gflag           = 0;
        public int      uid             = 0;
        public int[]    literals        = null;
        public int      activity        = 0;

        public void init (ClType tp, int [] lits, ushort gflg, int id)
        {
            type = tp;
            literals = new int[lits.Length];
            Array.Copy(lits, 0, literals, 0, lits.Length);
            gflag = gflg;
            uid = id;
            activity = 0;
        }

        public bool gid (int i)
        {
            sharp_assert (i>=1 && i<= WORD_WIDTH);
            return (( gflag & (ushort)(1<<(i-1))) != 0);
        }

        public void set_gid (int i)
        {
            sharp_assert (i>=1 && i<= WORD_WIDTH);
            gflag |= (ushort)(1<<(i-1));
        }

        public void clear_gid(int i)
        {
            sharp_assert (i>=1 && i<= WORD_WIDTH);
            gflag &= (ushort)~(1<<(i-1));
        }

        public int num_lits {   get {return literals.Length; }  }

        public int literal (int n)
        {
            return literals[n];
        }
    }

    public struct Antecedent
    {
        private int anteVal;

        public static implicit operator Antecedent( int v )     { return new Antecedent(v); }
        public static implicit operator int (Antecedent an) { return an.anteVal; }
        public Antecedent (int v) { anteVal = v; }
        public Antecedent (ImpType tp, int index)
        {
            anteVal = (index << 3) + (int) tp;
        }
        public ImpType type
        {
            get { return (ImpType) (anteVal & 0x7); }
            set
            {
                uint a = (uint) anteVal & (~(uint) 0x7);
                uint b = (uint) value;
                anteVal =  (int) (a | b);
                //anteVal = (((uint)anteVal) & (~(uint)0x7)) | (uint) value;
            }
        }

        public int index
        {
            get { return (anteVal >> 3); }
            set { anteVal = ((anteVal & 7) | (value << 3)); }
        }
    }

    public struct Implication
    {
        public int lit;
        public Antecedent ante;
    }

    public class NodeHashMap  : SATCommon
    {
        private const int XOR_MARK = (1 << 30);
        private MyHashtable     hash_table = new MyHashtable();

        private class NodeHashMapKey
        {
            public int left;
            public int right;
            public NodeHashMapKey(int l, int r)
            {
                left = l;
                right = r;
            }
            public override int GetHashCode()
            {
                long hashcode = left;
                hashcode <<= 16;
                hashcode ^= right;
                int lsig = (int)(hashcode & 0xffffffff);
                int msig = (int)(hashcode >> 32);
                return lsig ^ msig;
            }
            public override bool Equals(object obj)
            {
                NodeHashMapKey other = obj as NodeHashMapKey;
                if (other == null) return false;
                return other.left == left && other.right == right;
            }
        }

        public int lookup (NodeType op, int i1, int i2)
        {
            sharp_assert (op == NodeType.AND || op == NodeType.XOR);
            //1. left input always has smaller index than right
            if (i1 > i2) {
                int temp = i1;
                i1 = i2;
                i2 = temp;
            }
            //2. For XOR gate, always require both inputs not negated
            bool do_NEGATE = false;
            if (op == NodeType.XOR) {
                if (IS_NEGATED(i1)) {
                    i1 = NEGATE (i1);
                    do_NEGATE = !do_NEGATE;
                }
                if (IS_NEGATED(i2)) {
                    i2 = NEGATE(i2);
                    do_NEGATE = !do_NEGATE;
                }
            }
            //3. put special mark on the XOR node
            int l, r;
            l = i1;
            r = i2;
            if (op == NodeType.XOR)
                l += XOR_MARK;
            //4. Lookup
            NodeHashMapKey key = new NodeHashMapKey(l, r);
//          ulong key = ((ulong)l << 32) + (ulong) r;
            object item = hash_table[key];
            if (item == null)
                return INVALID;
            int o = (int) item;
            if (do_NEGATE)
                o = NEGATE(o);
            return o;
        }

        public void insert ( int n, NodeType op, int i1, int i2)
        {
            sharp_assert (op == NodeType.AND || op == NodeType.XOR);
            sharp_assert (i1 < i2);
            sharp_assert (! (   (op == NodeType.XOR) &&
                ( IS_NEGATED(i1) || IS_NEGATED(i2) )));
            sharp_assert (!IS_NEGATED(n));

            int l, r;
            l = i1;
            r = i2;
            if (op == NodeType.XOR)
                l += XOR_MARK;
            NodeHashMapKey key = new NodeHashMapKey(l, r);
//          ulong key = ((ulong)l << 32) + (ulong) r;
            sharp_assert ( !hash_table.Contains(key));
            hash_table[key] = n;
        }

        public void remove ( int n, NodeType op, int i1, int i2)
        {
            sharp_assert (op == NodeType.AND || op == NodeType.XOR);
            sharp_assert (i1 < i2);
            sharp_assert (! (   (op == NodeType.XOR) &&
                ( IS_NEGATED(i1) ||  IS_NEGATED(i2) )));
            sharp_assert ( ! IS_NEGATED(n) );
            //put special mark on the XOR node
            int l, r;
            l = i1;
            r = i2;
            if (op == NodeType.XOR)
                l += XOR_MARK;
            NodeHashMapKey key = new NodeHashMapKey(l, r);
//          ulong key = ((ulong)l << 32) + (ulong) r;

            sharp_assert ( (int)hash_table[key] == n);
            hash_table.Remove(key);
        }
    }


    class FreeList
    {
        VarVector variables;
        IntVector free_list;
        int delete_count;
        const double compact_ratio = 0.5;

        public FreeList (VarVector vars)
        {
            free_list = new IntVector(16);
            variables = vars;
        }

        public void add (IntVector new_frees)
        {
            for (int i = 0; i < new_frees.size(); ++i)
                free_list.push_back(new_frees[i]);
            free_list.sort();
        }

        public void delete_index (int idx)
        {
            delete_count ++;
            if ((double)delete_count / (double)free_list.size() > compact_ratio) {
                IntVector temp = new IntVector(16);
                for (int i = 0; i < free_list.size(); ++i) {
                    if (idx == i) //just deleted, so won't be in free_list anymore
                        continue;
                    if (variables[free_list[i]] == null ||
                        variables[free_list[i]].type == NodeType.FREE )
                        temp.push_back(free_list[i]);
                }
                free_list = temp;
            }
        }
        public int find_greater_than (int v)
        {
            int idx = free_list.binary_search (v);
            if (idx < 0)
                idx = ~ idx;
            else
                idx ++;
            for (int i = idx; i < free_list.size(); ++i) {
                if (variables[free_list[i]] == null ||
                    variables[free_list[i]].type == NodeType.FREE )
                {
                    int r = free_list[i];
                    delete_index(i);
                    return r;
                }
            }
            return -1;
        }
    }

    public class UnsatCore
    {
        public int [] core_clauses;
        public int [] core_nodes;
    }

    public class MyHashtable : Hashtable {}

    public interface SATHook
    {
        void OnBCP();
        void OnBacktrack(int blevel);
        void OnCaseSplit(int svar);
    }
}
