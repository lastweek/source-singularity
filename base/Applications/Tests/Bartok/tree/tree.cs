//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//
// The tree implementation comes from Maurice Herlihy's SXM implementation.
//
// Use the command line to set the number of threads and operations, to
// optionally wrap each operation in an atomic or try_all block, and to require
// deterministic output for automated testing.

namespace Test
{

    using System.Threading;
    using System.Runtime.CompilerServices;
    using System;
    using Microsoft.Contracts;

    public enum RunKind { Direct, Atomic, TryAll };

    public class Config {

        // Create deterministic output for bvt
        public static bool DETERMINISTIC = false;

        // Kind of concurrent control to use
        public static RunKind KIND;

        // Number of threads to run
        public static int THREADS        = 1;

        // Number of successful operations per thread (-1 => loop forever)
        public static int OP_COUNT       = 10000; 

        // Range of key values, 0..KEY_SPACE_MASK
        public static int KEY_SPACE_MASK = 0xffff;

        // Workload mix, should sum to 0x100
        public static int LOOKUP_FRAC    = 0xc0;
        public static int REMOVE_FRAC    = 0x20;
        public static int INSERT_FRAC    = 0x20;
    }

    // RBTree benchmark originally from Maurice Herlihy's SXM.

    public class RBTree 
    {
        public enum Color {BLACK, RED};

        public static int INITIAL_SIZE = Config.KEY_SPACE_MASK / 2;
        
        protected RBNode root;
        //  sentinelNode is convenient way of indicating a leaf node.

        public static RBNode sentinelNode; 
        
        public int Shadow = 0;

        public int Actual() {
            return ActualFrom(root);
        }

        public int ActualFrom(RBNode r) {
            if (r == sentinelNode) { 
                return 0;
            }
            else {
                return r.Value + ActualFrom(r.Left) + ActualFrom(r.Right);
            }
        }

        ///<remark>
        /// Initializes the tree shared by all the threads.
        /// </remark>
        [NotDelayed]
        public RBTree() 
        {
            // set up the sentinel node. the sentinel node is the key to a successful
            // implementation and for understanding the red-black tree properties.
            sentinelNode        = new RBNode();
            sentinelNode.Left   = null;
            sentinelNode.Right  = null;
            sentinelNode.Parent = null;
            sentinelNode.Color  = Color.BLACK;
            root                = sentinelNode;
            this.root.Value = Int32.MinValue;
            this.root.Color = Color.BLACK;
            int size = 0;
            Object o = new Object();
            Random random = new Random(o.GetHashCode());
            while (size < INITIAL_SIZE) {
                    int n = random.Next();
                    //                    int v = (n >> 8) & 0xfff;
                    int v = (n >> 8) & Config.KEY_SPACE_MASK;
                    if ((bool)Insert(v)) {
                        size++;
                        Shadow += v;
                    }
                }
        }

        /// <remarks>
        /// Inserts an element into the integer set, if it is not already present.
        /// </remarks>
        public bool Insert(int key)
        {
            // traverse tree - find where node belongs
            RBNode temp	= root;
            RBNode parent = null;

            while (temp != sentinelNode) {
                    // find Parent
                    parent = temp;
                    if (key == temp.Value) {
                            return false;
                        } 
                    else if (key > temp.Value) {
                            temp = temp.Right;
                        } 
                    else {
                            temp = temp.Left;
                        }
                }
			
            // setup node
            RBNode node         =   new RBNode();
            node.Parent         =   parent;
            node.Value 	        =   key;
            node.Left           =   sentinelNode;
            node.Right          =   sentinelNode;

            // insert node into tree starting at parent's location
            if (node.Parent != null) {
                    if (node.Value > node.Parent.Value) {
                            node.Parent.Right = node;
                        }
                    else
                        node.Parent.Left = node;
                }
            else
                root = node;					// first node added

            RestoreAfterInsert(node);           // restore red-black properties
            return true;
        }
  
        /// <remarks>
        /// Tests whether item is present.
        /// </remarks>
        /// <returns> whether the item was present</returns>
        public bool Contains(int key)
        {
            RBNode node = root;     // begin at root
            bool result = false;
            
            // traverse tree until node is found
            while (node != sentinelNode) {
                    if (key == node.Value) {
                            result = true;
                            break;
                        } 
                    else if (key < node.Value) {
                            node = node.Left;
                        } 
                    else {
                            node = node.Right;
                        }
                }
            return result;
        }
  
        /// <remarks>
        /// Remove item if present.
        /// </remarks>
        /// <returns> whether the item was removed</returns>
        public bool Remove(int key)
        {
            // find node
            RBNode node;

            node = root;
            while (node != sentinelNode) {
                    if (key == node.Value) {
                            break;
                        } 
                    else if (key < node.Value) {
                            node = node.Left;
                        } 
                    else {
                            node = node.Right;
                        }
                }

            if (node == sentinelNode)
                return false;				// key not found

            Delete(node);
            return true;
        }

		
        /// <summary>
        /// Delete a node
        /// </summary>
        /// <param name="z">node to be deleted</param>
        private void Delete(RBNode z)
        {
            // A node to be deleted will be: 
            //		1. a leaf with no children
            //		2. have one child
            //		3. have two children
            // If the deleted node is red, the red black properties still hold.
            // If the deleted node is black, the tree needs rebalancing

            RBNode x;
            RBNode y;					// work node 

            // find the replacement node (the successor to x) - the node one with 
            // at *most* one child. 
            if (z.Left == sentinelNode || z.Right == sentinelNode) 
                y = z;						// node has sentinel as a child
            else {
                    // z has two children, find replacement node which will 
                    // be the leftmost node greater than z
                    y = z.Right;				        // traverse right subtree	
                    while (y.Left != sentinelNode) // to find next node in sequence
                        y = y.Left;
                }

            // at this point, y contains the replacement node. it's content will be copied 
            // to the values in the node to be deleted

            // x (y's only child) is the node that will be linked to y's old parent. 
            if (y.Left != sentinelNode)
                x = y.Left;					
            else
                x = y.Right;					

            // replace x's parent with y's parent and
            // link x to proper subtree in parent
            // this removes y from the chain
            x.Parent = y.Parent;
            if (y.Parent != null)
                if(y == y.Parent.Left)
                    y.Parent.Left = x;
                else
                    y.Parent.Right = x; // missing enlist for update
            else
                root = x;			// make x the root node

            // copy the values from y (the replacement node) to the node being deleted.
            // note: this effectively deletes the node. 
            if (y != z) {
                    z.Value	= y.Value;
                }

            if (y.Color == Color.BLACK)
                RestoreAfterDelete(x);
        }

        ///<summary>
        /// RestoreAfterDelete
        /// Deletions from red-black trees may destroy the red-black 
        /// properties. Examine the tree and restore. Rotations are normally 
        /// required to restore it
        ///</summary>
        private void RestoreAfterDelete(RBNode x)
        {
            // maintain Red-Black tree balance after deleting node 			

            RBNode y;

            while (x != root && x.Color == Color.BLACK) {
                    if (x == x.Parent.Left)	 // determine sub tree from parent
                        {
                            y = x.Parent.Right;			// y is x's sibling 
                            if (y.Color == Color.RED) {
                                    // x is black, y is red - make both black and rotate
                                    y.Color			= Color.BLACK;
                                    x.Parent.Color	= Color.RED;
                                    RotateLeft(x.Parent);
                                    y = x.Parent.Right;
                                }
                            if(y.Left.Color == Color.BLACK && 
                               y.Right.Color == Color.BLACK) 
                                {	// children are both black
                                    y.Color = Color.RED;		// change parent to red
                                    x = x.Parent;					// move up the tree
                                } 
                            else {
                                    if (y.Right.Color == Color.BLACK) {
                                            y.Left.Color	= Color.BLACK;
                                            y.Color			= Color.RED;
                                            RotateRight(y);
                                            y				= x.Parent.Right;
                                        }
                                    y.Color			= x.Parent.Color;
                                    x.Parent.Color	= Color.BLACK;
                                    y.Right.Color	= Color.BLACK;
                                    RotateLeft(x.Parent);
                                    x = root;
                                }
                        } 
                    else {
                            // right subtree - same as code above with right and left swapped
                            y = x.Parent.Left;
                            if (y.Color == Color.RED) {
                                    y.Color			= Color.BLACK;
                                    x.Parent.Color	= Color.RED;
                                    RotateRight (x.Parent);
                                    y = x.Parent.Left;
                                }
                            if(y.Right.Color == Color.BLACK && 
                               y.Left.Color == Color.BLACK) 
                                {
                                    y.Color = Color.RED;
                                    x		= x.Parent;
                                } 
                            else {
                                    if (y.Left.Color == Color.BLACK) {
                                            y.Right.Color	= Color.BLACK;
                                            y.Color			= Color.RED;
                                            RotateLeft(y);
                                            y				= x.Parent.Left;
                                        }
                                    y.Color			= x.Parent.Color;
                                    x.Parent.Color	= Color.BLACK;
                                    y.Left.Color	= Color.BLACK;
                                    RotateRight(x.Parent);
                                    x = root;
                                }
                        }
                }
            x.Color = Color.BLACK;
        }

        private void RestoreAfterInsert(RBNode x)
        {   
            RBNode y;

            // maintain red-black tree properties after adding x
            while (x != root && x.Parent.Color == Color.RED) {
                    // Parent node is .Colored red; 
                    if (x.Parent == x.Parent.Parent.Left)	// determine traversal path	 
                        {										// is it on the Left or Right subtree?
                            y = x.Parent.Parent.Right;			// get uncle
                            if (y != null && y.Color == Color.RED) {
                                    // uncle is red; change x's Parent and uncle to black
                                    x.Parent.Color			= Color.BLACK;
                                    y.Color					= Color.BLACK;
                                    // grandparent must be red. Why? Every red node that is not 
                                    // a leaf has only black children 
                                    x.Parent.Parent.Color	= Color.RED;	
                                    x						= x.Parent.Parent;	// continue loop with grandparent
                                }	
                            else {
                                    // uncle is black; determine if x is greater than Parent
                                    if (x == x.Parent.Right) {
                                            // yes, x is greater than Parent; rotate Left
                                            // make x a Left child
                                            x = x.Parent;
                                            RotateLeft(x);
                                        }
                                    // no, x is less than Parent
                                    x.Parent.Color			= Color.BLACK;	// make Parent black
                                    x.Parent.Parent.Color	= Color.RED;		// make grandparent black
                                    RotateRight(x.Parent.Parent);					// rotate right
                                }
                        }
                    else {
                            // x's Parent is on the Right subtree
                            // this code is the same as above with "Left" and "Right" swapped
                            y = x.Parent.Parent.Left;
                            if (y != null && y.Color == Color.RED) {
                                    x.Parent.Color			= Color.BLACK;
                                    y.Color					= Color.BLACK;
                                    x.Parent.Parent.Color	= Color.RED;
                                    x						= x.Parent.Parent;
                                }
                            else {
                                    if (x == x.Parent.Left) {
                                            x = x.Parent;
                                            RotateRight(x);
                                        }
                                    x.Parent.Color			= Color.BLACK;
                                    x.Parent.Parent.Color	= Color.RED;
                                    RotateLeft(x.Parent.Parent);
                                }
                        }																													
                }
            root.Color = Color.BLACK;		// root should always be black
        }

        ///<summary>
        /// RotateLeft
        /// Rebalance the tree by rotating the nodes to the left
        ///</summary>
        public void RotateLeft(RBNode x)
        {
            // pushing node x down and to the Left to balance the tree. x's Right child (y)
            // replaces x (since y > x), and y's Left child becomes x's Right child 
            // (since it's < y but > x).
            
            RBNode y = x.Right;			// get x's Right node, this becomes y

            // set x's Right link
            x.Right = y.Left;					// y's Left child's becomes x's Right child

            // modify parents
            if (y.Left != sentinelNode) 
                y.Left.Parent = x;				// sets y's Left Parent to x

            if (y != sentinelNode)
                y.Parent = x.Parent;			// set y's Parent to x's Parent

            if (x.Parent != null) {
                    // determine which side of it's Parent x was on
                    if (x == x.Parent.Left)	 
                        x.Parent.Left = y;			// set Left Parent to y
                    else
                        x.Parent.Right = y;			// set Right Parent to y
                } 
            else
                root = y;						// at root, set it to y

            // link x and y 
            y.Left = x;							// put x on y's Left 
            if (x != sentinelNode)				 // set y as x's Parent
                x.Parent = y;		
        }

        ///<summary>
        /// RotateRight
        /// Rebalance the tree by rotating the nodes to the right
        ///</summary>
        public void RotateRight(RBNode x)
        {
            // pushing node x down and to the Right to balance the tree. x's Left child (y)
            // replaces x (since x < y), and y's Right child becomes x's Left child 
            // (since it's < x but > y).
            
            RBNode y = x.Left;			// get x's Left node, this becomes y

            // set x's Right link
            x.Left = y.Right;					// y's Right child becomes x's Left child

            // modify parents
            if (y.Right != sentinelNode) 
                y.Right.Parent = x;				// sets y's Right Parent to x

            if (y != sentinelNode)
                y.Parent = x.Parent;			// set y's Parent to x's Parent

            if (x.Parent != null)		 // null = root, could also have used root
                {	// determine which side of its Parent x was on
                    if (x == x.Parent.Right)	 
                        x.Parent.Right = y;			// set Right Parent to y
                    else
                        x.Parent.Left = y;			// set Left Parent to y
                } 
            else
                root = y;						// at root, set it to y

            // link x and y 
            y.Right = x;						// put x on y's Right
            if (x != sentinelNode)		 // set y as x's Parent
                x.Parent = y;		
        }	

        private int CountBlackNodes(RBNode root) 
        {
            if (sentinelNode == root)
                return 0;
            int me = (root.Color == Color.BLACK) ? 1 : 0;
            RBNode left = (sentinelNode == root.Left)
                ? sentinelNode 
                : root.Left;
            return me + CountBlackNodes(left);
        }

        private int Count(RBNode root) 
        {
            if (root == sentinelNode)
                return 0;
            return 1 + Count(root.Left) + Count(root.Right);

        }

        private void RecursiveValidate(RBNode root, int blackNodes, int soFar) 
        {
            // Empty sub-tree is vacuously OK
            if (sentinelNode == root)
                return;

            Color rootcolor = root.Color;
            soFar += ((Color.BLACK == rootcolor) ? 1 : 0);
            root.Marked = true;

            // Check left side
            RBNode left = root.Left;
            if (sentinelNode != left) {
                    if (left.Color == Color.RED && rootcolor == Color.RED) {
                            Console.WriteLine("Two consecutive red nodes!");
                            return;
                        }
                    if (left.Value >= root.Value) {
                            Console.WriteLine("Tree values out of order!");
                            return;
                        }
                    if (left.Marked) {
                            Console.WriteLine("Cycle in tree structure!");
                            return;
                        }
                    RecursiveValidate(left, blackNodes, soFar);
                }

            // Check right side
            RBNode right = root.Right;
            if (sentinelNode != right) {
                    if (right.Color == Color.RED && rootcolor == Color.RED) {
                            Console.WriteLine("Two consecutive red nodes!");
                            return;
                        }
                    if (right.Value <= root.Value) {
                            Console.WriteLine("Tree values out of order!");
                            return;
                        }
                    if (right.Marked) {
                            Console.WriteLine("Cycle in tree structure!");
                            return;
                        }
                    RecursiveValidate(right, blackNodes, soFar);
                }

            // Check black node count
            if (sentinelNode == root.Left || sentinelNode == root.Right) {
                    if (soFar != blackNodes) {
                            Console.WriteLine("Variable number of black nodes to leaves!");
                            return;
                        }
                }

            // Everything checks out if we get this far.
            return;
        }

        public class RBNode
        {
            /// creates new tree node *  
            internal int Value = 0;
            internal Color Color = Color.RED;
            internal bool Marked;
            internal RBNode Parent;
            internal RBNode Left;
            internal RBNode Right;
        }
    }

    class STMTest
    {

        static Object o = new Object();

        public static void ThreadLoop() {
            Random random = new Random();
            int my_shadow = 0;
            RBTree t = STMTest.t;
            bool r;
            int i;

            try {
            for (i = 0; ((Config.OP_COUNT == -1) || (i < Config.OP_COUNT)); i ++) {
                int n = random.Next();
                int v = (n >> 8) & Config.KEY_SPACE_MASK;

                r = false;
                if ((n & 0xff) < Config.LOOKUP_FRAC) {
                    if (Config.KIND == RunKind.Atomic) {
                        try {
                            r = t.Contains(v);
                        }
                        catch (AtomicFakeException) {

                        }
                    }
                    else if (Config.KIND == RunKind.TryAll) {
                        try {
                            r = t.Contains(v);
                        }
                        catch (TryAllFakeException) {

                        }
                    }
                    else {
                        r = t.Contains(v);
                    }
                }
                else if ((n & 0xff) < (Config.LOOKUP_FRAC + Config.REMOVE_FRAC)) {
                    if (Config.KIND == RunKind.Atomic) {
                        try {
                            r = t.Remove(v);
                        }
                        catch (AtomicFakeException) {

                        }
                    }
                    else if (Config.KIND == RunKind.TryAll) {
                        try {
                            r = t.Remove(v);
                        }
                        catch (TryAllFakeException) {

                        }
                    }
                    else {
                        r = t.Remove(v);
                    }
                    if (r) my_shadow -= v;
                }
                else {
                    if (Config.KIND == RunKind.Atomic) {
                        try {
                            r = t.Insert(v);
                        }
                        catch (AtomicFakeException) {

                        }
                    }
                    else if (Config.KIND == RunKind.TryAll) {
                        try {
                            r = t.Insert(v);
                        }
                        catch (TryAllFakeException) {

                        }
                    }
                    else {
                        r = t.Insert(v);
                    }
                    if (r) my_shadow += v;
                }
            }
            }
            catch (Exception e) {
                lock (o) {
                    Console.WriteLine("Failed with " + e);
                }
                throw e;
            }

            lock (o) {
                t.Shadow += my_shadow;
            }
        }

        static RBTree t;

        private static void Usage(String error) {
            Console.WriteLine(
@"Usage:
   tree [-t n] [-n n] [-k <RunKind>] [-d]

   -t n
      Use n threads.

   -n n
      Perform n operations on each thread.
      Runs forever if set to -1.

   -k RunKind
      Specify if operation kind should be ""atomic"", ""tryall"", or ""direct"".

   -d
      Use deterministic output (for automated testing).");

            throw new Exception("Illegal input: " + error);
        }

        private static String NextArg(string[] args, ref int nextArg) {
            if (nextArg >= args.Length) {
                Usage("missing argument");
            }
            return args[nextArg++];
        }

        private static int NextArgInt(string[] args, ref int nextArg, int min) {
            try {
                int x = Int32.Parse(NextArg(args, ref nextArg));
                if (x < min) {
                    Usage("parameter " + (nextArg-1) + " should be >= " + min);
                }
                return x;
            }
            catch (FormatException) {
                Usage("illegal format in parameter " + (nextArg-1));
                return 0;
            }
            catch (OverflowException) {
                Usage("overflow in parameter " + (nextArg-1));
                return 0;
            }
        }

        public static void Main(string[] args) {

            if (Config.LOOKUP_FRAC + Config.REMOVE_FRAC + Config.INSERT_FRAC != 0x100) {
                throw new Exception("Operations fractions should sum to 0x100\n");
            }

            int argIndex = 0;
            if (argIndex < args.Length) {
                if ((String.Compare(args[0], "tree", true) == 0)
                    || (String.Compare(args[0], "tree.exe", true) == 0)
                    || (String.Compare(args[0], "tree.x86", true) == 0)) {
                    argIndex++;
                }
            }

            // Read config options
            while (argIndex < args.Length) {
                String arg = NextArg(args, ref argIndex);
                switch (arg) {
                  case "tree":
                  case "tree.exe":
                  case "tree.x86": {
                      // TODO: SINGULARITY: Don't want to see executable name
                      break;
                  }
                  case "-t": {
                      Config.THREADS = NextArgInt(args, ref argIndex, 0);
                      break;
                  }
                  case "-n": {
                      Config.OP_COUNT = NextArgInt(args, ref argIndex, -1);
                      break;
                  }
                  case "-k": {
                      switch (NextArg(args, ref argIndex)) {
                        case "atomic": {
                            Config.KIND = RunKind.Atomic;
                            break;
                        }
                        case "tryall": {
                            Config.KIND = RunKind.TryAll;
                            break;
                        }
                        case "direct": {
                            Config.KIND = RunKind.Direct;
                            break;
                        }
                        default: {
                            Usage("Unexpected kind " + args[2]);
                            break;
                        }
                      }
                      break;
                  }
                  case "-d": {
                      Config.DETERMINISTIC = true;
                      break;
                  }
                  default: {
                      Usage("unknown parameter: " + arg);
                      break;
                  }
                }
            }

            // Initialise the tree
            t = new RBTree();

            // Start the threads

            // TODO: SINGULARITY: Implement Thread.Name
            // Thread.CurrentThread.Name = "Main";

            Thread[] threads = new Thread[Config.THREADS];
            for (int i = 0; i < Config.THREADS; i ++) {
                threads[i] = new Thread (new ThreadStart (ThreadLoop));
                
                // TODO: SINGULARITY: Implement Thread.Name
                // threads[i].Name = "swapping-thread-" + i;

                threads[i].Start();
            }

            // Wait for the threads to complete
            for (int i = 0; i < Config.THREADS; i ++) {
                threads[i].Join();
            }

            // Check that dead-reckoned sums agree with what we get 
            // traversing the tree
            int s = t.Shadow;
            int a = t.Actual();

            if (Config.DETERMINISTIC) {
                Console.WriteLine("Shadow - Actual = " + (s - a));
            }
            else {
                Console.WriteLine("Shadow = " + s);
                Console.WriteLine("Actual = " + a);
            }

            if (s != a) {
                throw new Exception("Mismatch");
            }
        }
    }
}
