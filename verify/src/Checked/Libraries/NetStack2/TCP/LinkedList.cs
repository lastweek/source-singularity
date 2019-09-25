///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:
//
//  Note:
//


using System;
using Drivers.Net;
using System.Net.IP;
using System.Threading;
using System.Diagnostics;

namespace Microsoft.Singularity.NetStack2
{

    public class LinkedListNode
    {
        public Object theObject;

        public  LinkedListNode prev;
        public  LinkedListNode nxt;
        public  LinkedList parent;

        public LinkedListNode (Object theObject, LinkedList linkedList)
        {
            this.theObject = theObject;
            this.parent = linkedList;
        }

        public Object RemoveObject()
        {
            Object tmp = theObject;
            theObject = null;
            parent = null;

            return tmp;
        }
    }

    //a simple linked list
    public class LinkedList
    {
        public  LinkedListNode head;
        private int count;

        public LinkedList()
        {
            count = 0;
            head = null;
        }

        public int Count {
            get { return count;}
        }

        public LinkedListNode InsertHead(Object theObject)
        {
            LinkedListNode node;

            node = new LinkedListNode(theObject, this);

            if (head == null) {
                head = node;
                node.prev = null;
                node.nxt = null;
            }
            else {
                node.nxt = head;
                head.prev = node;
                head = node;
            }
            count++;

            return node;
        }


        //O(1) removal if client tracks reference to address
        //of node
        public Object Remove(LinkedListNode node)
        {
            VTable.Assert(count > 0);

            VTable.Assert(node.parent == this);
            if (node == head) {
                head = head.nxt;
                if (head != null) {
                    head.prev = null;
                }
                count--;
                return node.RemoveObject();
            }
            LinkedListNode tmp;
            LinkedListNode tmp2;

            tmp = node.prev;
            if (tmp != null) {
                tmp.nxt =  node.nxt;
            }

            tmp = node.nxt;
            if(tmp != null) {
                tmp.prev = node.prev;
            }
            count--;

            return node.RemoveObject();
        }
    }
}










