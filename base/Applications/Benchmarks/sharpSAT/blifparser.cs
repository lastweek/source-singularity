// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System.Collections;
using System.Text;
using System.IO;
using System;
//using Microsoft.Zap;
namespace SharpSAT
{
    public class NetConst
    {
        public const int PI_MASK = 1;
        public const int PO_MASK = (1 << 1);
        public const int LATCH_OUT_MASK = (1 << 2);
        public const int LATCH_IN_MASK = (1 << 3);
        public const int COMB_MASK = (1 << 4);
        //private NetConst() {}
    }

    public enum ELatchDefault
    {
        LATCH_0 = 0,
        LATCH_1 = 1,
        LATCH_DC = 2,
        LATCH_X = 3
    };

    public enum EGateType
    {
        G_UNKNOWN,
        G_NOT,          //o = a'
        G_AND_11,       //o = ab
        G_AND_10,       //o = ab'
        G_AND_01,       //o = a'b
        G_AND_00,       //o = a'b'
        G_OR_11,        //o = a+b
        G_OR_10,        //o = a+b'
        G_OR_01,        //o = a'+b
        G_OR_00,        //o = a'+b'
        G_CONST_1,
        G_CONST_0,
        G_WIRE,
    };

    public class Gate
    {
        public int              index       = -1;
        public EGateType        gate_type   = EGateType.G_UNKNOWN;
        public string           name;
        public IntVector        fanins      = new IntVector(2);
        public IntVector        fanouts     = new IntVector(2);
        public int              type ;
        public ELatchDefault    latch_default ;
        public ObjVector        fanin_names = new ObjVector(1);

        public bool         is_PI()         { return ((type & NetConst.PI_MASK) != 0); }
        public bool         is_PO()         { return ((type & NetConst.PO_MASK) != 0); }
        public bool         is_LATCH_IN()   { return ((type & NetConst.LATCH_IN_MASK) != 0); }
        public bool         is_LATCH()      { return ((type & NetConst.LATCH_OUT_MASK) != 0); }
        public bool         is_COMB()       { return ((type & NetConst.COMB_MASK) != 0); }
        public void         set_PI()        { type |= NetConst.PI_MASK; }
        public void         set_PO()        { type |= NetConst.PO_MASK; }
        public void         set_LATCH_IN()  { type |= NetConst.LATCH_IN_MASK; }
        public void         set_LATCH()     { type |= NetConst.LATCH_OUT_MASK; }
        public void         set_COMB()      { type |= NetConst.COMB_MASK; }
    }

    class NetList : SATCommon
    {
        public string           name;
        public ObjVector        nodes           = new ObjVector(128);
        public IntVector        primary_inputs  = new IntVector(4);
        public IntVector        primary_outputs = new IntVector(4);
        public IntVector        latches         = new IntVector(4);
        public IntVector        combs           = new IntVector(4);
        public IntVector        inputs          = new IntVector(4);     //include PI and latch's outputs
        public IntVector        outputs         = new IntVector(4); //include PO and latch's inputs
        public MyHashtable      name2nodeid     = new MyHashtable();

        public Gate node (int k)
        {
            return (Gate)nodes[k];
        }

        Gate new_node(string name)
        {
            Gate node = new Gate();
            node.name = name;;
            node.index = nodes.size();
            nodes.push_back(node);
            name2nodeid[name] = node.index;
            return node;
        }

        Gate find_node_by_name(string name)
        {
            object o = name2nodeid[name];
            if (o == null)
                return null;
            else
                return (Gate)nodes[(int)o];
        }

        Gate create_pi(string name)
        {
            Gate n;
            if ((n = find_node_by_name(name)) != null) {
                sharp_assert (n.is_PI());
                return n;
            }
            n = new_node(name);
            n.set_PI();
            return n;
        }

        Gate create_po(string name)
        {
            Gate n;
            if ((n = find_node_by_name(name)) == null)
                n = new_node(name);
            n.set_PO();
            return n;
        }

        Gate create_latch(string latch_in, string latch_out, ELatchDefault deft)
        {
            Gate n;
            if ((n = find_node_by_name(latch_out)) == null)
                n = new_node(latch_out);
            //int id = n.index;
            sharp_assert (n.fanin_names.empty());
            n.fanin_names.push_back(latch_in);
            n.latch_default = deft;
            n.set_LATCH();
            return n;
        }

        Gate create_comb(string name, string [] inputs)
        {
            Gate n;
            if ((n = find_node_by_name(name)) == null)
                n = new_node(name);
            //int id = n.index;
            sharp_assert (n.fanin_names.empty());
            foreach (string s in inputs)
                n.fanin_names.push_back(s);
            n.set_COMB();
            return n;
        }

        static string get_multiple_line (StreamReader input)
        {
            string line = null;
            StringBuilder str = new StringBuilder();
            while (true) {
                try {
                    line = input.ReadLine();
                }
                catch (Exception e) {
                    Console.WriteLine("The file could not be read:");
                    Console.WriteLine(e.Message);
                    fatal();
                }
                if (line == null)
                    return null;
                if (line.IndexOf('\\') == -1) {
                    str.Append(line);
                    return str.ToString();
                }
                else
                    str.Append(line.Replace('\\',' '));
            }
        }

        void finalize_construct_network()
        {
            for (int i = 0; i < nodes.size(); ++i) {
                Gate n = node(i);
                for (int j = 0; j < n.fanin_names.size(); ++j) {
                    string name = (string)n.fanin_names[j];
                    Gate pin = find_node_by_name(name);
                    sharp_assert (pin != null);
                    n.fanins.push_back(pin.index);
                    pin.fanouts.push_back(n.index);
                    if (n.is_LATCH())
                        pin.set_LATCH_IN();
                }
            }
            for (int i = 0; i < nodes.size(); ++i) {
                Gate n = node(i);
                if (n.is_PI())
                    primary_inputs.push_back(n.index);
                if (n.is_PI() || n.is_LATCH())
                    inputs.push_back(n.index);
                if (n.is_PO())
                    primary_outputs.push_back(n.index);
                if (n.is_PO() || n.is_LATCH_IN())
                    outputs.push_back(n.index);
                if (n.is_LATCH())
                    latches.push_back(n.index);
                if (n.is_COMB())
                    combs.push_back(n.index);
            }
        }

        public void read_blif (string filename)
        {
            StreamReader input = null;
            ObjVector lines = new ObjVector(128);
            try {
                input = new StreamReader(filename);
            }
            catch (Exception e) {
                Console.WriteLine("The file could not be read:");
                Console.WriteLine(e.Message);
                fatal();
            }
            while (true) {
                string line = get_multiple_line(input);
                if (line == null)
                    break;
                lines.push_back(line);
                if (line == ".end")
                    break;
            }
            for (int i = 0; i < lines.size(); ++i) {
                string line = (string)lines[i];
                string [] temp_tokens = line.Split(new char[] {' ','\t'});
                int total_tokens = 0;
                foreach (string str in temp_tokens)
                    if (str != String.Empty)
                        ++ total_tokens;
                if (total_tokens == 0)
                    continue;
                string [] tokens = new string[total_tokens];
                foreach (string str in temp_tokens) {
                    if (str != String.Empty) {
                        tokens[tokens.Length - total_tokens] = str;
                        -- total_tokens;
                    }
                }
                string first_token = tokens[0];
                if (first_token == ".model") {
                    this.name = tokens[1];
                }
                else if (first_token == ".inputs") {
                    for (int k = 1; k < tokens.Length; ++k)
                        create_pi(tokens[k]);
                }
                else if (first_token == ".outputs") {
                    for (int k = 1; k < tokens.Length; ++k)
                        create_po(tokens[k]);
                }
                else if (first_token == ".latch") {
                    sharp_assert (tokens.Length == 3 || tokens.Length == 4);
                    ELatchDefault dft_v = ELatchDefault.LATCH_X;
                    if (tokens.Length == 4) {
                        string last_token = tokens[3];
                        sharp_assert (last_token.Length == 1);
                        dft_v = (ELatchDefault) Int32.Parse(last_token);
                    }
                    create_latch(tokens[1], tokens[2], dft_v);
                }
                else if (first_token == ".names") {
                    string [] inputs = new string [tokens.Length - 2];
                    sharp_assert (inputs.Length == 1 || inputs.Length == 2);
                    string name = tokens[tokens.Length - 1];
                    for (int k = 1; k < tokens.Length - 1; ++k)
                        inputs[k-1] = tokens[k];
                    Gate node = create_comb(name, inputs);

                    if ((string)lines[i+1] == "1 1" &&
                        (string)lines[i+2] == "0 1" )
                    {
                        node.gate_type = EGateType.G_CONST_1;
                        i+=2;
                    }
                    else if ((string)lines[i+1] == "1 1") {
                        warning ("A gate is a wire, sweep first ");
                        node.gate_type = EGateType.G_WIRE;      ++ i;
                    }
                    else if ((string)lines[i+1] == "0 1") {
                        node.gate_type = EGateType.G_NOT;   ++ i;
                    }
                    else if ((string)lines[i+1] == "11 1") {
                        node.gate_type = EGateType.G_AND_11;    ++ i;
                    }
                    else if ((string)lines[i+1] == "10 1") {
                        node.gate_type = EGateType.G_AND_10;    ++ i;
                    }
                    else if ((string)lines[i+1] == "01 1") {
                        node.gate_type = EGateType.G_AND_01;    ++ i;
                    }
                    else if ((string)lines[i+1] == "00 1") {
                        node.gate_type = EGateType.G_AND_00;    ++ i;
                    }
                    else if ((string)lines[i+1] == "0- 1" &&
                        (string)lines[i+2] == "-0 1")
                    {
                        node.gate_type = EGateType.G_OR_00; i+=2;
                    }
                    else if ((string)lines[i+1] == "0- 1" &&
                        (string)lines[i+2] == "-1 1")
                    {
                        node.gate_type = EGateType.G_OR_01; i+=2;
                    }
                    else if ((string)lines[i+1] == "1- 1" &&
                        (string)lines[i+2] == "-0 1")
                    {
                        node.gate_type = EGateType.G_OR_10; i+=2;
                    }
                    else if ((string)lines[i+1] == "1- 1" &&
                        (string)lines[i+2] == "-1 1")
                    {
                        node.gate_type = EGateType.G_OR_11; i+=2;
                    }
                    else {
                        fatal ("Don't know gate type for " + line);
                    }
                    sharp_assert ( ((string)lines[i+1])[0] == '.');
                }
                else if (first_token == ".end") {
                    break;
                }
                else if (first_token == ".wire_load_slope") {
                    warning("Warning: Ignoring " + first_token);
                }
                else if (first_token[0] == '.') {
                    fatal (first_token + ": Unable to handle this keyword");
                }
            }
            finalize_construct_network();
        }

        public void write_blif(string filename)
        {
            StreamWriter outfile = new StreamWriter(filename);
            outfile.WriteLine ( ".model " + this.name );

            outfile.Write ( ".inputs" );
            for (int i = 0; i < primary_inputs.size(); ++i)
                outfile.Write ( " " + node(primary_inputs[i]).name) ;
            outfile.WriteLine ();

            outfile.Write ( ".outputs" );
            for (int i = 0; i < primary_outputs.size(); ++i)
                outfile.Write ( " " + node(primary_outputs[i]).name) ;
            outfile.WriteLine ();

            for (int i = 0; i < latches.size(); ++i) {
                Gate n = node(latches[i]);
                outfile.WriteLine ( ".latch " + node(n.fanins[0]).name + " " + n.name + " " + (int) n.latch_default );
            }
            for (int i = 0; i < combs.size(); ++i) {
                Gate n = node(combs[i]);
                outfile.Write ( ".names");
                for (int j = 0; j < n.fanins.size(); ++j)
                    outfile.Write ( " " + node(n.fanins[j]).name);
                outfile.WriteLine (" " + n.name );
                if (n.gate_type == EGateType.G_NOT)
                    outfile.WriteLine ( "0 1" );
                else if (n.gate_type == EGateType.G_AND_11)
                    outfile.WriteLine ( "11 1" );
                else if (n.gate_type == EGateType.G_AND_10)
                    outfile.WriteLine ( "10 1" );
                else if (n.gate_type == EGateType.G_AND_01)
                    outfile.WriteLine ( "01 1" );
                else if (n.gate_type == EGateType.G_AND_00)
                    outfile.WriteLine ( "00 1" );
                else if (n.gate_type == EGateType.G_OR_11)
                    outfile.WriteLine ( "1- 1" + '\n' + "-1 1" );
                else if (n.gate_type == EGateType.G_OR_10)
                    outfile.WriteLine ( "1- 1" + '\n' + "-0 1" );
                else if (n.gate_type == EGateType.G_OR_01)
                    outfile.WriteLine ( "0- 1" + '\n' + "-1 1" );
                else if (n.gate_type == EGateType.G_OR_00)
                    outfile.WriteLine ( "0- 1" + '\n' + "-0 1" );
//              else if (n.gate_type == EGateType.G_EQUAL)
//                  outfile.WriteLine ( "11 1" + '\n' + "00 1" );
                else if (n.gate_type == EGateType.G_CONST_1)
                    outfile.WriteLine ( "1 1" + '\n' + "0 1" );
                else if (n.gate_type == EGateType.G_WIRE)
                    outfile.WriteLine ( "1 1" + '\n' + "0 0" );
                else
                    fatal ("Unknown gate type" );
            }
            outfile.WriteLine ( ".end" );
            outfile.Close();
        }
    }
}
