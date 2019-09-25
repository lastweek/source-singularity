// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Text;
using System.IO;
using System.Reflection;
using System.Text.RegularExpressions;

namespace Microsoft.Singularity.Applications
{
    class Generator
    {
        private String specFile;
        private String outputFile;
        private String className;
        private String targetNamespace;
        private const String fieldsSectionHeader = "[fields]";
        private String fieldsSectionCode;
        private static bool compileRegex = false;
        private const String initSection = "[init]";
        private const String tokensSection = "[tokens]";
        private const String grammarSection = "[grammar]";

        private const String EPSILON = "epsilon";
        private const int EPSILON_ID = 1;
        private Terminal epsilonTerm;

        private const String END_MARKER = "$";
        private const int END_MARKER_ID = 2;
        private Terminal endMarkerTerm;

        private ArrayList terminalList;
        private Hashtable productionStrings;
        private Hashtable grammarStringTable;
        private Hashtable precedenceTable;

        private Symbol[] grammarTable;
        private int numTerminals = 0;
        public Generator(String specFile,
                         String targetNamespace,
                         String className,
                         String outputFile)
        {
            this.specFile = specFile;
            this.targetNamespace = targetNamespace;
            this.className = className;
            this.outputFile = outputFile;

            terminalList = new System.Collections.ArrayList();
            productionStrings = new Hashtable();
            grammarStringTable = new Hashtable();
            precedenceTable = new Hashtable();
        }

        public static void Main(String[] args)
        {
            if (args.Length < 4) {
                Console.WriteLine("Usage: spg specfile targetNamespace targetClass outputFile");
                return;
            }

            //ScriptEngine.Run(fileString, new ScriptEngine.CommandLineRunner(nothing));
            Generator gen = new Generator(args[0], args[1], args[2], args[3]);
            gen.Generate();
        }

        public static int nothing(String[] args, bool isBackground){ return 0; }
        private static Regex comment = new Regex("#.*"); //will eat more than it should

        public void Generate()
        {

            String actionTableCode, gotoTableCode, tokenTypeTableCode, lexerActionMethodsCode,
                productionTable, productionActionMethods;

            epsilonTerm = new Terminal(EPSILON, 1);
            grammarStringTable[EPSILON] = epsilonTerm;
            numTerminals++;
            endMarkerTerm = new Terminal(END_MARKER, 2);
            grammarStringTable[END_MARKER] = epsilonTerm;
            numTerminals++;

            ParseSpecification();
            GenerateGrammarTable();

            GenerateParseTables(out actionTableCode, out gotoTableCode, out tokenTypeTableCode, out lexerActionMethodsCode, out productionTable, out productionActionMethods);
            DerivedParserClassTemplate template = GenerateParserClass(actionTableCode, gotoTableCode, tokenTypeTableCode, lexerActionMethodsCode, productionTable, productionActionMethods);

            WriteClassFile(template);
        }

        private void ParseSpecification()
        {
            FileStream file = new FileStream(specFile, FileMode.Open, FileAccess.Read);
            StreamReader fr = new StreamReader(file);
            String fileString = fr.ReadToEnd();

            StringReader sr = new StringReader(fileString);
            String line;
            bool parsedTokens = false, parsedGrammar = false;
            while ((line = sr.ReadLine()) != null) {
                line = line.Trim();
                if (line.Length == 0) continue;
                if (line[0] == '#') continue; //skip comments
                switch (line) {
                    case fieldsSectionHeader:
                        ParseFieldsSection(sr);
                        break;
                    case initSection:
                        ParseInitSection(sr);
                        break;
                    case tokensSection:
                        ParseTokenSection(sr);
                        parsedTokens = true;
                        break;
                    case grammarSection:
                        ParseGrammarSection(sr);
                        parsedGrammar = true;
                        break;
                    default:
                        continue;
                }
            }
            sr.Close();
            file.Close();
            if (!parsedTokens) {
                throw new Exception("missing lexical spec");
            }
            else if (!parsedGrammar) {
                throw new Exception("missing grammar spec");
            }
        }

        private void GenerateGrammarTable()
        {
            grammarTable = new Symbol[Symbol.idCount];
            grammarTable[1] = epsilonTerm;
            grammarTable[2] = endMarkerTerm;
            foreach (Terminal token in terminalList) {
                grammarTable[token.id] = token;
            }
            foreach (System.Collections.DictionaryEntry entry in productionStrings) {
                String name = entry.Key as String;
                Nonterminal nonterm = grammarStringTable[name] as Nonterminal;
                grammarTable[nonterm.id] = nonterm;
                System.Collections.ArrayList prods = entry.Value as System.Collections.ArrayList;
                int[][] rhss = new int[prods.Count][];
                String[][] allBindings = new string[prods.Count][];
                ProductionAction[] actions = new ProductionAction[prods.Count];
                int i = 0;
                foreach (ProductionString prod in prods) {
                    actions[i] = new ProductionAction(this, nonterm.id, i, prod.action);
                    ArrayList elems = new System.Collections.ArrayList();
                    ArrayList bindingsList = new ArrayList();
                    foreach (String elemAndBinding in prod.rhs.Split(new char[] { ' ' })) {
                        if (elemAndBinding == "") continue;
                        String[] split = elemAndBinding.Split(":".ToCharArray());
                        if (split[0] == EPSILON) continue;
                        Symbol sym = grammarStringTable[split[0]] as Symbol;
                        if (sym == null) throw new Exception("Undefined symbol: " + split[0]);
                        elems.Add(sym.id);
                        String binding = null;
                        if (split.Length > 1) {
                            binding = split[1];
                        }
                        bindingsList.Add(binding);
                    }
                    int[] rhs = new int[elems.Count];
                    for (int j = 0; j < rhs.Length; ++j) {
                        rhs[j] = (int)elems[j];
                    }
                    rhss[i] = rhs;

                    String[] bindings = new String[bindingsList.Count];
                    for (int j = 0; j < bindings.Length; ++j) {
                        bindings[j] = (String)bindingsList[j];
                    }
                    allBindings[i] = bindings;

                    ++i;
                }
                nonterm.rhss = rhss;
                nonterm.bindings = allBindings;
                nonterm.actions = actions;
            }
        }

        private void WriteClassFile(DerivedParserClassTemplate template)
        {
            String classText = template.Dump();
            FileStream file = new FileStream(outputFile, FileMode.Create, FileAccess.Write);
            StreamWriter sw = new StreamWriter(file);
            sw.Write(classText);
            sw.Close();
            file.Close();
        }

        private DerivedParserClassTemplate GenerateParserClass(String actionTableCode, String gotoTableCode, String tokenTypeTableCode, String lexerActionMethodsCode, String productionTable, String productionActionMethods)
        {
            DerivedParserClassTemplate template = new DerivedParserClassTemplate(targetNamespace, className);
            template.AddUsingCode("using System;\r\nusing System.Collections;\r\nusing System.Text;\r\nusing System.IO;\r\nusing System.Text.RegularExpressions;\r\nusing Microsoft.Contracts;\r\n");
            template.AddFieldCode(fieldsSectionCode);
            template.AddConstructorCode(actionTableCode + gotoTableCode + tokenTypeTableCode + productionTable);
            template.AddMethodCode(lexerActionMethodsCode + productionActionMethods);
            template.AddDefaultMembers();
            return template;
        }

        private void GenerateParseTables(out String actionTableCode, out String gotoTableCode, out String tokenTypeTableCode, out String lexerActionMethodsCode, out String productionTable, out String productionActionMethods)
        {
            ISet setsOfItems = ComputeSetsOfItems();
            computeFirst();
            computeFollow();
            String parserType = "Parser.";
            ArrayList productions;
            Parser.Action[][] actionTable = computeActionTable(setsOfItems, out productions);
            actionTableCode = GetProductionActionTableCode(parserType, "actionTable", actionTable);
            Parser.State[][] gotoTable = computeGotoTable(setsOfItems);
            gotoTableCode = GetGotoTableCode(parserType, "gotoTable", gotoTable);
            GetTokenTypeTableCode("tokenList", out tokenTypeTableCode, out lexerActionMethodsCode);
            GetProductionListCode(parserType, productions, out productionTable, out productionActionMethods);
        }

        public class DerivedParserClassTemplate
        {
            private String nspace;
            private String className;
            StringBuilder usings;
            StringBuilder derivations;
            StringBuilder fields;
            StringBuilder constructor;
            StringBuilder methods;

            public DerivedParserClassTemplate(String nspace, String className)
            {
                this.nspace = nspace; this.className = className;
                usings = new StringBuilder();
                derivations = new StringBuilder(",");
                fields = new StringBuilder();
                constructor = new StringBuilder();
                methods = new StringBuilder();
            }
            public void AddDefaultMembers() {
                fields.Append("  private Action[,]! actionTable;\n");
                fields.Append("  private State[,]! gotoTable;\n");
                fields.Append("  private Production[]! productionTable;\n");
                fields.Append("  private TokenType[]! tokenList;\n");
                methods.Append("  protected override Action[,]! ActionTable { get { return this.actionTable; } }\n");
                methods.Append("  protected override State[,]! GotoTable { get { return this.gotoTable; } }\n");
                methods.Append("  protected override Production[]! ProductionTable { get { return this.productionTable; } }\n");
                methods.Append("  protected override TokenType[]! TokenList { get { return this.tokenList; } }\n");

            }
            public void AddDerivationCode(String code)
            {
                derivations.Append(code);
            }
            public void AddMethodCode(String code){
                methods.Append(code);
            }

            public void AddFieldCode(String code)
            {
                fields.Append(code);
            }
            public void AddConstructorCode(String code)
            {
                constructor.Append(code);
            }

            public void AddUsingCode(String code)
            {
                usings.Append(code);
            }

            public String Dump()
            {
                StringBuilder dump = new StringBuilder();
                dump.Append("//This file is automatically generated\r\n" + usings + "\r\n" +
                            "namespace " + nspace + "{\r\n"
                            + "\r\n class " + className + " : Parser" + "\r\n" +
                                        "{\r\n" +
                                        fields +
                            //    "[NotDelayed]\r\n" +
                                        "public " + className + "(){\r\n " + constructor +
                            ";\r\n" +
                            //"base();\r\n" +
                            "}\r\n" +
                                        methods +
                                        "\t}\r\n" +
                              "}");

                return dump.ToString();
            }
        }

        private void GetProductionListCode(String parserTypeString, ArrayList productions, out String productionTable, out String productionActionMethods)
        {
            parserTypeString = "";
            StringBuilder array = new StringBuilder();
            StringBuilder methods = new StringBuilder();
            int i = 0;
            array.Append(parserTypeString + "productionTable = new[Delayed] Production[]{");
            foreach (ProductionAction action in productions) {
                String methodName = "production_action_" + i;
                StringBuilder method = new StringBuilder();
                method.Append("private Object " + methodName + "(Stack! stack) {\r\n");
                method.Append("\tObject value = null;\r\n");
                String[] bindings = (grammarTable[action.nonterm] as Nonterminal).bindings[action.production];
                for (int j = bindings.Length - 1; j >= 0; --j) {
                    if (bindings[j] != null) {
                        method.Append("\tObject " + bindings[j] + " = ( (StackElement!) stack.Pop()).value;");

                    }
                    else{
                        method.Append("\tstack.Pop(); //pop non binding element");
                    }
                    method.Append(j != 0 ? "\r\n\tstack.Pop(); //pop state\r\n" : "");
                }
                method.Append("\r\n\t\t//user code:\r\n" + action.action);
                method.Append("\r\n\treturn value;");
                method.Append("\r\n}\r\n");
                methods.Append(method);
                array.Append("new " + parserTypeString + "Production( " + action.nonterm + ", new " + parserTypeString + "Reducer(this." + methodName + ")),");
                ++i;
            }
            array.Remove(array.Length - 1, 1);
            array.Append("};\r\n");
            productionTable = array.ToString();
            productionActionMethods = methods.ToString();

        }
        private String lexActionMethodPrefix = "LexActionMethod_";
        private void GetTokenTypeTableCode(String tableName, out String tokenTableCode, out String lexerMethodsCode)
        {
            StringBuilder sb = new StringBuilder();
            StringBuilder methods = new StringBuilder();
            sb.Append(tableName + " = new[Delayed] TokenType[] \r\n\t\t{");
            int i = 0;
            int regExId = 0;
            RegexCompilationInfo[] regexCompInfo = new RegexCompilationInfo[terminalList.Count];
            foreach (Terminal term in terminalList) {
                String methodName = lexActionMethodPrefix + i;
                String id = term.id.ToString();
                if (compileRegex) {
                    regexCompInfo[regExId] = new RegexCompilationInfo(term.regex, RegexOptions.None, "LexRegex" + regExId, targetNamespace, true);
                }
                String regex = compileRegex ?  "(new LexRegex" + regExId++ + "())" : "new Regex(@" + term.regex + ")" ;

                String lexer;
                if (term.action != null && term.action != "") {
                    String method =
                        "\tprivate void " + methodName + "(Token! tok) { \r\n" + term.action + "\r\n\t}\r\n";
                    methods.Append(method);
                    lexer = "new Lexer(this." + methodName + ")";
                    ++i;
                }
                else {
                    lexer = "null";
                }
                sb.Append("new  TokenType(" + id + "," + regex + "," + lexer + " ),");
            }
            if (terminalList.Count != 0)
                sb.Remove(sb.Length - 1, 1);
            sb.Append("}\r\n;");
            if (compileRegex) {
                AssemblyName assembly = new AssemblyName();
                assembly.Name = "LexerRegex";
                Regex.CompileToAssembly(regexCompInfo, assembly);
            }
                tokenTableCode = sb.ToString();
            lexerMethodsCode = methods.ToString();

        }
        private String GetGotoTableCode(String parserTypeString, String tableName, Parser.State[][] gotoTable)
        {
            StringBuilder sb = new StringBuilder();

            sb.Append(tableName + " = new State[,]\r\n\t{\r\n");
            foreach (Parser.State[] row in gotoTable) {
                sb.Append("\r\n\t\t{");
                foreach (Parser.State state in row) {
                    if (state == null) {
                        sb.Append("null,");
                        continue;
                    }
                    sb.Append("new " + parserTypeString + "State(" + state.id.ToString() + "),");
                }
                if (row.Length != 0)
                    sb.Remove(sb.Length - 1, 1);
                sb.Append("},");
            }
            if (gotoTable.Length != 0)
                sb.Remove(sb.Length - 1, 1);
            sb.Append("\r\n\t};\r\n");

            return sb.ToString();
        }

        private Parser.State[][] computeGotoTable(ISet setsOfItems)
        {
            Parser.State[][] gotoTable = new Parser.State[setsOfItems.Count][];
            Hashtable/*ISet -> int*/ stateTable = new Hashtable();
            int i = 0;
            foreach (ISet set in setsOfItems) {
                gotoTable[i] = new Parser.State[Symbol.idCount];
                stateTable[set] = i++;
            }

            foreach (ISet items in setsOfItems) {
                foreach (Symbol symbol in grammarTable) {

                    if (symbol is Terminal) {
                        gotoTable[(int)stateTable[items]][symbol.id] = null;
                        continue;
                    }
                    ISet gotoSet = computeGoto(items, symbol);
                    if (gotoSet.Count == 0) continue;
                    Object gotoState = stateTable[gotoSet];
                    if (gotoState == null) throw new Exception("missing state"); ;
                    gotoTable[(int)stateTable[items]][symbol.id] = new Parser.State((int)gotoState);
                }
            }
            return gotoTable;

        }

        private String GetProductionActionTableCode(String parserTypeString, String tableName, Parser.Action[][] actionTable)
        {
            StringBuilder sb = new StringBuilder();
            sb.Append(tableName);
            sb.Append(" = new Parser.Action[,]\r\n\t{\r\n");
            foreach (Parser.Action[] row in actionTable) {
                sb.Append("\r\n\t\t{");
                foreach (Parser.Action action in row) {
                    if (action == null) {
                        sb.Append("null,");
                        continue;
                    }
                    sb.Append("new " + parserTypeString + "Action(");
                    String actionType = "";
                    switch (action.type) {
                        case Parser.ActionType.ACCEPT:
                            actionType = parserTypeString + "ActionType.ACCEPT";
                            break;
                        case Parser.ActionType.REDUCE:
                            actionType = parserTypeString + "ActionType.REDUCE";
                            break;
                        case Parser.ActionType.SHIFT:
                            actionType = parserTypeString + "ActionType.SHIFT";
                            break;
                        default:
                            throw new Exception("missed action type");
                    }
                    sb.Append(actionType + "," + action.stateOrProduction.ToString() + "),");
                }
                if (row.Length != 0)
                    sb.Remove(sb.Length - 1, 1);
                sb.Append("},");
            }
            if (actionTable.Length != 0)
                sb.Remove(sb.Length - 1, 1);
            sb.Append("\r\n\t};\r\n");

            return sb.ToString();
        }
        private Parser.Action[][] computeActionTable(ISet setsOfItems, out ArrayList productions)
        {
            //TODO: could be reduced since we only consult on terminals
            productions = new ArrayList();
            Parser.Action[][] actionTable = new Parser.Action[setsOfItems.Count][];
            Hashtable/*ISet -> int*/ stateTable = new Hashtable();
            Object[][] productionCacheTable = new Object[ Symbol.idCount][];

            int i = 0;
            foreach (ISet set in setsOfItems) {
                actionTable[i] = new Parser.Action[Symbol.idCount];
                stateTable[set] = i++;
            }
            foreach (ISet items in setsOfItems) {
                foreach (Item item in items) {
                    Nonterminal nonterm = grammarTable[item.nonterm] as Nonterminal;
                    int[] production = nonterm.rhss[item.production];
                    if (item.position == production.Length) {
                        if (item.nonterm == 0) {
                            Object obj = stateTable[items];
                            if (obj == null) throw new Exception("Missing state:" + items);
                            if (actionTable[(int)obj][END_MARKER_ID] != null) throw new Exception("not slr");
                            actionTable[(int)obj][END_MARKER_ID] = new Parser.Action(Parser.ActionType.ACCEPT, 0);
                            continue;
                        }

                        Object[] nontermProds = productionCacheTable[item.nonterm];
                        if (nontermProds == null) {
                            productionCacheTable[item.nonterm] = nontermProds = new Object[nonterm.rhss.Length];
                        }
                        Object prodIndexObject = nontermProds[item.production];
                        foreach (int followSym in followTable[item.nonterm] as HashSet) {
                            if (prodIndexObject == null) {
                                nontermProds[item.production] = prodIndexObject = productions.Add(nonterm.actions[item.production]);
                            }
                            int prodIndex = (int) prodIndexObject;
                            Object obj = stateTable[items];
                            if (obj == null) throw new Exception("Missing state:" + items);
                            Parser.Action newAction = new Parser.Action(Parser.ActionType.REDUCE, prodIndex);
                            Parser.Action currentAction = actionTable[(Int32)obj][followSym];
                            if (currentAction != null && !currentAction.Equals(newAction)) {
                                newAction = ResolveAction(currentAction, newAction, (Terminal) grammarTable[followSym], items, productions);
                            }
                            actionTable[(Int32)obj][followSym] = newAction;
                        }
                    }
                    else {
                        foreach (Symbol symbol in grammarTable) {
                            if (symbol is Nonterminal) continue;
                            ISet gotoSet = computeGoto(items, symbol);
                            Object nextState = (Object)stateTable[gotoSet];
                            if (nextState == null) continue;
                            Parser.Action newAction = new Parser.Action(Parser.ActionType.SHIFT, (Int32)nextState);
                            Parser.Action currentAction = actionTable[(Int32)stateTable[items]][symbol.id];
                            if (currentAction != null && !currentAction.Equals(newAction)) {
                                newAction = ResolveAction(currentAction, newAction, (Terminal) symbol ,items, productions);
                            }
                            actionTable[(Int32)stateTable[items]][symbol.id] = newAction;
                        }
                    }
                }
            }
            return actionTable;
        }
        private Parser.Action ResolveAction(Parser.Action a1, Parser.Action a2, Terminal symbol, ISet items, ArrayList productions)
        {
            Parser.Action reducer;
            Parser.Action shifter;
            if (a1.type == Parser.ActionType.REDUCE) {
                reducer = a1; shifter = a2;
            }
            else {
                reducer = a2; shifter = a1;
            }
            ProductionAction reduction = productions[reducer.stateOrProduction] as ProductionAction;
            int[] reductionSymbols = (grammarTable[reduction.nonterm] as Nonterminal).rhss[reduction.production];
            int j;
            for (j = reductionSymbols.Length - 1; j >= 0; --j) {
                if (grammarTable[reductionSymbols[j]] is Terminal) break;
            }
            if (j == -1) throw new Exception("non terminal in reduction");
            int reductionTerminal = reductionSymbols[j];
            int precedence;
            PrecedenceRelation precedenceRelation = precedenceTable[new HashSet(new int[] { symbol.id, reductionTerminal })] as PrecedenceRelation;
                if (precedenceRelation == null) {
                    //Console.Write("no precedence relation between " + grammarTable[symbol.id].name + " and " + grammarTable[reductionTerminal].name);
                    //Console.WriteLine(" defaulting to equivalent precedence");
                    precedence = PrecedenceRelation.EQUAL;
                }
                else {
                    precedence = precedenceRelation.Precedence(symbol.id);
                }

            Parser.Action action;
            switch (precedence) {
                case PrecedenceRelation.EQUAL:
                    action = reducer; //left associative by default?
                    break;
                case PrecedenceRelation.GREATER:
                    action = shifter;
                    break;
                case PrecedenceRelation.LESS:
                    action = reducer;
                    break;
                default:
                    throw new Exception("missing precedence type");
            }
            return action;
        }
        private Parser.Action PromptAction(Parser.Action a1, Parser.Action a2, Terminal symbol, ISet items, ArrayList productions)
        {
            Console.WriteLine("In State: ");
            foreach (Item item in items) {
                Console.WriteLine(item.ToString());
            }
            Console.WriteLine("On symbol: " + symbol.name);
            Console.WriteLine("1) " + ActionString(a1, productions));
            Console.WriteLine("2) " + ActionString(a2, productions));
            Console.Write("Selection: ");

            int selection;
            do {
                selection = Convert.ToInt32(Console.ReadLine());
            } while (selection != 1 && selection != 2);

            return selection == 1 ? a1 : a2;
        }

        private string ActionString(Parser.Action action, ArrayList productions)
        {
            switch (action.type) {
                case Parser.ActionType.ACCEPT:
                    return "ACCEPT";
                case Parser.ActionType.REDUCE:
                    return "REDUCE by " + productions[action.stateOrProduction];
                case Parser.ActionType.SHIFT:

                    return "SHIFT";
                default:
                    throw new Exception("missing action type");
            }
        }

        private class Item
        {
            public int nonterm;
            public int production;
            public int position;
            public Generator gen;
            public Item(Generator gen, int nonterm, int production, int position)
            {
                this.gen = gen; this.nonterm = nonterm; this.production = production; this.position = position;
            }
            public override int GetHashCode()
            {
                return nonterm.GetHashCode() ^ production.GetHashCode() ^ position.GetHashCode();
            }

            public override bool Equals(object obj)
            {
                if (!(obj is Item)) return false;
                Item that = obj as Item;
                return this.nonterm == that.nonterm && this.production == that.production && this.position == that.position;
            }

            public override String ToString()
            {
                StringBuilder sb = new StringBuilder();
                Nonterminal nonterm = gen.grammarTable[this.nonterm] as Nonterminal;
                for (int i = 0; i < nonterm.rhss[production].Length; ++i) {
                    String spacer = i == this.position ? " . " : " ";
                    sb.Append(spacer + gen.grammarTable[nonterm.rhss[production][i]].ToString());
                }
                if (this.position == nonterm.rhss[production].Length) sb.Append(" . ");
                return gen.grammarTable[this.nonterm] + "=>" + sb.ToString();
            }

        }

        private ISet doClosure(ISet items)
        {
            Queue toProcess = new Queue(items);
            ISet newItems = new HashSet(items);
            while (toProcess.Count != 0) {
                Item item = toProcess.Dequeue() as Item;
                Nonterminal nonterm = grammarTable[item.nonterm] as Nonterminal;
                if (item.position == nonterm.rhss[item.production].Length) continue;
                Symbol nextSymbol = grammarTable[nonterm.rhss[item.production][item.position]];
                if (nextSymbol is Nonterminal) {
                    for (int j = 0; j < ((Nonterminal)nextSymbol).rhss.Length; ++j) {
                        Item newItem = new Item(this, nextSymbol.id, j, 0);
                        if (!newItems.Contains(newItem)) {
                            toProcess.Enqueue(newItem);
                            newItems.Add(newItem);
                        }
                    }
                }
            }
            return newItems;
        }

        private ISet computeGoto(ISet items, Symbol symbol)
        {
            ISet gotoSet = new HashSet();
            foreach (Item item in items) {
                Nonterminal nonterm = grammarTable[item.nonterm] as Nonterminal;
                if (item.position == nonterm.rhss[item.production].Length) continue;
                if (nonterm.rhss[item.production][item.position] != symbol.id) continue;
                Item nextItem = new Item(this, item.nonterm, item.production, item.position + 1);
                gotoSet.Add(nextItem);
            }

            gotoSet = doClosure(gotoSet);
            return gotoSet;
        }
        // these need to be ordered by creation so set 0 is the initial state  
        private ISet ComputeSetsOfItems()
        {
            ISet sets = new HashSet();
            ISet rootSet = new HashSet();
            rootSet.Add(new Item(this, 0, 0, 0));
            rootSet = doClosure(rootSet);
            sets.Add(rootSet);
            Queue toProcess = new Queue(sets);
            while (toProcess.Count != 0) {
                ISet set = toProcess.Dequeue() as ISet;
                foreach (Symbol symbol in grammarTable) {
                    ISet gotoSet = computeGoto(set, symbol);
                    if (gotoSet.Count == 0)
                        continue;
                    if (sets.Contains(gotoSet)) continue;
                    toProcess.Enqueue(gotoSet);
                    sets.Add(gotoSet);
                }
            }
            return sets;
        }
        ISet[] firstTable;
        public void computeFirst()
        {
            firstTable = new ISet[Symbol.idCount];
            bool changed = true;
            while (changed) {
                changed = false;
                foreach (Symbol symbol in grammarTable) {
                    if (symbol is Terminal) {
                        ISet first = firstTable[symbol.id];
                        if (first == null) {
                            first = new HashSet();
                            changed = true;
                        }
                        first.Add(symbol.id);

                        firstTable[symbol.id] = first;

                    }
                    else if (symbol is Nonterminal) {
                        Nonterminal nonterm = symbol as Nonterminal;
                        foreach (int[] rhs in nonterm.rhss) {
                            ISet newFirst = firstTable[nonterm.id];

                            if (newFirst == null) {
                                firstTable[nonterm.id] = newFirst = new HashSet();
                            }
                            HashSet oldFirst = new HashSet(newFirst);
                            if (rhs.Length == 0) { // epsilon production  
                                newFirst.Add(EPSILON_ID);
                            }
                            else {
                                bool epsilonPrior = true;
                                for (int i = 0; i < rhs.Length && epsilonPrior; ++i) {
                                    Symbol sym = grammarTable[rhs[i]];
                                    if (sym is Terminal) {
                                        newFirst.Add(rhs[i]);
                                        if (sym.id != EPSILON_ID)
                                            epsilonPrior = false;
                                    }
                                    else if (sym is Nonterminal) {
                                        ISet moreFirst = firstTable[sym.id];
                                        if (moreFirst == null) {
                                            moreFirst = new HashSet();
                                            firstTable[sym.id] = moreFirst;
                                            break;
                                        }
                                        newFirst.AddAll(moreFirst);
                                        if (!moreFirst.Contains(EPSILON_ID))
                                            epsilonPrior = false;
                                    }
                                }
                            }
                            changed |= !oldFirst.Equals(newFirst);
                        }
                    }
                }
            }

        }

        private ISet[] followTable;
        public void computeFollow()
        {
            followTable = new ISet[Symbol.idCount];
            followTable[0] = new HashSet();
            followTable[0].Add(END_MARKER_ID);
            bool changed = false;
            do {
                changed = false;
                foreach (Symbol symbol in grammarTable) {
                    if (!(symbol is Nonterminal)) continue;
                    Nonterminal nonterm = symbol as Nonterminal;
                    changed |= ComputeFollowForNonterminal(changed, nonterm);
                }
            } while (changed);
        }

        private bool ComputeFollowForNonterminal(bool changed, Nonterminal nonterm)
        {
            foreach (int[] rhs in nonterm.rhss) {
                changed |= ComputeFollowForProduction(changed, nonterm, rhs);
            }
            return changed;
        }

        private bool ComputeFollowForProduction(bool changed, Nonterminal nonterm, int[] rhs)
        {
            ISet endFirst = new HashSet();
            for (int i = rhs.Length - 1; i >= 0; --i) {
                Symbol sym = grammarTable[rhs[i]];
                if (sym is Nonterminal) {
                    ISet follow = followTable[sym.id];
                    if (follow == null) {
                        followTable[sym.id] = follow = new HashSet();
                    }
                    ISet oldFollow = new HashSet(follow);
                    follow.AddAll(endFirst);
                    follow.Remove(EPSILON_ID);
                    if (i == rhs.Length - 1 || endFirst.Contains(EPSILON_ID)) {
                        ISet prodFollow = followTable[nonterm.id];
                        if (prodFollow == null) {
                            followTable[nonterm.id] = prodFollow = new HashSet();
                        }
                        follow.AddAll(prodFollow);
                    }
                    if (!oldFollow.Equals(follow)) changed = true;
                    if (!firstTable[sym.id].Contains(EPSILON_ID))
                        endFirst = new HashSet();
                    endFirst.AddAll(firstTable[sym.id]);
                }
                else {
                    endFirst = new HashSet();
                    endFirst.Add(sym.id);
                }
            }
            return changed;
        }

        public void ParseFieldsSection(TextReader sr)
        {
            fieldsSectionCode = ParseSection(sr);
        }

        public String ParseInitSection(TextReader sr)
        {
            return ParseSection(sr);
        }
        private const String tokenAssign = ":=";

        class TokenSpec
        {

            public Terminal token;
            public Regex regex;
            public TokenSpec(Terminal token, Regex regex)
            {
                this.token = token; this.regex = regex;
            }
        }

        private class PrecedenceRelation
        {
            public const int LESS = -1, EQUAL = 0, GREATER = 1;
            public int type;
            public int leftTerminal;
            public int rightTerminal;
            public PrecedenceRelation(int type, int leftTerminal, int rightTerminal)
            {
                this.type = type; this.leftTerminal = leftTerminal; this.rightTerminal = rightTerminal;
            }

            public override int GetHashCode()
            {
                return type.GetHashCode() ^ leftTerminal.GetHashCode() ^ rightTerminal.GetHashCode();
            }

            public override bool Equals(object obj)
            {
                if (!(obj is PrecedenceRelation)) return false;
                PrecedenceRelation that = obj as PrecedenceRelation;
                return this.type == that.type && this.leftTerminal == that.leftTerminal && this.rightTerminal == that.rightTerminal;
            }
            //assumes that you that right side of the caller and this instance match
            public int Precedence(int leftSide)
            {
                if (this.leftTerminal == leftSide) return this.type;
                else {
                    switch (this.type) {
                        case LESS:
                            return GREATER;
                        case EQUAL:
                            return EQUAL;
                        case GREATER:
                            return LESS;
                        default:
                            throw new Exception("missed type");
                    }
                }
            }

        }
        public void ParseTokenSection(TextReader sr)
        {
            String line = sr.ReadLine();
            if (line == null || line.Trim() != "{") throw new Exception("missing left brace");
            while ((line = sr.ReadLine()) != null) {
                line = line.Trim();
                if (line == "") continue;
                if (line == "}") {
                    return;
                }
                int index = line.IndexOf(tokenAssign);
                if (index == -1) {
                    int precedence = PrecedenceRelation.GREATER;
                    index = line.IndexOf(">");
                    if (index == -1) {
                        precedence = PrecedenceRelation.LESS;
                        index = line.IndexOf("<");
                        if (index == -1) {
                            precedence = PrecedenceRelation.EQUAL;
                            index = line.IndexOf("=");
                            if (index == -1) throw new Exception("invalid token line");
                        }
                    }

                    String[] leftTerminalNames = whitespace.Split(line.Substring(0, index));
                    String[] rightTerminalNames = whitespace.Split(line.Substring(index + 1));
                    Symbol[] rightTerminalSymbols = new Symbol[rightTerminalNames.Length];
                    for (int i = 0; i < rightTerminalSymbols.Length; ++i) {
                        if (rightTerminalNames[i] == "") continue;
                        Symbol rightSymbol = grammarStringTable[rightTerminalNames[i]] as Terminal;
                        if (rightSymbol == null || !(rightSymbol is Terminal))
                            throw new Exception("Symbol is either not defined for non a terminal:" + rightTerminalNames[i]);
                        rightTerminalSymbols[i] = rightSymbol;
                    }
                    foreach (String leftTerminalName in leftTerminalNames) {
                        if (leftTerminalName == "") continue;
                        Symbol leftSymbol = grammarStringTable[leftTerminalName] as Symbol;
                        if (leftSymbol == null || !(leftSymbol is Terminal))
                            throw new Exception("Symbol is either not defined for non a terminal:" + leftTerminalName);
                        foreach (Symbol rightSymbol in rightTerminalSymbols) {
                            if (rightSymbol == null) continue;
                            precedenceTable[new HashSet(new int[] { leftSymbol.id, rightSymbol.id })] = new PrecedenceRelation(precedence, leftSymbol.id, rightSymbol.id);
                        }
                    }

                    continue;
                }
                String regex = line.Substring(index + tokenAssign.Length).Trim();
                String action = ParseSection(sr);
                Terminal token = new Terminal(line.Substring(0, index).Trim(), regex, action);
                grammarStringTable[token.name] = token;
                numTerminals++;
                terminalList.Add(token);
            }
        }


        private const String startSymbol = "S";
        private const String productionSym = "=>";
        public void ParseGrammarSection(TextReader sr)
        {
            String line = sr.ReadLine();
            if (line == null || line.Trim() != "{") throw new Exception("missing left brace");
            bool foundStart = false;
            while ((line = sr.ReadLine()) != null) {
                line = line.Trim();
                if (line == "") continue;
                if (line == "}") {
                    if (!foundStart) {
                        throw new Exception("No start symbol S");
                    }
                    return;
                }
                int index = line.IndexOf(productionSym);
                if (index == -1) throw new Exception("bad grammar format");
                String name = line.Substring(0, index).Trim();
                if (!foundStart && name == startSymbol) {
                    Nonterminal augment = new Nonterminal(startSymbol + "'", 0);
                    grammarStringTable[augment.name] = augment;
                    System.Collections.ArrayList augProdList = new System.Collections.ArrayList();
                    productionStrings[augment.name] = augProdList;
                    augProdList.Add(new ProductionString(augment, startSymbol, ""));
                    foundStart = true;
                }
                String rhs = line.Substring(index + productionSym.Length).Trim();
                String action = ParseSection(sr);

                System.Collections.ArrayList prodList = productionStrings[name] as System.Collections.ArrayList;
                if (prodList == null) {
                    productionStrings[name] = prodList = new System.Collections.ArrayList();
                }

                Nonterminal nonterm = grammarStringTable[name] as Nonterminal;
                if (nonterm == null) {
                    grammarStringTable[name] = nonterm = new Nonterminal(name);
                }
                prodList.Add(new ProductionString(nonterm, rhs, action));

            }

            throw new Exception("missing right brace");
        }
        private static Regex whitespace = new Regex("\\s");

        public static String ParseSection(TextReader sr)
        {
            StringBuilder section = new StringBuilder();
            while (true) {
                int peek = sr.Peek();
                if (peek == -1) return null;
                char cpeek = (char)peek;
                if (whitespace.IsMatch(((char)peek).ToString())) {
                    sr.Read();
                }
                else if (peek != '{') {
                    return null;
                }
                else
                    break;
            }
            sr.Read();
            //if(line == null || line.Trim() != "{") throw new Exception();  
            int numBrackets = 1;
            int last = -1;
            bool inString = false;
            bool inQuotes = false;
            int curr;
            while ((curr = sr.Read()) != -1) {
                switch (curr) {
                    case '{':
                        if (!inString && !inQuotes && last != '\\') numBrackets++;
                        break;
                    case '}':
                        if (!inString && !inQuotes && last != '\\') numBrackets--;
                        break;
                    case '"':
                        if (!inString && last != '\\') {
                            inQuotes = !inQuotes;
                        }
                        break;
                    case '\'':
                        if (!inQuotes && last != '\\')
                            inString = !inString;
                        break;
                }
                if (numBrackets == 0) break;
                section.Append((char)curr);
                last = curr;
            }
            if (numBrackets > 0) throw new Exception("missing bracket");
            return section.ToString();
        }


        private class Symbol
        {
            public static int idCount = 3;
            public int id;
            public String name;
            protected Symbol(String name)
            {
                id = idCount++;
                this.name = name;
            }
            protected Symbol(String name, int id)
            {
                this.name = name;
                this.id = id;
            }

            public override int GetHashCode()
            {
                return name.GetHashCode();
            }

            public override bool Equals(object obj)
            {
                if (!(obj is Symbol)) {
                    return false;
                }
                return name.Equals(((Symbol)obj).name);
            }

            public override string ToString()
            {
                return name + ":" + id;
            }
        }

        private class Nonterminal : Symbol
        {
            public int[][] rhss;
            public String[][] bindings;
            public ProductionAction[] actions;
            public Nonterminal(String name) : base(name) { }
            public Nonterminal(String name, int id) : base(name, id) { }
        }

        private class Terminal : Symbol
        {
            public String regex;
            public String action;
            public Terminal(String name, String regex, String action) : base(name) { this.regex = regex; this.action = action; }
            public Terminal(String name, int id) : base(name, id) { }
        }

        private class ProductionAction
        {
            public String action;
            public int nonterm;
            public int production;
            public Generator gen;
            public ProductionAction(Generator gen, int nonterm, int production, String action)
            {
                this.gen = gen;
                this.nonterm = nonterm;
                this.production = production;
                this.action = action;
            }

            public override String ToString()
            {
                StringBuilder sb = new StringBuilder(gen.grammarTable[nonterm].name + " => ");
                foreach (int sym in (gen.grammarTable[nonterm] as Nonterminal).rhss[production]) {
                    sb.Append(gen.grammarTable[sym].name + " ");
                }
                return sb.ToString();
            }
        }
        private class ProductionString
        {
            Nonterminal nonterm;
            public String rhs;
            public String action;
            public ProductionString(Nonterminal nonterm, String rhs, String action)
            {
                this.nonterm = nonterm;
                this.rhs = rhs;
                this.action = action;
            }
        }
    }
}
