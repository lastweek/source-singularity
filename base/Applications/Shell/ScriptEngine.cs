// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Text.RegularExpressions;
using System.Text;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Contracts;

namespace Microsoft.Singularity.Applications
{
    ///
    // Provides a reasonable script engine implementation.
    // This engine is composed of two distinct parts: the parser
    // and the interpreter. Parser.cs and ScriptParser.cs provide
    // the parsing functionality. Parser.cs is the general handwritten slr
    // driver while ScriptParser contains the automatically generated
    // parse tables and semantic action functions for productions
    // and lex operations of this specific scripting language. This file
    // provides the interpretation mechanism that runs over an ast produced
    // by the parser.
    //  
    class ScriptEngine
    {
        private String script;
        private Block parsedScript;
        public const String LAST_COMMAND_EXIT_SYMBOL = "?";
        public const String NUM_ARGUMENTS_SYM = "#";
        public delegate int CommandLineRunner(ShellControl! shellControl, 
                                              String[] commandLine, 
                                              bool isBackground);

        private CommandLineRunner runner;


        public static int Run(String script, ShellControl! shellControl, CommandLineRunner runner)
        {
            return Run(script, shellControl, runner, null);
        }

        public static int Run(String script, ShellControl! shellControl,
                              CommandLineRunner runner, String[] arguments)
        {
            ScriptEngine engine = new ScriptEngine(script, runner);
            try {
                engine.Parse();
            }
            catch (Parser.ParseException e) {
                Console.WriteLine(e.Message);
                return -1;
            }
            catch (Exception e) {
                Console.WriteLine(e.Message);
                return -1;
            }

            try {
                return engine.Run(shellControl, arguments);
            }
            catch (Interpretation.InterpretationException e) {
                Console.WriteLine(e.Message);
            }
            catch (ScriptException e) {
                Console.WriteLine(e.Message);
            }
            catch (Exception e) {
                Console.WriteLine(e.Message);
            }
            return -1;
        }


        private ScriptEngine(String script, CommandLineRunner runner)
        {
            this.script = script;
            this.runner = runner;
        }

        private void Parse()
        {
            ScriptParser parser = new ScriptParser();
            parsedScript = (Block)parser.Parse(script);

        }

        private int Run(ShellControl! shellControl, String[] arguments)
        {
            Interpretation interp = new Interpretation(runner, arguments);
            parsedScript.Interpret(shellControl, interp);
            return interp.ExitCode;
        }

        public class ScriptException : Exception
        {
            public ScriptException(String message) : base(message) { }
        }

        public class Interpretation
        {
            public static readonly object! undefinedObj = new Object();
            private Hashtable! symbolTable;
            private bool exit = false;

            [NotDelayed]
            public Interpretation(CommandLineRunner runner, String[] arguments)
            {
                this.runner = runner;
                symbolTable = new Hashtable();
                base();
                int i = 0;
                if (arguments != null) {
                    for (; i < arguments.Length; ++i) {
                        SetSymbol(i.ToString(), arguments[i]);
                    }
                }
                SetSymbol(NUM_ARGUMENTS_SYM, i);
            }

            public int ExitCode
            {
                get {
                    Object exitCode = LookupSymbol(LAST_COMMAND_EXIT_SYMBOL);
                    if (exitCode == null) {
                        return 0;
                    }
                    return (Int32) exitCode; 
                }
                set { SetSymbol(LAST_COMMAND_EXIT_SYMBOL, value); }
            }

            public bool Exit
            {
                get { return exit; }
                set { exit = value; }
            }

            public CommandLineRunner runner;

            public object! LookupSymbol(string! symbol)
            {
                Object value = symbolTable[symbol];
                if (value == null) {
                    return undefinedObj;
                }
                return value;
            }
            public void SetSymbol(string! key, Object value)
            {
                symbolTable[key] = value;
            }

            public class InterpretationException : Exception
            {
                public InterpretationException(String message) : base(message) { }
            }

            public class UndefinedVariableException : InterpretationException
            {
                public UndefinedVariableException(String variable)
                    : base("Use of undefined variable: " + variable) { }
            }

            public class TypeConversionException : InterpretationException
            {
                public TypeConversionException(String value, String type)
                    : base("Could not convert " + value + " to type: " + type) { }
            }

            public class UnknownTypeException : InterpretationException
            {
                public UnknownTypeException(String type)
                    : base("Unknown type" + type) { }
            }

            public class DivideByZeroException : InterpretationException
            {
                public DivideByZeroException() : base("Division by zero undefined.") { }
            }

           
        }
        public abstract class Element { }

        public abstract class Expression : Element
        {
            public abstract object! GetValue(Interpretation! interp);
            public abstract string! StringValue(Interpretation! interp);
            public abstract int IntValue(Interpretation! interp);
            public abstract bool BoolValue(Interpretation! interp);
            public bool IsIntLike() { return true; }
            public bool IsBoolLike() { return true; }
            public bool IsStringLike() { return true; }
        }

        public class VariableReference : Expression
        {
            String variable;
            public VariableReference(String variable)
            {
                this.variable = variable;
            }
            public override object! GetValue(Interpretation! interp)
            {
                object value = interp.LookupSymbol(variable);
                if (value == Interpretation.undefinedObj)
                    throw new Interpretation.UndefinedVariableException(variable);
                return value;
            }

            public override string! StringValue(Interpretation! interp)
            {
                object value = GetValue(interp);
                return value.ToString();
            }

            public override int IntValue(Interpretation! interp)
            {
                Object value = GetValue(interp);
                if (value is String) {
                    return Int32.Parse((String)value);
                }
                else if (value is Int32) {
                    return (int)value;
                }
                else if (value is bool) {
                    return ((bool)value) ? 1 : 0;
                }
                throw new Interpretation.UnknownTypeException(value.GetType().ToString());
            }

            public override bool BoolValue(Interpretation! interp)
            {
                Object value = GetValue(interp);
                if (value is String) {
                    try {
                        return Boolean.Parse((String)value);
                    }
                    catch (FormatException) {
                        throw new Interpretation.TypeConversionException((String)value, "bool");
                    }

                }
                else if (value is Int32) {

                    return ((int)value) == 0 ? true : false;
                }
                else if (value is Boolean) {
                    return (bool)value;
                }
                throw new Interpretation.UnknownTypeException(value.GetType().ToString());
            }
        }

        public abstract class IntegerExpression : Expression
        {
            public override object! GetValue(Interpretation! interp) { return IntValue(interp); }
            public override string! StringValue(Interpretation! interp)
            {
                int value = IntValue(interp);
                return value.ToString();
            }
            public override bool BoolValue(Interpretation! interp)
            {
                int value = IntValue(interp);
                return value == 0 ? true : false;
            }
        }

        public class IntegerLiteral : IntegerExpression
        {
            private int value;
            public IntegerLiteral(int value)
            {
                this.value = value;
            }
            public override int IntValue(Interpretation! interp) { return value; }
        }
        public abstract class IntegerBinaryExpression : IntegerExpression
        {
            public Expression left;
            public Expression right;
            protected IntegerBinaryExpression(Expression left, Expression right)
            {
                this.left = left; this.right = right;
            }
        }
        public class Add : IntegerBinaryExpression
        {
            public Add(Expression left, Expression right) : base(left, right) { }
            public override int IntValue(Interpretation! interp)
            {
                return left.IntValue(interp) + right.IntValue(interp);
            }
        }
        public class Subtract : IntegerBinaryExpression
        {
            public Subtract(Expression left, Expression right) : base(left, right) { }
            public override int IntValue(Interpretation! interp)
            {
                return left.IntValue(interp) - right.IntValue(interp);
            }
        }

        public class Multiply : IntegerBinaryExpression
        {
            public Multiply(Expression left, Expression right) : base(left, right) { }
            public override int IntValue(Interpretation! interp)
            {
                return left.IntValue(interp) * right.IntValue(interp);
            }
        }

        public class Divide : IntegerBinaryExpression
        {
            public Divide(Expression left, Expression right) : base(left, right) { }
            public override int IntValue(Interpretation! interp)
            {
                int leftVal = left.IntValue(interp);
                int rightVal = right.IntValue(interp);
                if (rightVal == 0) {
                    throw new DivideByZeroException();
                }
                return leftVal / rightVal;

            }
        }

        public class Mod : IntegerBinaryExpression
        {
            public Mod(Expression left, Expression right) : base(left, right) { }
            public override int IntValue(Interpretation! interp)
            {
                return left.IntValue(interp) % right.IntValue(interp);
            }
        }
        public abstract class BooleanExpression : Expression
        {
            public override object! GetValue(Interpretation! interp) { return BoolValue(interp); }
            public override int IntValue(Interpretation! interp)
            {
                bool value = BoolValue(interp);
                return value ? 1 : 0;
            }
            public override string! StringValue(Interpretation! interp)
            {
                bool value = BoolValue(interp);
                return value.ToString();
            }
        }

        public class BooleanLiteral : BooleanExpression
        {
            bool value;
            public BooleanLiteral(bool value)
            {
                this.value = value;
            }
            public override bool BoolValue(Interpretation! interp) { return value; }

        }
        public abstract class BooleanBinaryExpression : BooleanExpression
        {
            protected Expression left;
            protected Expression right;
            public BooleanBinaryExpression(Expression left, Expression right)
            {
                this.left = left; this.right = right;
            }
            protected int CompareOperands(Interpretation! interp)
            {
                return CompareTo(left.GetValue(interp), right, interp);
            }
            private static int CompareTo(Object left, Expression e, Interpretation! interp)
            {
                if (left == null) {
                    if (e == null) {
                        return 0;
                    }
                    return -1;
                }
                if (e == null) {
                    return 1;
                }
                if (left is String) {
                    return ((String)left).CompareTo(e.StringValue(interp));
                }
                else if (left is int) {
                    return ((int)left).CompareTo(e.IntValue(interp));
                }
                else if (left is Boolean) {
                    return ((Boolean)left).CompareTo(e.BoolValue(interp));
                }
                throw new Interpretation.UnknownTypeException("unsupported type");
            }
        }
        public class And : BooleanBinaryExpression
        {
            public And(Expression left, Expression right) : base(left, right) { }

            public override bool BoolValue(Interpretation! interp)
            {
                return left.BoolValue(interp) && right.BoolValue(interp);
            }
        }

        public class Or : BooleanBinaryExpression
        {
            public Or(Expression left, Expression right) : base(left, right) { }
            public override bool BoolValue(Interpretation! interp)
            {
                return left.BoolValue(interp) || right.BoolValue(interp);
            }
        }

        public class Less : BooleanBinaryExpression
        {
            public Less(Expression left, Expression right) : base(left, right) { }
            public override bool BoolValue(Interpretation! interp)
            {
                int compare = CompareOperands(interp);
                return compare < 0;
            }
        }

        public class LessEqual : BooleanBinaryExpression
        {
            public LessEqual(Expression left, Expression right) : base(left, right) { }
            public override bool BoolValue(Interpretation! interp)
            {
                int compare = CompareOperands(interp);
                return compare < 0 || compare == 0;
            }
        }

        public class Equal : BooleanBinaryExpression
        {
            public Equal(Expression left, Expression right) : base(left, right) { }
            public override bool BoolValue(Interpretation! interp)
            {
                int compare = CompareOperands(interp);
                return compare == 0;
            }
        }

        public class Greater : BooleanBinaryExpression
        {
            public Greater(Expression left, Expression right) : base(left, right) { }
            public override bool BoolValue(Interpretation! interp)
            {
                int compare = CompareOperands(interp);
                return compare > 0;
            }
        }

        public class GreaterEqual : BooleanBinaryExpression
        {
            public GreaterEqual(Expression left, Expression right) : base(left, right) { }
            public override bool BoolValue(Interpretation! interp)
            {
                int compare = CompareOperands(interp);
                return compare == 0 || compare > 0;
            }
        }


        public class Negate : BooleanExpression
        {
            Expression expr;
            public Negate(Expression expr)
            {
                this.expr = expr;
            }
            public override bool BoolValue(Interpretation! interp)
            {
                return !expr.BoolValue(interp);
            }
        }

        public abstract class StringExpression : Expression
        {
            public override object! GetValue(Interpretation! interp)
            {
                return StringValue(interp);
            }
            public override int IntValue(Interpretation! interp)
            {
                String value = StringValue(interp);
                try {
                    return Int32.Parse(value);
                }
                catch (FormatException) {
                    throw new Interpretation.TypeConversionException(value, "String");
                }
            }

            public override bool BoolValue(Interpretation! interp)
            {
                String value = StringValue(interp);
                try {
                    return Boolean.Parse(value);
                }
                catch (FormatException) {
                    throw new Interpretation.TypeConversionException(value, "String");
                }
            }
        }
        private static Regex whitespace = new Regex(@"\s+");

        public class StringInterpolation : StringExpression
        {
            private ArrayList interpolationElems;
            private static Regex escaped_dollar = new Regex(@"\\\$");

            private static String[]! Split(string! interpolation)
            {
                ArrayList chunks = new ArrayList();
                char last = (char) -1;
                int lastIndex = 0;
                for (int i = 0; i < interpolation.Length; last = interpolation[i], ++i) {
                    if (interpolation[i] == '$' && last != '\\') {
                        chunks.Add(interpolation.Substring(lastIndex, i - lastIndex));
                        lastIndex = i + 1;
                    }
                }
                chunks.Add((lastIndex < interpolation.Length - 1 ? interpolation.Substring(lastIndex) : ""));
                String[] strings = new string[chunks.Count];
                chunks.CopyTo(strings);
                return strings;
            }

            [NotDelayed]
            public StringInterpolation(string! interpolation)
            {
                interpolationElems = new ArrayList();
                String[] split = Split(interpolation);
                if (split[0] != "") {
                    //replace escaped $ and add
                    interpolationElems.Add(new StringLiteral(escaped_dollar.Replace(split[0], "$")));
                }
                for (int i = 1; i < split.Length; ++i) {
                    string var, rest;
                    string! split_i = (!)split[i];
                    if (split_i[0] == '{') {
                        int index = split_i.IndexOf('}');
                        if (index == -1) {
                            throw new ScriptException("Unmatched left brace in " + interpolation);
                        }
                        var = split_i.Substring(1, index - 1);
                        rest = index + 1 < split_i.Length ? split_i.Substring(index + 1) : "";
                    }
                    else {
                        Match m = whitespace.Match(split_i);
                        assert m != null;
                        int index = m.Success ? m.Index : split_i.Length;
                        var = split_i.Substring(0, index);
                        rest = index + 1 < split_i.Length ? split_i.Substring(index + 1) : "";
                    }
                    //didn't replace escaped dollar signs in variable, bad syntax anyway.
                    interpolationElems.Add(new VariableReference(var));
                    if (rest != "") {
                        interpolationElems.Add(new StringLiteral(escaped_dollar.Replace(rest, "$")));

                    }
                }
            }

            public override string! StringValue(Interpretation! interp)
            {
                StringBuilder sb = new StringBuilder();
                foreach (Expression! elem in interpolationElems) {
                    sb.Append(elem.StringValue(interp));
                }
                return sb.ToString();
            }
        }
        public class StringLiteral : StringExpression
        {
            private string literal;
            public StringLiteral(String literal)
            {
                this.literal = literal;
            }
            public override string! StringValue(Interpretation! interp)
            {
                return literal;

            }
        }

        public class Concat : StringExpression
        {
            private Expression left;
            private Expression right;
            public Concat(Expression left, Expression right)
            {
                this.left = left; this.right = right;
            }

            public override string! StringValue(Interpretation! interp)
            {
                return left.StringValue(interp) + right.StringValue(interp);
            }
        }

        public abstract class Statement : Element
        {
            public abstract void Interpret(ShellControl! shellControl, Interpretation! interp);
        }

        public class Assign : Statement
        {
            String variable;
            Expression expression;
            public Assign(String variable, Expression expression)
            {
                this.variable = variable; this.expression = expression;
            }
            public override void Interpret(ShellControl! shellControl, Interpretation! interp)
            {
                Object value = expression.GetValue(interp);
                if (interp != null)
                    interp.SetSymbol(variable, value);
            }
        }
        public class If : Statement
        {
            Expression condition;
            Block block;
            public If(Expression condition, Block block)
            {
                this.condition = condition; this.block = block;
            }
            public override void Interpret(ShellControl! shellControl, Interpretation! interp)
            {
                if (condition.BoolValue(interp)) {
                    block.Interpret(shellControl, interp);
                }
            }
        }
        public class IfThenElse : Statement
        {
            Expression condition;
            Block trueBlock;
            Block falseBlock;
            public IfThenElse(Expression condition, Block trueBlock, Block falseBlock)
            {
                this.condition = condition; this.trueBlock = trueBlock; this.falseBlock = falseBlock;
            }
            public override void Interpret(ShellControl! shellControl, Interpretation! interp)
            {
                if (condition.BoolValue(interp)) {
                    trueBlock.Interpret(shellControl, interp);
                }
                else {
                    falseBlock.Interpret(shellControl, interp);
                }
            }
        }

        public class While : Statement
        {
            Expression condition;
            Block block;
            public While(Expression condition, Block block)
            {
                this.condition = condition; this.block = block;
            }
            public override void Interpret(ShellControl! shellControl, Interpretation! interp)
            {
                while (condition.BoolValue(interp)) {
                    block.Interpret(shellControl, interp);
                    if (interp.Exit) break;
                }
            }
        }
        public class Block : Statement
        {
            ArrayList statements;
            public Block(ArrayList statements)
            {
                this.statements = statements;
            }
            public override void Interpret(ShellControl! shellControl, Interpretation! interp)
            {
                foreach (Statement statement in statements) {
                    if (statement != null)
                        statement.Interpret(shellControl, interp);
                    if (interp.Exit) break;
                }
            }
            public override string! ToString()
            {
                throw new ScriptException("The method or operation is not implemented.");
            }
        }

        public class Command : Statement
        {
            public ArrayList commandLine;
            bool async;

            public Command(ArrayList commandLine) : this(commandLine, false) { }
            public Command(ArrayList commandLine, bool async)
            {
                this.commandLine = commandLine;
                this.async = async;
            }
            public override void Interpret(ShellControl! shellControl, Interpretation! interp)
            {
                String[] arguments = new String[commandLine.Count];
                int i = 0;
                //Console.WriteLine("Interpret Command");
                foreach (Expression! e in commandLine) {
                    string arg = e.StringValue(interp);
                    //Console.WriteLine("  CMD[{0}]: {1}", i, arg);
                    arguments[i++] = arg;
                }
                if (i != 0 && ((!)arguments[0]).Trim() == "exit") {
                    if (arguments.Length >= 2) {
                        try {
                            int exitCode = Int32.Parse(arguments[1]);
                            interp.ExitCode = exitCode;
                        }
                        catch (FormatException) {
                            throw new Interpretation.TypeConversionException((String)arguments[1], "integer");
                        }
                    }
                    interp.Exit = true;
                }
                else if (false) {
                    //
                    //arguments[0].Trim() == "read") {
                    //string input = Console.ReadLine();
                    //String[] split = whitespace.Split(input);
                    //for (int j = 1, k = 0; j < arguments.Length && k < split.Length; ++j, ++k) {
                    //interp.SetSymbol(arguments[j], split[k]);
                    //
                }
                else {
                    int exitCode = interp.runner(shellControl, arguments, async);
                    interp.ExitCode = exitCode;
                }
            }
        }
    }
}
