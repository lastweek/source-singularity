// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.IO;
using System.Text;

//
// This "Proto-Lisp" interpreter can evaluate simple LISP-like expressions.
// Proto-Lisp is lexically scoped (not dynamically scoped like the original
// LISP), and provides simple "closures". The idea of Proto-Lisp is to
// create a minimally powerful language to allow further refinements to
// be created on top of it. For example, you could write a more fully-
// featured LISP interpreter in Proto-Lisp.
//
// Currently, the interpreter has the following classic LISP primitives:
//
//          atom, eq, car, cdr, cons, cond
//
// In addition, (define <x> <y>) is provided, which binds the variable
// name x to the expression y in the global environment.
//
// Also, the (lambda (<arglist>) (<bodyexpr>)) primitive is provided.
// The lambda primitive creates a "closure" by capturing the lexical
// environment it is evaluated in. This lets you pull stunts like:
//
// (define multiplier (factor) (lambda (x) (* x factor)))
//
// evaluating "(multiplier 5)", say, returns a function that takes one
// argument and multiplies it by 5.
//
// (defun <name> (<arglist>) (<bodyexpr>)) is provided as syntactic
// sugar, signifying (define <name> (lambda (<arglist>) (<bodyexpr>)))
//

namespace ProtoLisp
{
    class Interpreter
    {
        private PLEnvironment globalEnv; // Top-level environment

        public Interpreter()
        {
            globalEnv = new PLEnvironment();
        }

        // Convert a C# boolean value to a ProtoLisp expression
        private PLObject BoolToExpr(bool b)
        {
            // True is "t", false is the empty list
            if (b) {
                return new PLStringAtom("t");
            }
            else {
                return new PLList();
            }
        }

        // Convert a ProtoLisp expression to a native C# bool value
        private bool ExprToBool(PLObject expr)
        {
            // Anything that is not "t" is false
            return ((expr is PLStringAtom) && (expr.Equals("t")));
        }

        // Write a string to a stream as ASCII
        private void StreamWriteLine(Stream stream, string text)
        {
            byte[] bytes = Encoding.ASCII.GetBytes(text + "\r\n");
            stream.Write(bytes, 0, bytes.Length);
        }

        //
        // ---------------- PRIMITIVE FUNCTIONS ----------------
        //

        // atom: indicates whether its (one) argument is an atom
        private PLObject atom_fun(PLObject expr)
        {
            // An atom is an object that is an instance of PLAtom, or
            // the empty list (considered "false")
            if (expr is PLAtom) {
                return BoolToExpr(true);
            }
            else if ((expr is PLList) && (((PLList)expr).Count == 0)) {
                return BoolToExpr(true);
            }

            return BoolToExpr(false);
        }

        // eq: indicates whether its (two) arguments are equal.
        private PLObject eq_fun(PLObject a, PLObject b)
        {
            if ((a is PLAtom) && (b is PLAtom)) {
                // Two atoms compare by value
                return BoolToExpr(a.Equals(b));
            }
            else {
                // Two empty lists are equal
                if ((a is PLList) && (((PLList)a).Count == 0) &&
                    (b is PLList) && (((PLList)b).Count == 0))
                {
                    return BoolToExpr(true);
                }
            }

            return BoolToExpr(false);
        }

        // car: returns the first value in a list
        private PLObject car_fun(PLList list)
        {
            return list[0];
        }

        // cdr: returns the remainder of a list
        private PLList cdr_fun(PLList list)
        {
            PLList retval = new PLList();

            for (int i = 1; i < list.Count; ++i) {
                retval.Add(list[i]);
            }

            return retval;
        }

        // cons: creates a list from an expression and an existing list
        private PLList cons_fun(PLObject a, PLList b)
        {
            PLList retval = new PLList();
            retval.Add(a);

            for (int i = 0; i < b.Count; ++i) {
                retval.Add(b[i]);
            }

            return retval;
        }

        // cond: examines a sequence of pairs. Its result is the second
        // item in the first pair whose first element evaluates to true.
        private PLObject cond_fun(PLList condPLList, PLEnvironment localEnv, Stream traceStream)
        {
            for (int i = 0; i < condPLList.Count; ++i) {
                if (!(condPLList[i] is PLList)) {
                    throw new Exception("An argument passed to the 'cond' primitive was not a list");
                }

                PLList condition = (PLList)condPLList[i];

                if (condition.Count != 2) {
                    throw new Exception("An argument passed to the 'cond' primitive was not a 2-item list");
                }

                PLObject carVal = Eval(car_fun(condition), localEnv, traceStream);

                if (ExprToBool(carVal)) {
                    // This subexpression evaluated to true. Evaluate
                    // the second part of the condition.
                    return Eval(condition[1], localEnv, traceStream);
                }
            }

            return BoolToExpr(false);
        }

        // define: Binds a name to an expression in the global context
        private PLObject define_fun(string name, PLObject obj)
        {
            globalEnv.Put(name, obj);
            return new PLStringAtom(name);
        }

        // lambda: Creates an evaluatable closure.
        private PLObject lambda_fun(PLList args, PLObject body, PLEnvironment env)
        {
            return new PLClosure(args, body, env);
        }

        //
        // Primitive arithmetic operations
        //
        private PLNumberAtom plus_fun(PLNumberAtom a, PLNumberAtom b)
        {
            return a + b;
        }

        private PLNumberAtom minus_fun(PLNumberAtom a, PLNumberAtom b)
        {
            return a - b;
        }

        private PLNumberAtom mult_fun(PLNumberAtom a, PLNumberAtom b)
        {
            return a * b;
        }

        private PLNumberAtom div_fun(PLNumberAtom a, PLNumberAtom b)
        {
            return a / b;
        }

        //
        // ---------------- end of primitives ----------------
        //

        // Execute a given closure, with a given set of argument values
        private PLObject Execute(PLClosure fun, PLList argVals, Stream traceStream)
        {
            if (traceStream != null) {
                StreamWriteLine(traceStream, "** Executing a closure...");
            }

            // Check the argument list
            if (fun.argNames.Count != argVals.Count) {
                throw new Exception ("Function invoked with wrong number of arguments");
            }

            // Augment the closure's environment with additional
            // entries that bind the argument values to their
            // symbolic names, then evaluate the function body.
            PLEnvironment funEnv;

            if (fun.env != null) {
                funEnv = (PLEnvironment)fun.env.Clone();
            }
            else {
                funEnv = new PLEnvironment();
            }

            for (int i = 0; i < fun.argNames.Count; ++i) {
                funEnv.Put(((PLStringAtom)fun.argNames[i]).ToString(), argVals[i]);
            }

            return Eval(fun.body, funEnv, traceStream);
        }

        // Apply the specified argument list to the function indicated
        // by the provided expression. The function expression may simply
        // be the symbolic name of a function, or it may be an evaluatable
        // expression in its own right.
        private PLObject Apply(PLObject func, PLList args, PLEnvironment localEnv, Stream traceStream)
        {
            if (traceStream != null) {
                StreamWriteLine(traceStream, "** Evaluating the expression \"" + ExpressionToString(func) + "\" as a function");
            }

            if (func is PLStringAtom) {
                // Function is named by a symbol

                if (func.Equals("atom")) {
                    if (args.Count != 1) {
                        throw new Exception("Incorrect number of arguments passed to the 'atom' primitive");
                    }

                    return atom_fun(args[0]);
                }
                else if (func.Equals("eq")) {
                    if (args.Count != 2) {
                        throw new Exception("Incorrect number of arguments passed to the 'eq' primitive");
                    }

                    return eq_fun(args[0], args[1]);
                }
                else if (func.Equals("car")) {
                    if (args.Count != 1) {
                        throw new Exception("Incorrect number of arguments passed to the 'car' primitive");
                    }

                    if (!(args[0] is PLList)) {
                        throw new Exception("The argument passed to the 'car' primitive was not a list");
                    }

                    return car_fun((PLList)args[0]);
                }
                else if (func.Equals("cdr")) {
                    if (args.Count != 1) {
                        throw new Exception("Incorrect number of arguments passed to the 'cdr' primitive");
                    }

                    if (!(args[0] is PLList)) {
                        throw new Exception("The argument passed to the 'cdr' primitive was not a list");
                    }

                    return cdr_fun((PLList)args[0]);
                }
                else if (func.Equals("cons")) {
                    if (args.Count != 2) {
                        throw new Exception("Incorrect number of arguments passed to the 'cons' primitive");
                    }

                    if (!(args[1] is PLList)) {
                        throw new Exception("The second argument passed to the 'cons' primitive was not a list");
                    }

                    return cons_fun(args[0], (PLList)args[1]);
                }
                else if (func.Equals("+")) {
                    if (args.Count != 2) {
                        throw new Exception("Incorrect number of arguments pass to the '+' primitive");
                    }

                    if (!(args[0] is PLNumberAtom) ||
                        !(args[1] is PLNumberAtom))
                    {
                        throw new Exception("Both arguments to the '+' primitive must be numbers");
                    }

                    return plus_fun((PLNumberAtom)args[0], (PLNumberAtom)args[1]);
                }
                else if (func.Equals("-")) {
                    if (args.Count != 2) {
                        throw new Exception("Incorrect number of arguments pass to the '-' primitive");
                    }

                    if (!(args[0] is PLNumberAtom) ||
                        !(args[1] is PLNumberAtom))
                    {
                        throw new Exception("Both arguments to the '-' primitive must be numbers");
                    }

                    return minus_fun((PLNumberAtom)args[0], (PLNumberAtom)args[1]);
                }
                else if (func.Equals("*")) {
                    if (args.Count != 2) {
                        throw new Exception("Incorrect number of arguments pass to the '*' primitive");
                    }

                    if (!(args[0] is PLNumberAtom) ||
                        !(args[1] is PLNumberAtom))
                    {
                        throw new Exception("Both arguments to the '*' primitive must be numbers");
                    }

                    return mult_fun((PLNumberAtom)args[0], (PLNumberAtom)args[1]);
                }
                else if (func.Equals("/")) {
                    if (args.Count != 2) {
                        throw new Exception("Incorrect number of arguments pass to the '/' primitive");
                    }

                    if (!(args[0] is PLNumberAtom) ||
                        !(args[1] is PLNumberAtom))
                    {
                        throw new Exception("Both arguments to the '/' primitive must be numbers");
                    }

                    return div_fun((PLNumberAtom)args[0], (PLNumberAtom)args[1]);
                }

                // The name does not indicate a built-in primitive.
                // Look up the function in our environment
                PLObject funObj = Lookup(func.ToString(), localEnv);

                if (!(funObj is PLClosure)) {
                    throw new Exception ("The symbolic name \"" + func + "\" is not bound to a function");
                }

                // Run the function!
                return Execute((PLClosure)funObj, args, traceStream);
            }
            else {
                // The function is an expression, not just a name. This expression
                // had better evaluate to a closure.
                PLObject funObj = Eval(func, localEnv, traceStream);

                if (!(funObj is PLClosure)) {
                    throw new Exception ("Expression \"" + ExpressionToString(func) + "\" does not evaluate to a function");
                }

                // Run this function expression
                return Execute((PLClosure)funObj, args, traceStream);
            }
        }

        // Evaluate a list of expressions. Return a new list that gives the
        // value for each expression.
        private PLList EvalPLList(PLList list, PLEnvironment localEnv, Stream traceStream)
        {
            PLList retval = new PLList();

            for (int i = 0; i < list.Count; ++i) {
                retval.Add(Eval(list[i], localEnv, traceStream));
            }

            return retval;
        }

        // Look up the value that a symbolic name is bound to; check the
        // provided local environment as well as the global environment.
        private PLObject Lookup(string name, PLEnvironment localEnv)
        {
            PLObject retval;

            if (localEnv != null) {
                retval = localEnv.Lookup(name);

                if (retval != null) {
                    return retval;
                }
            }

            return globalEnv.Lookup(name);
        }

        public PLObject Eval(PLObject expr, PLEnvironment localEnv, Stream traceStream)
        {
            if (traceStream != null) {
                StreamWriteLine(traceStream, "** Evaluating: " + ExpressionToString(expr));
            }

            if (expr is PLAtom) {
                PLAtom atomExpr = (PLAtom)expr;

                if (atomExpr is PLNumberAtom) {
                    // Numbers eval to themselves
                    return atomExpr;
                }
                else {
                    if (atomExpr.Equals("t")) {
                        // "t" (True) evals to itself
                        return atomExpr;
                    }
                    else if (atomExpr.Equals("nil")) {
                        // Return whatever our native representation for false is
                        return BoolToExpr(false);
                    }
                    else {
                        PLObject retval = Lookup(atomExpr.ToString(), localEnv);

                        if (retval == null) {
                            throw new Exception("The symbolic name \"" + atomExpr + "\" is not bound.");
                        }

                        return retval;
                    }
                }
            }
            else if (expr is PLList) {
                PLList listExpr = ((PLList)expr);

                // The empty list evaluates to itself
                if (listExpr.Count == 0) {
                    return listExpr;
                }

                PLObject carVal = car_fun(listExpr);

                // Check for special-case primitives
                if (carVal is PLStringAtom) {
                    if (carVal.Equals("cond")) {
                        if (listExpr.Count < 2) {
                            throw new Exception("Must pass at least one argument to the 'cond' primitive");
                        }

                        return cond_fun(cdr_fun(listExpr), localEnv, traceStream);
                    }
                    else if (carVal.Equals("quote")) {
                        if (listExpr.Count != 2) {
                            throw new Exception("Incorrect number of arguments passed to the 'quote' primitive");
                        }

                        // Return the second portion of the list
                        return listExpr[1];
                    }
                    else if (carVal.Equals("define")) {
                        if (listExpr.Count != 3) {
                            throw new Exception ("Incorrect number of arguments passed to the 'define' primitive");
                        }

                        if (!(listExpr[1] is PLStringAtom)) {
                            throw new Exception ("The first argument passed to the 'define' primitive was not a string");
                        }

                        return define_fun(((PLStringAtom)listExpr[1]).ToString(),
                                          Eval(listExpr[2], localEnv, traceStream));
                    }
                    else if (carVal.Equals("lambda")) {
                        if (listExpr.Count != 3) {
                            throw new Exception ("Incorrect number of arguments passed to the 'lambda' primitive");
                        }

                        if (!(listExpr[1] is PLList)) {
                            throw new Exception ("The first argument to the 'lambda' primitive was not a list");
                        }

                        return lambda_fun((PLList)listExpr[1], listExpr[2], localEnv);
                    }
                    else if (carVal.Equals("defun")) {
                        // Syntactic sugar for (define <name> (lambda ...
                        if (listExpr.Count != 4) {
                            throw new Exception ("Incorrect number of arguments passed to the 'defun' primitive");
                        }

                        if (!(listExpr[1] is PLStringAtom)) {
                            throw new Exception ("The first argument passed to the 'defun' primitive was not a simple name");
                        }

                        if (!(listExpr[2] is PLList)) {
                            throw new Exception ("The second argument passed to the 'defun' argument was not a list");
                        }

                        return define_fun(((PLStringAtom)listExpr[1]).ToString(),
                                          lambda_fun((PLList)listExpr[2], listExpr[3], localEnv));
                    }
                }

                // Assume a general function invocation. Evaluate all the
                // arguments and invoke.
                PLList args = EvalPLList(cdr_fun(listExpr), localEnv, traceStream);
                return Apply(listExpr[0], args, localEnv, traceStream);
            }
            else {
                throw new Exception("Unrecognized type passed to Eval()");
            }
        }

        // Turn a ProtoLisp expression into a printable string
        public static string ExpressionToString(PLObject obj)
        {
            if (obj is PLStringAtom) {
                return ((PLStringAtom)obj).ToString();
            }

            else if (obj is PLNumberAtom) {
                return ((PLNumberAtom)obj).ToString();
            }

            else if (obj is PLList) {
                PLList list = (PLList)obj;
                string retval = "(";

                for (int i = 0; i < list.Count; ++i) {
                    retval += ExpressionToString(list[i]);

                    if (i < list.Count - 1) {
                        retval += " ";
                    }
                }

                retval += ")";
                return retval;
            }
            else if (obj is PLClosure) {
                return "<<closure>>";
            }
            else {
                return "???";
            }
        }
    }
}
