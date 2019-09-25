// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Text;
using System.IO;

namespace ProtoLisp
{
    class Engine
    {
        private Interpreter interpreter;

        public Engine()
        {
            interpreter = new Interpreter();
        }

        public string EvalAll(string lispExpr, bool printEveryExpression, bool debugTrace)
        {
            MemoryStream stream = new MemoryStream(Encoding.ASCII.GetBytes(lispExpr));
            return EvalAll(stream, printEveryExpression, debugTrace);
        }

        public string EvalAll(Stream stream, bool printEveryExpression, bool debugTrace)
        {
            MemoryStream outputStream = new MemoryStream();
            StreamWriter writer = new StreamWriter(outputStream);

            Lexer lexer = new Lexer(stream);
            PLObject lastVal = null;

            try {
                PLObject obj;

                while ((obj = lexer.GetExpression()) != null) {
                    if (debugTrace) {
                        lastVal = interpreter.Eval(obj, null, outputStream);
                    }
                    else {
                        lastVal = interpreter.Eval(obj, null, null);
                    }

                    if (printEveryExpression) {
                        writer.WriteLine(Interpreter.ExpressionToString(lastVal));
                        writer.Flush();
                    }
                }
            }
            catch (Exception e) {
                writer.WriteLine("Exception caught: " + e);
            }

            if (!printEveryExpression) {
                writer.WriteLine(Interpreter.ExpressionToString(lastVal));
            }

            writer.Flush();

            int length = (int)outputStream.Length;
            return Encoding.ASCII.GetString(outputStream.GetBuffer(), 0, length);
        }
    }
}
