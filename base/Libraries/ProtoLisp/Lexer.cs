// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Text;
using System.IO;
using System.Diagnostics;

//
// The Lexer class tokenizes an input stream of text
// and can also read off complete Proto-Lisp expressions
// for evaluation.
//
// The lexer has a one-character lookahead buffer.
//
namespace ProtoLisp
{
    class Lexer
    {
        // Constructor
        public Lexer(Stream stream)
        {
            inputStream = stream;
            haveLookAhead = false;
        }

        // Returns the next character in the input stream.
        // The stream is not (conceptually) advanced.
        // Calling PeekNextChar or GetNextChar will
        // return the same character.
        //
        // Returns null if the end of the stream has been
        // reached.
        private bool PeekNextChar(out char val)
        {
            if (haveLookAhead) {
                val = lookAheadVal;
                return true;
            }
            else {
                int nextVal = inputStream.ReadByte();

                if (nextVal == -1) {
                    // Nothing more to read
                    val = '\0';
                    return false;
                }
                else {
                    haveLookAhead = true;
                    // Hacky cast: just assume everything is 1-byte ASCII
                    lookAheadVal = (char)nextVal;
                    val = lookAheadVal;
                    return true;
                }
            }
        }

        // Retrieves the next character, and advances the stream.
        // Returns null if the end has already been reached.
        private bool GetNextChar(out char val)
        {
            char dummy;

            if (!PeekNextChar(out dummy)) {
                val = '\0';
                return false;
            }

            Debug.Assert(haveLookAhead);
            val = lookAheadVal;
            haveLookAhead = false;
            return true;
        }

        // Advances the stream without returning the current
        // character.
        private void DiscardNextChar()
        {
            char dummyChar;
            GetNextChar(out dummyChar);
        }

        // Get the next token.
        private string GetToken()
        {
            char peekChar;

            // Skip whitespace
            if (!PeekNextChar(out peekChar)) {
                return null;
            }

            while (Char.IsWhiteSpace(peekChar)) {
                // Throw away the whitespace char
                DiscardNextChar();
                if (!PeekNextChar(out peekChar)) {
                    return null;
                }
            }

            // Special one-character tokens
            if ((peekChar == '(') || (peekChar == ')') || (peekChar == '\'')) {
                // Consume and return this character
                DiscardNextChar();
                return new String(peekChar, 1);
            }

            String token = "";

            do
            {
                token += peekChar;
                DiscardNextChar();

                if (!PeekNextChar(out peekChar)) {
                    // Ran into the end of the stream
                    return token;
                }
            } while ((!Char.IsWhiteSpace(peekChar)) && (peekChar != '(') && (peekChar != ')'));

            return token;
        }

        public PLObject GetExpression()
        {
            string token = GetToken();

            if (token == null) {
                return null;
            }

            if (token.Equals("'")) {
                // The "'" character means "quote", and preserve
                // the next expression.
                PLList retval = new PLList();
                retval.Add(new PLStringAtom("quote"));

                PLObject nextExpr = GetExpression();

                if (nextExpr == null) {
                    throw new Exception("'quote' was not followed by a complete expression");
                }

                retval.Add(nextExpr);
                return retval;
            }

            if  (!token.Equals("(")) {
                // Not the beginning of a list; the expression is
                // simply this token. See if it's a number or a
                // plain string.
                try {
                    return new PLNumberAtom(token);
                }
                catch (Exception) {
                    // Just treat it as a regular string
                    return new PLStringAtom(token);
                }
            }
            else {
                // We have the beginning of a list, which can contain
                // any number of expressions. Keep building our list
                // until we encounter the closing paren.
                PLList retval = new PLList();

                PLObject nextExpr = GetExpression();

                while (! nextExpr.Equals(")")) {
                    retval.Add(nextExpr);

                    nextExpr = GetExpression();

                    if (nextExpr == null) {
                        throw new Exception("Incomplete expression (unbalanced parens?");
                    }
                }

                return retval;
            }
        }

        private Stream inputStream;
        private bool haveLookAhead;
        private char lookAheadVal;
    }
}
