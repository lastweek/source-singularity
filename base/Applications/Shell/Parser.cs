// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Text.RegularExpressions;
using Microsoft.Contracts;

namespace Microsoft.Singularity.Applications
{
    ///
    // This is a general lr parser driver.
    // Parses the programming by first lexing it into a number
    // of tokens for a token stack. Then parser then pops tokens off
    // this stack, consults the parse tables and push the corresponding
    // nonterminals and states on the operand stack. This is the same
    // algorithm from the dragon book with some tweaks to support optional
    // tokens (i.e. newlines).
    //  
    abstract class Parser
    {
        private const int END_INPUT_MARKER_ID = 2;

        protected abstract Action[,]! ActionTable { get; }
        protected abstract State[,]! GotoTable { get; }
        protected abstract Production[]! ProductionTable { get; }
        protected abstract TokenType[]! TokenList { get; }


        public class ParseException : Exception
        {
            public ParseException(Token! token, string! error)
                : base("Parse error on line " + token.lineNumber + ", char " + token.charIndex + ": " + error) { }
        }

        public Object Parse(string! input)
        {
            Stack leftStack = new Stack();
            leftStack.Push(new State(0));

            ArrayList list = Lex(ref input);
            list.Reverse(); //could return a stack out of lex instead
            Stack rightStack = new Stack(list);
            while (rightStack.Count != 0) {
                State st = (State!)leftStack.Pop();
                Token tok = (Token!)rightStack.Pop();
                Action action = ActionTable[st.id, tok.id];
                while (tok.optional && action == null && rightStack.Count != 0) {
                    tok = (Token!)rightStack.Pop();
                    action = ActionTable[st.id, tok.id];
                }

                if (action == null) {
                    if (tok.id == END_INPUT_MARKER_ID) {
                        throw new ParseException(tok, " unexpected EOF");
                    }
                    throw new ParseException(tok, "'" + tok.value + "' unexpected input");
                }

                if (action.type == ActionType.SHIFT) {
                    leftStack.Push(st);
                    leftStack.Push(tok);
                    leftStack.Push(new State(action.stateOrProduction));
                }
                else if (action.type == ActionType.REDUCE) {
                    Production production = (!)ProductionTable[action.stateOrProduction];
                    Object value = production.Reduction(leftStack);
                    StackElement topLeft = (StackElement)leftStack.Pop();
                    State previousState;
                    if (topLeft is State) {
                        previousState = (State)topLeft;
                    }
                    else {
                        leftStack.Push(topLeft);
                        previousState = st; // took an epsilon transition   
                    }
                    State nextState = GotoTable[previousState.id, production.NonterminalType];
                    if (nextState == null) throw new Exception("missing state");
                    leftStack.Push(previousState);
                    leftStack.Push(new Nonterminal(production.NonterminalType, value));
                    leftStack.Push(nextState);
                    rightStack.Push(tok);
                }
                else if (action.type == ActionType.ACCEPT) {
                    break;
                }
            }
            Nonterminal result = (Nonterminal!)leftStack.Pop();
            return result.value;
        }

        private static int CountOccurrences(string! input, char c, out int last)
        {
            int count = 0;
            last = -1;
            for (int i = 0; i < input.Length; ++i) {
                if (c == input[i]) {
                    ++count;
                    last = i;
                }
            }
            return count;
        }

        private static bool IsNewLine(char t) { return t == '\n'; }
        public ArrayList! Lex(ref string! input)
        {
            ArrayList tokens = new ArrayList();
            int lineNumber = 1;
            int charIndex = 1;
        outer:
            while (input.Length != 0) {
                foreach (TokenType! spec in TokenList) {
                    Match! match = (!)spec.Regex.Match(input);
                    if (match == null || !match.Success) continue;
                    input = input.Remove(0, ((!)match.Value).Length);
                    if (spec.Lexer != null) {
                        Token token = new Token(spec.Type, match.Value, lineNumber, charIndex);
                        spec.Lexer(token);
                        if (token.value != null)
                            tokens.Add(token);
                    }
                    else {
                        tokens.Add(new Token(spec.Type, match.Value, lineNumber, charIndex));
                    }
                    int lastIndex;
                    int occurrences = CountOccurrences(match.Value, '\n', out lastIndex);
                    if (occurrences > 0) {
                        lineNumber += occurrences;
                        charIndex = match.Value.Length - (lastIndex + 1);
                    }
                    else {
                        charIndex += match.Value.Length;
                    }
                    goto outer;
                }
                throw new Exception("unknown input: " + input);
            }
            tokens.Add(new Token(END_INPUT_MARKER_ID, null, lineNumber, charIndex));
            return tokens;
        }

        public delegate Object Reducer(Stack! stack);
        public delegate void Lexer(Token! tok);

        public class Production
        {
            public readonly int NonterminalType;
            public readonly Reducer Reduction;
            public Production(int nonterminalType, [Delayed] Reducer reduction)
            {
                this.NonterminalType = nonterminalType;
                this.Reduction = reduction;
            }
        }

        public class StackElement
        {
            public readonly int id;
            public Object value;
            public StackElement(int id) { this.id = id; }
#if false
            // Error: Bartok can not handle complicated override pattern of System.Object.ToString.  [Specifically, it was overridden via a MethodImpl or replaced via interface method reimplementation, effectively merging two virtual slots.  Then the original slot was overridden by Microsoft.Singularity.Applications.Parser.Token.ToString, effectively splitting the slots again.  Bartok currently can not analyze the split.]
            public override string! ToString()
            {
                return id.ToString();
            }
#endif
        }
        public class State : StackElement
        {
            public State(int number) : base(number) { }

        }
        public class Token : StackElement
        {
            public readonly int lineNumber;
            public readonly int charIndex;
            public bool optional = false;
            public Token(int type, Object value, int lineNumber, int charIndex)
                : base(type)
            {
                this.value = value;
                this.lineNumber = lineNumber;
                this.charIndex = charIndex;
                this.optional = optional;
            }

#if false
            // Error: Bartok can not handle complicated override pattern of System.Object.ToString.  [Specifically, it was overridden via a MethodImpl or replaced via interface method reimplementation, effectively merging two virtual slots.  Then the original slot was overridden by Microsoft.Singularity.Applications.Parser.Token.ToString, effectively splitting the slots again.  Bartok currently can not analyze the split.]
            public override string! ToString()
            {
                return value + ":" + id;
            }
#endif
        }
        private class Nonterminal : StackElement
        {
            public Nonterminal(int type, Object value) : base(type) { this.value = value; }
        }

        public enum ActionType { SHIFT, REDUCE, ACCEPT }
        public class Action
        {
            public ActionType type;
            public int stateOrProduction;
            public Action(ActionType type, int stateOrProduction)
            {
                this.type = type; this.stateOrProduction = stateOrProduction;
            }
            public override int GetHashCode()
            {
                return type.GetHashCode() ^ stateOrProduction.GetHashCode();
            }
            public override bool Equals(object obj)
            {
                Action that = obj as Action;
                if (that == null) return false;
                return this.type == that.type && this.stateOrProduction == that.stateOrProduction;
            }

            public override string! ToString()
            {
                return type + " " + stateOrProduction;
            }
        }

        protected class TokenType
        {
            public readonly int Type;
            public readonly Regex! Regex;
            public readonly Lexer Lexer;
            public TokenType(int type, Regex regex, [Delayed] Lexer lexer)
            {
                this.Type = type; this.Regex = (!)regex; this.Lexer = lexer;
            }
        }
    }
}
