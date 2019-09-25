////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   This is a very limited Xml Reader.
//
//  BUG:    The parser cannot handle attributes in single quotes
//          Actually, that's a feature -- XML requires the quotes.
//
namespace Microsoft.Singularity.Xml
{
    using System;
    using System.IO;
    using System.Collections;
    using System.Text;

    /// <summary>
    /// This is a simple XML Parser that does no validation.  All it does it parse the syntax of XML
    /// </summary>
    public class XmlReader
    {
        private States state;
        private int lineNumber;
        XmlNode doc; 
        
        public XmlReader()
        {
            state = States.START;
            lineNumber = 1;
        }

        private enum TokenType
        {
            NAME,
            STRING_LITERAL,
            OPERATOR,
            NONE
        }

        private enum States
        {
            START,
            NEED_ELEMENT_NAME,
            NEED_ATTRIBUTE_NAME,
            NEED_EQUALS_SIGN,
            NEED_ATTRIBUTE_VALUE,
            NEED_CLOSURE_BRACKET,
            NEED_CLOSURE_NAME,
            NEED_FINAL_BRACKET,
            QUESTION_MARK_ELEMENT,
            GET_STRINGS
        }

        public XmlNode Parse(byte[] xmlBytes)
        {
            MemoryStream ms = new MemoryStream(xmlBytes);
            StreamReader sr = new StreamReader(ms);
            doc = new XmlNode("::xml");
            return ParseHelper(doc, sr);
        }

        public XmlNode Parse(string filePath)
        {
            StreamReader sr = new StreamReader(filePath);
            doc = new XmlNode("::xml");
            return ParseHelper(doc, sr);
        }


        private XmlNode ParseHelper(XmlNode doc, TextReader sr)
        {
        
            TokenType type;
            string token = null;
            ArrayList xmlNodes = new ArrayList();
            XmlNode curNode = null;
            Stack st = new Stack();
            string curAttributeName = null;

            while (ReadToken(sr, out token, out type)) {
                switch (state) {
                    case States.START:
                        //Console.WriteLine("START");
                        if (type == TokenType.OPERATOR && token.Equals("<")) {
                            state = States.NEED_ELEMENT_NAME;
                        }
                        else {
                            // All other text is interpreted as freestanding text.
                            // It had better occur within a tag!
                            if (st.Count == 0) {
                                throw new XmlException("Line " + lineNumber + ": Text must be inside a tag");
                            }

                            XmlNode lastNode = (XmlNode)st.Peek();
                            lastNode.AddText(token);

                            // Next state depends on whether we're at the end of the text-within-a-tag
                            // already or not.
                            if ((char)sr.Peek() == '<') {
                                // Looks like we're already at the end
                                state = States.START;
                            }
                            else {
                                state = States.GET_STRINGS;
                            }
                        }
                        break;

                    case States.NEED_ELEMENT_NAME:
                        //Console.WriteLine("NEED_ELEMENT_NAME");
                        if (type == TokenType.NAME) {
                            state = States.NEED_ATTRIBUTE_NAME;
                            curNode = new XmlNode(token, st.Count);

                            //Console.WriteLine("Saw beginning of element: " + token);
                        }
                        else if (type == TokenType.OPERATOR && token.Equals("/")) {
                            state = States.NEED_CLOSURE_NAME;
                        }
                        else if (type == TokenType.OPERATOR &&
                                 (token.Equals("?") || token.Equals("!") || token.Equals('-'))) {
                            // then go to the question mark state and ignore this element
                            state = States.QUESTION_MARK_ELEMENT;
                        }
                        else {
                            throw new XmlException("Line " + lineNumber + ": Can only begin a tag with / or a name");
                        }
                        break;

                    case States.NEED_ATTRIBUTE_NAME:
                        //Console.WriteLine("NEED_ATTRIBUTE_NAME");
                        if (type == TokenType.NAME) {
                            state = States.NEED_EQUALS_SIGN;
                            curAttributeName = token;
                        }
                        else if (type == TokenType.OPERATOR && token.Equals(">")) {
                            // hold onto this node so we can check it later
                            state = States.START;
                            bool stackEmpty = st.Count == 0;

                            if (!stackEmpty) {
                                XmlNode parent = (XmlNode)st.Peek();
                                parent.AddChild(curNode);
                                //DebugStub.WriteLine("add {1} to {0}", 
                                //    __arglist(parent.Name, curNode.Name));
                            }
                            else doc.AddChild(curNode);
                            st.Push(curNode);

                            curNode = null;
                        }
                        else if (type == TokenType.OPERATOR && token.Equals("/")) {
                            // this node is almost complete
                            state = States.NEED_CLOSURE_BRACKET;
                        }
                        else {
                            throw new XmlException("Line " + lineNumber + ": Must have either attributes, '/>', or '>' after the name of an element");
                        }
                        break;

                    case States.NEED_EQUALS_SIGN:
                        //Console.WriteLine("NEED_EQUALS_SIGN");
                        if (type == TokenType.OPERATOR && token.Equals("=")) {
                            state = States.NEED_ATTRIBUTE_VALUE;
                        }
                        else {
                            throw new XmlException("Line " + lineNumber + ": Need an '=' after an attribute name");
                        }
                        break;

                    case States.NEED_ATTRIBUTE_VALUE:
                        //Console.WriteLine("NEED_ATTRIBUTE_VALUE");
                        if (type == TokenType.STRING_LITERAL) {
                            state = States.NEED_ATTRIBUTE_NAME;
                            string unescaped_attribute_value = ExpandEntityReferences(token);
                            curNode[curAttributeName] = unescaped_attribute_value;
                            //DebugStub.WriteLine("  {2}.attr[{0}]={1}",
                            //    __arglist(curAttributeName ,unescaped_attribute_value, curNode.Name));
                            curAttributeName = null;
                        }
                        else {
                            throw new XmlException("Line " + lineNumber + ": Must have an attribute value after the '=' in an XML node");
                        }
                        break;

                    case States.NEED_CLOSURE_BRACKET:
                        //Console.WriteLine("NEED_CLOSURE_BRACKET");
                        if (type == TokenType.OPERATOR && token.Equals(">")) {
                            // this node is done, and we don't have to check it
                            state = States.START;
                            bool stackEmpty = st.Count == 0;

                            if (!stackEmpty) {
                                XmlNode parent = (XmlNode)st.Peek();
                                parent.AddChild(curNode);
                            }
                            else doc.AddChild(curNode);
                        }
                        else {
                            throw new XmlException("Line " + lineNumber + ": Must have a '>' after a closing '/' in an XML node");
                        }
                        break;

                    case States.NEED_CLOSURE_NAME:
                        //Console.WriteLine("NEED_CLOSURE_NAME");
                        if (type == TokenType.NAME) {
                            // pop the last XmlNode and make sure that this name matches.
                            // Otherwise we don't have balanced open and close tags
                            state = States.NEED_FINAL_BRACKET;
                            XmlNode xmln = (XmlNode)st.Pop();
                            if (!token.Equals(xmln.Name)) {
                                throw new XmlException("Line " + lineNumber + ": " + token + " does not match " + xmln.Name);
                            }
                            //Console.WriteLine("Saw end of element: " + token);
                        }
                        else {
                            throw new XmlException("Line " + lineNumber + ": Must have a name after an opening />");
                        }

                        break;
                    case States.NEED_FINAL_BRACKET:
                        //Console.WriteLine("NEED_FINAL_BRACKET");
                        if (type == TokenType.OPERATOR && token.Equals(">")) {
                            state = States.START;
                        }
                        else {
                            throw new XmlException("Line " + lineNumber + ": Must have a > after a closure tag's name");
                        }
                        break;

                    case States.QUESTION_MARK_ELEMENT:
                        // just stay in this state until you see a '>'
                        while ('>' != ReadCharacter(sr)) {
                            ;
                        }
                        state = States.START;
                        break;

                    case States.GET_STRINGS:
                        {
                            // stay in this state until you see a '<'
                            StringBuilder sb = new StringBuilder();
                            XmlNode prevNode = (XmlNode)st.Peek();

                            if (type == TokenType.OPERATOR && token.Equals("<")) {
                                throw new XmlException("Unexpected tag beginning while in text state");
                            }

                            sb.Append(token);
                            while ((char)sr.Peek() != '<') {
                                sb.Append((char)sr.Read());
                            }

                            prevNode.AddText(sb.ToString());
                            state = States.START;
                            //Console.WriteLine("Grabbed string data");
                        }
                        break;
                }
            }

            sr.Close();
            return doc;
        }

        /// <summary>
        /// This method expands XML entity references found in an input string.
        /// If an invalid entity reference is encountered, this method will throw
        /// XmlException.
        /// </summary>
        /// <param name="input">The string to search for entity references.</param>
        /// <returns>The expanded string.</returns>
        private static string ExpandEntityReferences(string input)
        {
            // In most cases, there are no entity references.  Check for that case now.
            // If we do find an entity reference, then the work isn't wasted.
            int start = input.IndexOf('&');
            if (start == -1)
                return input;

            StringBuilder buffer = new StringBuilder();
            buffer.Append(input, 0, start);
            start++;

            for (;;) {
                // At this point, 'start' points to a named XML entity.
                // locate the entity name.
                int end = input.IndexOf(';', start);
                if (end == -1)
                    throw new XmlException("An invalid entity reference was found.  '&' is present, but there is no matching ';'.");

                int name_length = end - start;
                if (name_length == 0)
                    throw new XmlException("An invalid entity reference was found.  '&;' is not a valid entity reference.");

                string entity_name = input.Substring(start, name_length);
                string value;

                switch (entity_name) {
                    case "amp": value = "&"; break;
                    case "lt": value = "<"; break;
                    case "gt": value = ">"; break;
                    case "quot": value = "\""; break;
                    default:
                        throw new XmlException(String.Format("An invalid entity reference was found.  The entity '&{0};' is not recognized.", entity_name));
                }

                buffer.Append(value);

                // Are there any more entity references in this string?
                int next = input.IndexOf('&', end + 1);
                if (next == -1) {
                    // There are no more entity references in the string.
                    // Append the rest of the string.
                    buffer.Append(input, end + 1, input.Length - end - 1);
                    return buffer.ToString();
                }

                // Yes, there are more references.  Keep looping, preserving
                // the same meaning of 'start' as when we entered this loop.
                buffer.Append(input, end + 1, next - (end + 1));
                start = next + 1; // skip over next '&'
            }
        }

        private char ReadCharacter(TextReader sr)
        {
            char tempChar = (char)sr.Read();
            if (tempChar == '\n') {
                lineNumber++;
            }
            return tempChar;
        }

        private bool ReadToken(TextReader sr, out string token, out TokenType type)
        {
            // fortunately for us, the first character tells us exactly which of the three
            // types of token this is. [a-zA-Z] means it's a NAME, ["] means it's a STRING_LITERAL
            // and [<>/=] means it's an operator
            int nextVal = sr.Peek();

            if (nextVal == -1) {
                // this is the end of the file
                token = "";
                type = TokenType.NONE;
                return false;
            }

            char firstChar = unchecked((char)nextVal);

            // if it's in [a-zA-Z]
            if (('a' <= firstChar && firstChar <= 'z') || ('A' <= firstChar && firstChar <= 'Z')) {
                token = ReadName(sr);
                type = TokenType.NAME;
                return true;
            }
            else if (firstChar == '"') {
                token = ReadString(sr);
                type = TokenType.STRING_LITERAL;
                return true;
            }
            else if (firstChar == '<' ||
                     firstChar == '>' ||
                     firstChar == '/' ||
                     firstChar == '=' ||
                     firstChar == '?' ||
                     firstChar == '!' ||
                     firstChar == '-') {
                sr.Read();
                token = firstChar.ToString();
                type = TokenType.OPERATOR;
                return true;
            }
            else if (firstChar == ' ' || firstChar == '\n' || (int)firstChar == 13 || firstChar == '\t') {
                // throw away all whitespace
                while (firstChar == ' ' || firstChar == '\n' || (int)firstChar == 13 || firstChar == '\t') {
                    char tempChar = (char)sr.Read();
                    if (tempChar == '\n') {
                        // increment the line count
                        lineNumber++;
                    }
                    firstChar = (char)sr.Peek();
                }
                return ReadToken(sr, out token, out type);
            }
            else {
                sr.Read();
                type = TokenType.NONE;
                token = firstChar.ToString();
                return true;
                //                throw new XmlException("Line " + lineNumber + ": '" + firstChar + "' is not a valid first character for a token");
            }
        }

        private string ReadName(TextReader sr)
        {
            StringBuilder sb = new StringBuilder();

            // add characters to our string until we see something that's not in [a-zA-Z0-9_-.:]
            char read = (char)sr.Peek();

            while (('a' <= read && read <= 'z') ||
                   ('A' <= read && read <= 'Z') ||
                   ('0' <= read && read <= '9') ||
                   read == '-' ||
                   read == '_' ||
                   read == '.' ||
                   read == ':') {
                sb.Append((char)sr.Read());
                read = (char)sr.Peek();
            }

            return sb.ToString();
        }

        private string ReadString(TextReader sr)
        {
            StringBuilder sb = new StringBuilder();
            // we need to read this string and translate it into a string literal.
            // this means that we have (for the moment) two magic characters: \ and "
            // "\\" means \ and "\"" means "
            bool translateNext = false;
            char read = (char)sr.Peek();
            if (read != '"') {
                throw new XmlException("Line " + lineNumber + ": Cannot start a string literal with " + (char)read + ".  You must use a '\"'");
            }
            // drop the '"' on the floor
            sr.Read();
            read = (char)sr.Read();

            while (read != '"' || translateNext) {
                if (!translateNext) {
                    if (read == '\\') {
                        translateNext = true;
                    }
                    else {
                        sb.Append(read);
                        read = (char)sr.Read();
                    }
                }
                else {
                    translateNext = false;
                    if (read == '\\') {
                        sb.Append("\\");
                        read = (char)sr.Read();
                    }
                    else if (read == '"') {
                        sb.Append("\"");
                        read = (char)sr.Read();
                    }
                    else {
                        throw new XmlException("Line " + lineNumber + ": Invalid escape sequence: \\" + read);
                    }
                }
            }

            return sb.ToString();
        }
    }
}
