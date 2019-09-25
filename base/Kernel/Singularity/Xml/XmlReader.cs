////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   This is a very limited Xml Reader, carved out of the
//          Libraries\Xml implementation.  At the end exists a
//          very basic stream class, which makes it possible to avoid linking
//          against System.IO.
//
//  Note:   All kernel Xml stream must be encoded as UTF-8.
//          UTF-8 is a way of writing Unicode characters with variable numbers
//          of bytes per character, optimized for the lower 127 ASCII
//          characters.  It's an efficient way of encoding US English in an
//          internationalizable way.
//          The UTF-8 byte order mark is simply the Unicode byte order mark
//          (0xFEFF) written in UTF-8 (0xEF 0xBB 0xBF).  The byte order mark
//          is used mostly to distinguish UTF-8 text from other encodings, and
//          doesn't switch the byte orderings.
//
//            bytes   bits    UTF-8 representation
//            -----   ----    -----------------------------------
//            1        7      0vvvvvvv
//            2       11      110vvvvv 10vvvvvv
//            3       16      1110vvvv 10vvvvvv 10vvvvvv
//            4       21      11110vvv 10vvvvvv 10vvvvvv 10vvvvvv
//            -----   ----    -----------------------------------
//
//          Surrogate:
//            Real Unicode value = (HighSurrogate - 0xD800) * 0x400 +
//                                 (LowSurrogate - 0xDC00) + 0x10000
//
//  BUG:    The parser cannot handle attributes in single quotes
//          Actually, that's a feature -- XML requires the quotes.
//
//          Use this file for XML processing inside the Kernel
///////////////////////////////////////////////////////////////////////////////

namespace Microsoft.Singularity.Xml
{
    using System;
    using System.Collections;
    using Singularity.Io;
    using System.Text;

    /// <summary>
    /// This is a simple XML Parser that does no validation.
    /// All it does it parse the syntax of XML
    /// Note - since IoMemory is not CLSCompliant, neither is this!
    /// </summary>
    [CLSCompliant(false)]
    public class XmlReader
    {
        private States state;
        private int lineNumber;
        private KernelMemoryStream stream;
        private bool isUtf8;
        private XmlNode doc;
        private XmlNode[] stack;
        private int stackTop;
        private const int defaultStackDepth = 16;

        private XmlReader()
        {
            state = States.START;
            lineNumber = 1;
            stack = new XmlNode[defaultStackDepth];
            stackTop = 0;
            doc = new XmlNode("::xml");
        }

        public XmlReader(IoMemory mem)
            : this()
        {
            if (mem == null)
                throw new ArgumentNullException("mem");
            stream = new KernelIoMemoryStream(mem);
        }

        public XmlReader(byte[] buffer)
            : this()
        {
            if (buffer == null)
                throw new ArgumentNullException("buffer");
            stream = new KernelByteMemoryStream(buffer);
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

        //////////////////////////////////////////////////// Stack Operations.
        //
        private void Push(XmlNode node)
        {
            if (stackTop >= stack.Length) {
                XmlNode[] dest = new XmlNode[stack.Length * 2];
                for (int i = 0; i < stackTop; i++) {
                    dest[i] = stack[i];
                }
                stack = dest;
            }
            stack[stackTop++] = node;
        }

        private XmlNode Pop()
        {
            XmlNode node = stack[stackTop - 1];
            stack[stackTop--] = null; // encourage GC sooner.
            return node;
        }

        private XmlNode Peek()
        {
            return stack[stackTop - 1];
        }

        //////////////////////////////////////////////////////////////////////
        //
        public XmlNode Parse()
        {
            if (stream == null) {
                return doc;
            }

            TokenType type;
            string token = null;
            XmlNode curNode = null;
            string curAttributeName = null;

            // Check for a UTF-8 preamble.
            isUtf8 = false;
            if (PeekCharacter() == 0xef) {
                if (ReadCharacter() == 0xef &&
                    ReadCharacter() == 0xbb &&
                    ReadCharacter() == 0xbf) {
                    isUtf8 = true;
                }
            }

            while (ReadToken(out token, out type)) {
                switch (state) {
                    case States.START:
                        if (type == TokenType.OPERATOR && token.Equals("<")) {
                            state = States.NEED_ELEMENT_NAME;
                        }
                        else {
                            // All other text is interpreted as freestanding text.
                            // It had better occur within a tag!
                            if (stackTop == 0) {
                                throw new XmlException(lineNumber, "Line " + lineNumber + ": Text must be inside a tag");
                            }

                            XmlNode lastNode = Peek();
                            lastNode.AddText(token);

                            // Next state depends on whether we're at the end of
                            // the text-within-a-tag already or not.
                            if (PeekCharacter() == '<') {
                                // Looks like we're already at the end
                                state = States.START;
                            }
                            else {
                                state = States.GET_STRINGS;
                            }
                        }
                        break;

                    case States.NEED_ELEMENT_NAME:
                        if (type == TokenType.NAME) {
                            state = States.NEED_ATTRIBUTE_NAME;
                            curNode = new XmlNode(token);
                        }
                        else if (type == TokenType.OPERATOR && token.Equals("/")) {
                            state = States.NEED_CLOSURE_NAME;
                        }
                        else if (type == TokenType.OPERATOR &&
                                 (token.Equals("?") ||
                                  token.Equals("!") ||
                                  token.Equals('-'))) {
                            // then go to the question mark state and ignore this element
                            state = States.QUESTION_MARK_ELEMENT;
                        }
                        else {
                            throw new XmlException(lineNumber, "Line " + lineNumber + ": Can only begin a tag with / or a name");
                        }
                        break;

                    case States.NEED_ATTRIBUTE_NAME:
                        if (type == TokenType.NAME) {
                            state = States.NEED_EQUALS_SIGN;
                            curAttributeName = token;
                        }
                        else if (type == TokenType.OPERATOR && token.Equals(">")) {
                            // hold onto this node so we can check it later
                            state = States.START;

                            if (stackTop != 0) {
                                XmlNode parent = Peek();
                                parent.AddChild(curNode);
                            }
                            else {
                                doc.AddChild(curNode);
                            }
                            Push(curNode);
                            curNode = null;
                        }
                        else if (type == TokenType.OPERATOR && token.Equals("/")) {
                            // this node is almost complete
                            state = States.NEED_CLOSURE_BRACKET;
                        }
                        else {
                            throw new XmlException(lineNumber, "Line " + lineNumber + ": Must have either attributes, '/>', or '>' after the name of an element");
                        }
                        break;

                    case States.NEED_EQUALS_SIGN:
                        if (type == TokenType.OPERATOR && token.Equals("=")) {
                            state = States.NEED_ATTRIBUTE_VALUE;
                        }
                        else {
                            throw new XmlException(lineNumber, "Line " + lineNumber + ": Need an '=' after an attribute name");
                        }
                        break;

                    case States.NEED_ATTRIBUTE_VALUE:
                        if (type == TokenType.STRING_LITERAL) {
                            state = States.NEED_ATTRIBUTE_NAME;
                            string unescaped_attribute_value = ExpandEntityReferences(token);
                            curNode.AddAttribute(curAttributeName, unescaped_attribute_value);
                            curAttributeName = null;
                        }
                        else {
                            throw new XmlException(lineNumber, "Line " + lineNumber + ": Must have an attribute value after the '=' in an XML node");
                        }
                        break;

                    case States.NEED_CLOSURE_BRACKET:
                        if (type == TokenType.OPERATOR && token.Equals(">")) {
                            // this node is done, and we don't have to check it
                            state = States.START;

                            if (stackTop != 0) {
                                XmlNode parent = Peek();
                                parent.AddChild(curNode);
                            }
                            else {
                                doc.AddChild(curNode);
                            }
                        }
                        else {
                            throw new XmlException(lineNumber, "Line " + lineNumber + ": Must have a '>' after a closing '/' in an XML node");
                        }
                        break;

                    case States.NEED_CLOSURE_NAME:
                        if (type == TokenType.NAME) {
                            // pop the last XmlNode and make sure that this name matches.
                            // Otherwise we don't have balanced open and close tags
                            state = States.NEED_FINAL_BRACKET;
                            XmlNode xmln = Pop();
                            if (!token.Equals(xmln.Name)) {
                                throw new XmlException(lineNumber, "Line " + lineNumber + ": " + token + " does not match " + xmln.Name);
                            }
                        }
                        else {
                            throw new XmlException(lineNumber, "Line " + lineNumber + ": Must have a name after an opening />");
                        }

                        break;
                    case States.NEED_FINAL_BRACKET:
                        if (type == TokenType.OPERATOR && token.Equals(">")) {
                            state = States.START;
                        }
                        else {
                            throw new XmlException(lineNumber, "Line " + lineNumber + ": Must have a > after a closure tag's name");
                        }
                        break;

                    case States.QUESTION_MARK_ELEMENT:
                        // just stay in this state until you see a '>'
                        while ('>' != ReadCharacter()) {
                            ;
                        }
                        state = States.START;
                        break;

                    case States.GET_STRINGS:
                        {
                            // stay in this state until you see a '<'
                            StringBuilder sb = new StringBuilder();
                            XmlNode prevNode = Peek();

                            if (type == TokenType.OPERATOR && token.Equals("<")) {
                                throw new XmlException(lineNumber, "Unexpected tag beginning while in text state");
                            }

                            sb.Append(token);
                            while (PeekCharacter() != -1 && PeekCharacter() != '<') {
                                sb.Append((char)ReadCharacter());
                            }

                            prevNode.AddText(sb.ToString());
                            state = States.START;
                        }
                        break;
                }
            }
            stream.Close();
            stream = null;
            return doc;
        }

        /// <summary>
        /// This method expands XML entity references found in an input string.
        /// If an invalid entity reference is encountered, this method will throw
        /// XmlException.
        /// </summary>
        /// <param name="input">The string to search for entity references.</param>
        /// <returns>The expanded string.</returns>
        private string ExpandEntityReferences(string input)
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
                    throw new XmlException(lineNumber, "An invalid entity reference was found.  '&' is present, but there is no matching ';'.");

                int name_length = end - start;
                if (name_length == 0)
                    throw new XmlException(lineNumber, "An invalid entity reference was found.  '&;' is not a valid entity reference.");

                string entity_name = input.Substring(start, name_length);
                string value;

                switch (entity_name) {
                    case "amp": value = "&"; break;
                    case "lt": value = "<"; break;
                    case "gt": value = ">"; break;
                    case "quot": value = "\""; break;
                    default:
                        throw new XmlException(lineNumber, String.Format("An invalid entity reference was found.  The entity '&{0};' is not recognized.", entity_name));
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

        //////////////////////////////////////////////////////////////////////
        //
        private int undoChar;

        private void UndoRead(int c)
        {
            undoChar = c;
        }

        private int PeekCharacter()
        {
            if (undoChar == '\0') {
                undoChar = ReadCharacter();
            }
            return undoChar;
        }

        private int ReadCharacter()
        {
            int val;
            if (undoChar != '\0') {
                val = undoChar;
                undoChar = '\0';
                return val;
            }

            val = stream.Read();
            if (val == '\n') {
                lineNumber++;
            }

            if (!isUtf8 || val < 0x80) {
                return val;
            }

            //  Shared UTF-8 Decoding:
            //      bytes   bits    UTF-8 representation
            //      -----   ----    -----------------------------------
            //      1        7      0vvvvvvv
            //      2       11      110vvvvv 10vvvvvv
            //      3       16      1110vvvv 10vvvvvv 10vvvvvv
            //      4       21      11110vvv 10vvvvvv 10vvvvvv 10vvvvvv
            //      -----   ----    -----------------------------------
            //
            int bytes = 0;
            if (val <= 0xdf) {
                bytes = 1;
                val &= 0x1f;
            }
            else if (val <= 0xef) {
                bytes = 2;
                val &= 0x0f;
            }
            else if (val <= 0xf7) {
                bytes = 3;
                    val &= 0x07;
            }

            while (bytes-- > 0) {
                int next = stream.Read();
                if (next < 0x80 || next > 0xbf) {
                    throw new XmlException(lineNumber, "Buffer_InvalidEncoding");
                }
                val = val << 6 | (next & 0x3f);
            }
            return val;
        }

        //////////////////////////////////////////////////////////////////////
        //
        private bool ReadToken(out string token, out TokenType type)
        {
            // fortunately for us, the first character tells us exactly which of
            // the three types of token this is. [a-zA-Z] means it's a NAME, ["]
            // means it's a STRING_LITERAL and [<>/=] means it's an operator
            int nextVal = PeekCharacter();

            if (nextVal == -1) {
                // this is the end of the file
                token = "";
                type = TokenType.NONE;
                return false;
            }

            char firstChar = unchecked((char)nextVal);

            // if it's in [a-zA-Z]
            if (('a' <= firstChar && firstChar <= 'z') ||
                ('A' <= firstChar && firstChar <= 'Z')) {
                token = ReadName();
                type = TokenType.NAME;
                return true;
            }
            else if (firstChar == '"') {
                token = ReadString();
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
                ReadCharacter();
                token = firstChar.ToString();
                type = TokenType.OPERATOR;
                return true;
            }
            else if (firstChar == ' ' ||
                     firstChar == '\n' ||
                     (int)firstChar == 13 ||
                     firstChar == '\t') {
                // throw away all whitespace
                while (firstChar == ' ' ||
                       firstChar == '\n' ||
                       (int)firstChar == 13 ||
                       firstChar == '\t') {
                    char tempChar = (char)ReadCharacter();
                    // patch to avoid problems with \n before EOF
                    if (PeekCharacter() == -1) {
                        type = TokenType.NONE;
                        token = "";
                        return false;
                    }
                    else {
                        firstChar = (char)PeekCharacter();
                    }
                }
                return ReadToken(out token, out type);
            }
            else {
                ReadCharacter();
                type = TokenType.NONE;
                token = firstChar.ToString();
                return true;
                // throw new XmlException(lineNumber, "Line " + lineNumber + ": '" + firstChar + "' is not a valid first character for a token");
            }
        }

        private string ReadName()
        {
            StringBuilder sb = new StringBuilder();

            // add characters to our string until we see something that's not in [a-zA-Z0-9_-.:]
            char read = (char)PeekCharacter();

            while (('a' <= read && read <= 'z') ||
                   ('A' <= read && read <= 'Z') ||
                   ('0' <= read && read <= '9') ||
                   read == '-' ||
                   read == '_' ||
                   read == '.' ||
                   read == ':') {
                sb.Append((char)ReadCharacter());
                read = (char)PeekCharacter();
            }
            return sb.ToString();
        }

        private string ReadString()
        {
            StringBuilder sb = new StringBuilder();
            // we need to read this string and translate it into a string literal.
            // this means that we have (for the moment) two magic characters: \ and "
            // "\\" means \ and "\"" means "
            bool translateNext = false;
            int read_or_eof = PeekCharacter();
            if (read_or_eof == -1) {
                throw new XmlException(lineNumber, "Line " + lineNumber + ": Cannot start a string literal at EOF.");
            }
            char read = (char)read_or_eof;
            if (read != '"') {
                throw new XmlException(lineNumber, "Line " + lineNumber + ": Cannot start a string literal with " + (char)read + ".  You must use a '\"'");
            }
            // drop the '"' on the floor
            ReadCharacter();
            read = (char)ReadCharacter();

            while (read != '"' || translateNext) {
                if (!translateNext) {
                    if (read == '\\') {
                        translateNext = true;
                    }
                    else {
                        sb.Append(read);
                        read = (char)ReadCharacter();
                    }
                }
                else {
                    translateNext = false;
                    if (read == '\\') {
                        sb.Append("\\");
                        read = (char)ReadCharacter();
                    }
                    else if (read == '"') {
                        sb.Append("\"");
                        read = (char)ReadCharacter();
                    }
                    else {
                        throw new XmlException(lineNumber, "Line " + lineNumber + ": Invalid escape sequence: \\" + read);
                    }
                }
            }

            return sb.ToString();
        }
    }

    abstract class KernelMemoryStream
    {
        public void Close()
        {
        }

        public abstract int Read();
    }

    /// <summary>
    /// This is a wholly unsafe manner of making a byte array look like
    /// a stream to the KernelXmlReader by giving it Read(), Peek(), and
    /// Close() methods.
    /// </summary>
    class KernelIoMemoryStream : KernelMemoryStream
    {
        private IoMemory buffer;   // can access buffer[???] as needed
        private int      position;
        private int      size;

        public KernelIoMemoryStream(IoMemory buffer)
        {
            if (buffer == null)
                throw new ArgumentNullException("buffer");
            this.buffer = buffer;
            position = 0;
            size = buffer.Length;
        }

        public override int Read()
        {
            if (position >= size) {
                return -1;
            }

            return buffer[position++];
        }
    }

    class KernelByteMemoryStream : KernelMemoryStream
    {
        private byte[]  buffer;   // can access buffer[???] as needed
        private int     position;
        private int     size;

        public KernelByteMemoryStream(byte[] buffer)
        {
            if (buffer == null)
                throw new ArgumentNullException("buffer");
            this.buffer = buffer;
            position = 0;
            size = buffer.Length;
        }

        public override int Read()
        {
            if (position == size) {
                return -1;
            }
            return buffer[position++];
        }
    }
}
