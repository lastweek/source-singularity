//------------------------------------------------------------------------------
// <copyright file="XmlWriter.cs" company="Microsoft">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//------------------------------------------------------------------------------
namespace Microsoft.Singularity.Xml
{
    using System;
    using System.Collections;
    using System.Text;
    using System.IO;

// <include file='doc\XmlWriter.uex' path='docs/doc[@for="Formatting"]/*' />
/// <devdoc>
///    <para>
///       Specifies formatting options for the XmlWriter stream.
///    </para>
/// </devdoc>
    public enum Formatting {
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="Formatting.None"]/*' />
        /// <devdoc>
        ///    <para>
        ///       No special formatting is done (this is the default).
        ///    </para>
        /// </devdoc>
        None,
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="Formatting.Indented"]/*' />
        /// <devdoc>
/// This option causes child elements to be indented using
/// the Indentation and IndentChar properties.  It only indents Element Content
/// (http://www.w3.org/TR/1998/REC-xml-19980210#sec-element-content)
/// and not Mixed Content (http://www.w3.org/TR/1998/REC-xml-19980210#sec-mixed-content)
/// according to the XML 1.0 definitions of these terms.
/// </devdoc>
        Indented,
    };



// <include file='doc\XmlWriter.uex' path='docs/doc[@for="WriteState"]/*' />
/// <devdoc>
///    <para>
///       Specifies the state of the XmlWriter stream.
///    </para>
/// </devdoc>
    public enum WriteState {
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="WriteState.Start"]/*' />
        /// <devdoc>
        ///    <para>
        ///       Nothing has been written yet.
        ///    </para>
        /// </devdoc>
        Start,
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="WriteState.Prolog"]/*' />
        /// <devdoc>
        ///    <para>
        ///       Writing the prolog.
        ///    </para>
        /// </devdoc>
        Prolog,
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="WriteState.Element"]/*' />
        /// <devdoc>
        ///    <para>
        ///       Writing a the start tag for an element.
        ///    </para>
        /// </devdoc>
        Element,
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="WriteState.Attribute"]/*' />
        /// <devdoc>
        ///    <para>
        ///       Writing an attribute value.
        ///    </para>
        /// </devdoc>
        Attribute,
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="WriteState.Content"]/*' />
        /// <devdoc>
        ///    <para>
        ///       Writing element content.
        ///    </para>
        /// </devdoc>
        Content,
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="WriteState.Closed"]/*' />
        /// <devdoc>
        ///    <para>
        ///       Close has been called.
        ///    </para>
        /// </devdoc>
        Closed,
    };

 

// Abstract base class.
    // <include file='doc\XmlWriter.uex' path='docs/doc[@for="XmlWriter"]/*' />
    /// <devdoc>
    ///    <para>Represents a writer that provides fast non-cached forward-only way of generating XML streams containing XML documents that conform to the W3C Extensible Markup Language (XML) 1.0 specification and the Namespaces in XML specification.</para>
    /// <para>This class is <see langword='virtual'/> .</para>
    /// </devdoc>
    public  class XmlWriter {

        Encoding encoding;
        TextWriter textWriter;
        char quoteChar;
        TagInfo[] stack;
        int top;
        int indentation;
        char indentChar;
        bool flush;
        bool indented; // perf - faster to check a boolean.

        // State machine is working through autocomplete
        private enum State
        {
            Start,
            Prolog,
            PostDTD,
            Element,
            Attribute,
            Content,
            AttrOnly,
            Epilog,
            Error,
            Closed
        }

        private enum Token
        {
            PI,
            Doctype,
            Comment,
            CData,
            StartElement,
            EndElement,
            LongEndElement,
            StartAttribute,
            EndAttribute,
            Content,
            RawData,
            Whitespace,
            Empty
        }

        static string[] stateName = {
            "Start",
            "Prolog",
            "PostDTD",
            "Element",
            "Attribute",
            "Content",
            "AttrOnly",
            "Epilog",
            "Error",
            "Closed",
        };

        static string[] tokenName = {
            "PI",
            "Doctype",
            "Comment",
            "CData",
            "StartElement",
            "EndElement",
            "LongEndElement",
            "StartAttribute",
            "EndAttribute",
            "Content",
            "RawData",
            "Whitespace",
            "Empty"
        };

        static readonly State[,] stateTableDefault = {
            //                          State.Start      State.Prolog     State.PostDTD    State.Element    State.Attribute  State.Content   State.AttrOnly   State.Epilog
            //
            /* Token.PI             */{ State.Prolog,    State.Prolog,    State.PostDTD,   State.Content,   State.Content,   State.Content,  State.Error,     State.Epilog},
            /* Token.Doctype        */{ State.PostDTD,   State.PostDTD,   State.Error,     State.Error,     State.Error,     State.Error,    State.Error,     State.Error},
            /* Token.Comment        */{ State.Prolog,    State.Prolog,    State.PostDTD,   State.Content,   State.Content,   State.Content,  State.Error,     State.Epilog},
            /* Token.CData          */{ State.Content,   State.Content,   State.Error,     State.Content,   State.Content,   State.Content,  State.Error,     State.Epilog},
            /* Token.StartElement   */{ State.Element,   State.Element,   State.Element,   State.Element,   State.Element,   State.Element,  State.Error,     State.Element},
            /* Token.EndElement     */{ State.Error,     State.Error,     State.Error,     State.Content,   State.Content,   State.Content,  State.Error,     State.Error},
            /* Token.LongEndElement */{ State.Error,     State.Error,     State.Error,     State.Content,   State.Content,   State.Content,  State.Error,     State.Error},
            /* Token.StartAttribute */{ State.AttrOnly,  State.Error,     State.Error,     State.Attribute, State.Attribute, State.Error,    State.Error,     State.Error},
            /* Token.EndAttribute   */{ State.Error,     State.Error,     State.Error,     State.Error,     State.Element,   State.Error,    State.Epilog,     State.Error},
            /* Token.Content        */{ State.Content,   State.Content,   State.Error,     State.Content,   State.Attribute, State.Content,  State.Attribute, State.Epilog},
            /* Token.RawData        */{ State.Prolog,    State.Prolog,    State.PostDTD,   State.Content,   State.Attribute, State.Content,  State.Attribute, State.Epilog},
            /* Token.Whitespace     */{ State.Prolog,    State.Prolog,    State.PostDTD,   State.Content,   State.Attribute, State.Content,  State.Attribute, State.Epilog},
        };

        static readonly State[,] stateTableDocument = {
            //                          State.Start      State.Prolog     State.PostDTD    State.Element    State.Attribute  State.Content   State.AttrOnly   State.Epilog
            //
            /* Token.PI             */{ State.Error,     State.Prolog,    State.PostDTD,   State.Content,   State.Content,   State.Content,  State.Error,     State.Epilog},
            /* Token.Doctype        */{ State.Error,     State.PostDTD,   State.Error,     State.Error,     State.Error,     State.Error,    State.Error,     State.Error},
            /* Token.Comment        */{ State.Error,     State.Prolog,    State.PostDTD,   State.Content,   State.Content,   State.Content,  State.Error,     State.Epilog},
            /* Token.CData          */{ State.Error,     State.Error,     State.Error,     State.Content,   State.Content,   State.Content,  State.Error,     State.Error},
            /* Token.StartElement   */{ State.Error,     State.Element,   State.Element,   State.Element,   State.Element,   State.Element,  State.Error,     State.Error},
            /* Token.EndElement     */{ State.Error,     State.Error,     State.Error,     State.Content,   State.Content,   State.Content,  State.Error,     State.Error},
            /* Token.LongEndElement */{ State.Error,     State.Error,     State.Error,     State.Content,   State.Content,   State.Content,  State.Error,     State.Error},
            /* Token.StartAttribute */{ State.Error,     State.Error,     State.Error,     State.Attribute, State.Attribute, State.Error,    State.Error,     State.Error},
            /* Token.EndAttribute   */{ State.Error,     State.Error,     State.Error,     State.Error,     State.Element,   State.Error,    State.Error,     State.Error},
            /* Token.Content        */{ State.Error,     State.Error,     State.Error,     State.Content,   State.Attribute, State.Content,  State.Error,     State.Error},
            /* Token.RawData        */{ State.Error,     State.Prolog,    State.PostDTD,   State.Content,   State.Attribute, State.Content,  State.Error,     State.Epilog},
            /* Token.Whitespace     */{ State.Error,     State.Prolog,    State.PostDTD,   State.Content,   State.Attribute, State.Content,  State.Error,     State.Epilog},
        };

        State[,] stateTable;
        State currentState;
        Token lastToken;

        struct TagInfo
        {
            internal string name;
            internal string prefix;
            internal string defaultNs;
            internal int prefixCount;
            internal bool mixed; // whether to pretty print the contents of this element.
            internal void Init()
            {
                name = null;
                prefix = null;
                defaultNs = String.Empty;
                prefixCount = 0;
                mixed = false;
            }
        }
       
        
        public XmlWriter(Stream w, Encoding encoding) 
        {
            textWriter = new StreamWriter(w, encoding);
            this.encoding = encoding;
            indentation = 2;
            indentChar = ' ';
            stack = new TagInfo[10];
            top = 0;// 0 is an empty sentanial element
            stack[top].Init();
            quoteChar = '"';
            flush = false;
            indented = true;
            this.stateTable = stateTableDefault;
        }
        
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="XmlWriter.WriteStartDocument"]/*' />
        /// <devdoc>
        ///    <para>Writes out the XML declaration with the version "1.0".</para>
        /// </devdoc>
        public virtual void WriteStartDocument()
        {
        }
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="XmlWriter.WriteStartDocument1"]/*' />
        /// <devdoc>
        ///    <para>Writes out the XML declaration with the version "1.0" and the
        ///       standalone attribute.</para>
        /// </devdoc>
        public virtual void WriteStartDocument(bool standalone)
        {
            StartDocument(-1); 
        }
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="XmlWriter.WriteEndDocument"]/*' />
        /// <devdoc>
        ///    Closes any open elements or attributes and
        ///    puts the writer back in the Start state.
        /// </devdoc>
        public virtual void WriteEndDocument()
        {
        }

        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="XmlWriter.WriteStartElement"]/*' />
        /// <devdoc>
        ///    <para>Writes out the specified start tag and associates it with the
        ///       given namespace.</para>
        /// </devdoc>
        public void WriteStartElement(string localName, string ns) {
            WriteStartElement(null, localName, ns);
        }

        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="XmlWriter.WriteStartElement1"]/*' />
        /// <devdoc>
        ///    <para>Writes out the specified start tag and
        ///       associates it with the given namespace and prefix.</para>
        /// </devdoc>
        public virtual void WriteStartElement(string prefix, string localName, string ns)
        {
            AutoComplete(Token.StartElement);
            PushStack();
            textWriter.Write('<');
            stack[top].name = localName;
            textWriter.Write(localName);
        }

        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="XmlWriter.WriteStartElement2"]/*' />
        /// <devdoc>
        ///    <para>Writes out a start tag with the specified name.</para>
        /// </devdoc>
        public void WriteStartElement(string localName) {
            WriteStartElement(null, localName, null);
        }


        public void WriteAttributeString(string localName, string value) {
            WriteStartAttribute(null, localName, null);
            WriteString(value);
            WriteEndAttribute();
        }

        public virtual void WriteString(string text)
        {
            if (null != text && String.Empty != text) {
                AutoComplete(Token.Content);
                textWriter.Write(text);
            }
        }
        public virtual void WriteEndAttribute()
        {
            AutoComplete(Token.EndAttribute);
        }


        // <include file='doc\XmlTextWriter.uex' path='docs/doc[@for="XmlTextWriter.WriteStartAttribute"]/*' />
        /// <devdoc>
        ///    <para>Writes the start of an attribute.</para>
        /// </devdoc>
        public virtual void WriteStartAttribute(string prefix, string localName, string ns)
        {
            AutoComplete(Token.StartAttribute);

            textWriter.Write(localName);
            textWriter.Write('=');
            textWriter.Write(this.quoteChar);
        }
        
 
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="XmlWriter.WriteEndElement"]/*' />
        /// <devdoc>
        ///    <para>Closes one element and pops the corresponding namespace scope.</para>
        /// </devdoc>
        public virtual void WriteEndElement()
        {
            InternalWriteEndElement(false);
        }
        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="XmlWriter.WriteFullEndElement"]/*' />
        /// <devdoc>
        ///    <para>Closes one element and pops the
        ///       corresponding namespace scope.</para>
        /// </devdoc>
        public virtual void WriteFullEndElement()
        {
            InternalWriteEndElement(true);
        }


        // <include file='doc\XmlTextWriter.uex' path='docs/doc[@for="XmlTextWriter.Close"]/*' />
        /// <devdoc>
        ///    <para>Close this stream and the underlying stream.</para>
        /// </devdoc>
        public virtual void Close()
        {
            try {
                AutoCompleteAll();
            }
            catch (Exception) { } // never fail
            Flush();
            textWriter.Close();
            this.currentState = State.Closed;
        }

        // <include file='doc\XmlWriter.uex' path='docs/doc[@for="XmlWriter.Flush"]/*' />
        /// <devdoc>
        ///    <para>Flush whatever is in the buffer to the underlying streams and flush the
        ///       underlying stream.</para>
        /// </devdoc>
        public virtual void Flush()
        {
            textWriter.Flush();
        }
        
        internal void FlushEncoders() 
        {
            textWriter.Flush();
        }

        void Indent(bool beforeEndElement)
        {
            // pretty printing.
            if (top == 0) {
                textWriter.WriteLine();
            }
            else if (!stack[top].mixed) {
                textWriter.WriteLine();
                int i = beforeEndElement ? top - 1 : top;
                for (i *= this.indentation; i > 0; i--) {
                    textWriter.Write(this.indentChar);
                }
            }
        }
        void StartDocument(int standalone)
        {
            if (this.currentState != State.Start) {
                throw new InvalidOperationException("Res.Xml_NotTheFirst");
            }
            this.stateTable = stateTableDocument;
            this.currentState = State.Prolog;

            StringBuilder bufBld = new StringBuilder(128);
            bufBld.Append("version=" + quoteChar + "1.0" + quoteChar);
            if (this.encoding != null) {
                bufBld.Append(" encoding=" + quoteChar);
                //bufBld.Append(this.encoding.WebName);
                bufBld.Append("utf-8");
                bufBld.Append(quoteChar);
            }
            if (standalone >= 0) {
                bufBld.Append(" standalone=" + quoteChar);
                bufBld.Append(standalone == 0 ? "no" : "yes");
                bufBld.Append(quoteChar);
            }
            InternalWriteProcessingInstruction("xml", bufBld.ToString());
        }
        
        void InternalWriteProcessingInstruction(string name, string text)
        {
            textWriter.Write("<?");
            textWriter.Write(name);
            textWriter.Write(' ');
            if (null != text) {
                textWriter.Write(text);
            }
            textWriter.Write("?>");
        }

        void AutoCompleteAll()
        {
            while (top > 0) {
                if (this.flush) {
                    FlushEncoders();
                }
                WriteEndElement();
            }
        }

          void InternalWriteEndElement(bool longFormat) {
            if (top <= 0) {
                throw new InvalidOperationException("Res.Xml_NoStartTag");
            }
            // if we are in the element, we need to close it.
            AutoComplete(longFormat ?  Token.LongEndElement : Token.EndElement);
            if (this.lastToken == Token.LongEndElement) {
                if (this.indented) {
                    Indent(true);
                }
                textWriter.Write('<');
                textWriter.Write('/');
                textWriter.Write(stack[top].name);
                textWriter.Write('>');
            }
            top--;
        }

        void PushStack() {
            if (top == stack.Length - 1) {
                TagInfo[] na = new TagInfo[stack.Length + 10];
                if (top > 0) Array.Copy(stack,na,top + 1);
                stack = na;
            }

            top ++; // Move up stack
            stack[top].Init();
        }


        void WriteEndStartTag(bool empty)
        {
            //xmlEncoder.StartAttribute(false);
            //xmlEncoder.EndAttribute();
            if (empty) {
                textWriter.Write(" /");
            }
            textWriter.Write('>');
        }

        void WriteEndAttributeQuote()
        {
            textWriter.Write(this.quoteChar);
        }

        void AutoComplete(Token token)
        {
            if (this.currentState == State.Closed) {
                throw new InvalidOperationException("Res.Xml_Closed");
            }

            State curr = this.currentState;
            State newState = this.stateTable[(int)token, (int)this.currentState];
            //Console.WriteLine("complete: <{1},{0}> ->{2}", 
            //    tokenName[(int) token], stateName[(int) currentState], stateName[(int) newState]);
            if (newState == State.Error) {
                throw new InvalidOperationException("Res.Xml_WrongToken, tokenName[(int)token], stateName[(int)this.currentState]");
            }

            switch (token) {
                case Token.Doctype:
                    if (this.indented && this.currentState != State.Start) {
                        Indent(false);
                    }
                    break;

                case Token.StartElement:
                case Token.Comment:
                case Token.PI:
                case Token.CData:
                    if (this.currentState == State.Attribute) {
                        WriteEndAttributeQuote();
                        WriteEndStartTag(false);
                    }
                    else if (this.currentState == State.Element) {
                        WriteEndStartTag(false);
                    }
                    Flush();
                    if (token == Token.CData) {
                        stack[top].mixed = true;
                    }
                    else if (this.indented && this.currentState != State.Start) {
                        Indent(false);
                    }
                    break;

                case Token.EndElement:
                case Token.LongEndElement:
                    if (this.flush) {
                        FlushEncoders();
                    }
                    if (this.currentState == State.Attribute) {
                        WriteEndAttributeQuote();
                    }
                    if (this.currentState == State.Content) {
                        token = Token.LongEndElement;
                    }
                    else {
                        WriteEndStartTag(token == Token.EndElement);
                    }
                    if (stateTableDocument == this.stateTable && top == 1) {
                        newState = State.Epilog;
                    }
                    break;

                case Token.StartAttribute:
                    if (this.flush) {
                        FlushEncoders();
                    }
                    if (this.currentState == State.Attribute) {
                        WriteEndAttributeQuote();
                        textWriter.Write(' ');
                    }
                    else if (this.currentState == State.Element) {
                        textWriter.Write(' ');
                    }
                    break;

                case Token.EndAttribute:
                    if (this.flush) {
                        FlushEncoders();
                    }
                    WriteEndAttributeQuote();
                    break;

                case Token.Whitespace:
                case Token.Content:
                case Token.RawData:
                    if (this.currentState == State.Element && this.lastToken != Token.Content) {
                        WriteEndStartTag(false);
                    }
                    //else if (this.currentState == State.Attribute && this.specialAttr == SpecialAttr.None && this.lastToken == Token.Content)
                    else if (this.currentState == State.Attribute && this.lastToken == Token.Content) {
                        // Beta 2
                        // textWriter.Write(' ');
                    }
                    if (newState == State.Content) {
                        stack[top].mixed = true;
                    }
                    break;

                default:
                    throw new InvalidOperationException("Res.Xml_InvalidOperation");
            }
            this.currentState = newState;
            this.lastToken = token;
        }

    }
}

