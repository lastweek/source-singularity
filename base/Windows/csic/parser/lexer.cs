public class Char2InputElementEnumerator : InputElementEnumerator, System.Collections.IEnumerator {
	protected int colno = 1;
	protected int lineno = 1;
	protected int startColumn = 0;
	protected string file;
	protected int fileOffset;

	protected CharEnumerator ce;
	private bool success;
	private bool atEOI;
	// private bool yieldEOF;
	private InputElement buffered = null;

	protected System.Text.StringBuilder tmp = new System.Text.StringBuilder();

	public Char2InputElementEnumerator(CharEnumerator ce, string file) {
		this.ce = ce;
		this.file = file;
		success = false;
		// yieldEOF = false;
		atEOI = !ce.MoveNext();
	}

	protected bool ret(string tag) {
		return ret(tag, tag);
	}

	protected bool ret(string tag, string str) {
		_current = new InputElement(tag, str, file, lineno, colno, file, fileOffset);
		success = true;
		return true;
	}

	protected bool ret(string tag, System.Text.StringBuilder buf) {
		return ret(tag, buf.ToString());
	}

	protected bool malformed(string tag, string str) {
		_current = new MalformedInputElement(new InputElement(tag, str, file, lineno, colno, file, fileOffset));
		success = true;
		return true;
	}

	protected bool malformed(string tag, System.Text.StringBuilder buf) {
		return malformed(tag, buf.ToString());
	}


	public override bool MoveNext() {
		string str;

		if (buffered != null) {
			_current = buffered;
			buffered = null;
			return true;
		}
		if (atEOI) {
			// if (yieldEOF) {
			// 	return success = false;
			// }
			// yieldEOF = true;
			return ret("<EOF>");
		}
		colno = ce.Location - startColumn + 1;
		fileOffset = ce.Location;

		tmp.Length = 0;
		switch (ce.Current) {
		case '#':
			return preproc();
		case '"':
			tmp.Append('"');
			return stringLiteral();
		case '\'':
			tmp.Append('\'');
			return characterLiteral();
		case '0':
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
		case '8':
		case '9':
			return number();

		case '\u0009':
			nextchar();
			return ret("WHITESPACE", "\u0009");
		case '\u000b':
			nextchar();
			return ret("WHITESPACE", "\u000b");
		case '\u000c':
			nextchar();
			return ret("WHITESPACE", "\u000c");
		case '\u001a':
			nextchar();
			return ret("WHITESPACE", "\u001a");
		case '\u000d':
			str = "\u000d";
			if (nextchar()) {
				if (ce.Current == '\u000a') {
					str = "\u000d\u000a";
					nextchar();
				}
			}
			startColumn = ce.Location;
			lineno++;
			return ret("NEWLINE", str);
		case '\u000a':
			nextchar();
			startColumn = ce.Location;
			lineno++;
			return ret("NEWLINE", "\u000a");
		case '\u2028':
			nextchar();
			startColumn = ce.Location;
			lineno++;
			return ret("NEWLINE", "\u2028");
		case '\u2029':
			nextchar();
			startColumn = ce.Location;
			lineno++;
			return ret("NEWLINE", "\u2029");
		case '/':
			if (!nextchar()) {
				return ret("/");
			}
			if (ce.Current == '=') {
				nextchar();
				return ret("/=");
			}
			tmp.Append("/");
			if (ce.Current == '/') {	// begin "//" comment
				tmp.Append('/');
				return slashslashComment();
			}
			if (ce.Current == '*') {	// begin "/*" comment
				tmp.Append('*');
				return slashstarComment();
			}
			return ret("/");
		case '.':
			if (!nextchar()) {
				return ret(".");
			}
			if (ce.Current < '0' || ce.Current > '9') {
				return ret(".");
			}
			tmp.Append(".");
			while (nextchar() && ce.Current >= '0' && ce.Current <= '9') {
				tmp.Append(ce.Current);
			}
			return dotRealLiteral();


		case '+':
			if (!nextchar()) {
				return ret("+");
			}
			switch (ce.Current) {
			case '+':
				nextchar();
				return ret("++");
			case '=':
				nextchar();
				return ret("+=");
			default:
				return ret("+");
			}
		case ';':
			nextchar();
			return ret(";");
		case '[':
			nextchar();
			return ret("[");
		case '{':
			nextchar();
			return ret("{");
		case '(':
			nextchar();
			return ret("(");
		case '%':
			if (!nextchar()) {
				return ret("%");
			}
			switch (ce.Current) {
			case '=':
				nextchar();
				return ret("%=");
			default:
				return ret("%");
			}
		case '-':
			if (!nextchar()) {
				return ret("-");
			}
			switch (ce.Current) {
			case '-':
				nextchar();
				return ret("--");
			case '=':
				nextchar();
				return ret("-=");
			case '>':
				nextchar();
				return ret("->");
			default:
				return ret("-");
			}
		case '=':
			if (!nextchar()) {
				return ret("=");
			}
			switch (ce.Current) {
			case '=':
				nextchar();
				return ret("==");
			default:
				return ret("=");
			}
		case ']':
			nextchar();
			return ret("]");
		case '}':
			nextchar();
			return ret("}");
		case '*':
			if (!nextchar()) {
				return ret("*");
			}
			switch (ce.Current) {
			case '=':
				nextchar();
				return ret("*=");
			default:
				return ret("*");
			}
		case ':':
			if (!nextchar()) {
				return ret(":");
			}
			switch (ce.Current) {
			case ':':
				nextchar();
				return ret("::");
			default:
				return ret(":");
			}
		case '?':
			nextchar();
			return ret("?");
		case ',':
			nextchar();
			return ret(",");
		case '<':
			if (!nextchar()) {
				return ret("<");
			}
			switch (ce.Current) {
			case '=':
				nextchar();
				return ret("<=");
			case '<':
				if (!nextchar()) {
					return ret("<<");
				}
				switch (ce.Current) {
				case '=':
					nextchar();
					return ret("<<=");
				default:
					return ret("<<");
				}
			default:
				return ret("<");
			}
		case '|':
			if (!nextchar()) {
				return ret("|");
			}
			switch (ce.Current) {
			case '=':
				nextchar();
				return ret("|=");
			case '|':
				nextchar();
				return ret("||");
			default:
				return ret("|");
			}
		case '!':
			if (!nextchar()) {
				return ret("!");
			}
			switch (ce.Current) {
			case '=':
				nextchar();
				return ret("!=");
			default:
				return ret("!");
			}
		case ')':
			nextchar();
			return ret(")");
		case '&':
			if (!nextchar()) {
				return ret("&");
			}
			switch (ce.Current) {
			case '=':
				nextchar();
				return ret("&=");
			case '&':
				nextchar();
				return ret("&&");
			default:
				return ret("&");
			}
		case '>':
			if (!nextchar()) {
				return ret(">");
			}
			switch (ce.Current) {
			case '=':
				nextchar();
				return ret(">=");
			default:
				return ret(">");
			}
		case '^':
			if (!nextchar()) {
				return ret("^");
			}
			switch (ce.Current) {
			case '=':
				nextchar();
				return ret("^=");
			default:
				return ret("^");
			}
		case '~':
			nextchar();
			return ret("~");
		}

		if (UnicodeHelp.isZs(ce.Current)) {
			string t = ce.Current.ToString();
			t = System.String.Intern(t);
			nextchar();
			return ret("WHITESPACE", t);
		}

		// identifier, keyword, verbatim identifier, or verbatim string
		if (ce.Current == '@') {
			tmp.Append('@');
			if (!nextchar()) {
				return ret("UNRECOGNIZED", "@");
			}
			tmp.Append(ce.Current);
			if (ce.Current == '"') {
				return verbatimString();
			}
			return id_key(true);
		}
		if (UnicodeHelp.isLetterCharacter(ce.Current)
		    || ce.Current == '_') {
			tmp.Append(ce.Current);
			return id_key(false);
		}

		str = ce.Current.ToString();
		nextchar();
		return ret("UNRECOGNIZED", str);
	}

	private bool verbatimString() {
		int lineno = this.lineno;
		for (;;) {
			if (!nextchar()) {
				return malformed("string-literal", tmp.ToString());
			}
			tmp.Append(ce.Current);
		CONT:
			switch (ce.Current) {
			default:
				break;
				
			case '"':
				if (!nextchar() || ce.Current != '"') {
					bool b = ret("string-literal", tmp.ToString());
					this.lineno = lineno;
					return b;
				}
				tmp.Append(ce.Current);
				break;
			case '\u000d':
				if (!nextchar()) {
					lineno++;
					startColumn = ce.Location+1;
					bool b = malformed("string-literal", tmp);
					this.lineno = lineno;
					return b;
				}
				tmp.Append(ce.Current);
				if (ce.Current != '\u000a') { // count new-line on the \u000a of \u000d\u000a
					lineno++;
					startColumn = ce.Location+1;
				}
				goto CONT;	// evil, evil, evil!
			case '\u000a':
			case '\u2028':
			case '\u2029':
				lineno++;
				startColumn = ce.Location+1;
				break;
			}
		}
	}

	private bool dotRealLiteral() {
		// START cut-n-paste
		if (ce.Current == 'e' || ce.Current == 'E') {
			tmp.Append(ce.Current);
			if (!nextchar()) {
				return malformed("real-literal", tmp.ToString());
			}
			if (ce.Current == '-' || ce.Current == '+') {
				tmp.Append(ce.Current);
				if (!nextchar()) {
					return malformed("real-literal", tmp);
				}
			}
			if (ce.Current < '0' || ce.Current > '9') {
				return malformed("real-literal", tmp);
			}
			tmp.Append(ce.Current);
			while (nextchar() && ce.Current >= '0' && ce.Current <= '9') {
				tmp.Append(ce.Current);
			}
		}
		realSuffix();
		return ret("real-literal", tmp);
		// END cut-n-paste
	}

	// identifier, verbatim identifier, or keyword
	private bool id_key(bool verbatimFlag) {
		bool errorFlag;

		while (nextchar()) {
			if (UnicodeHelp.isIdentifierPartCharacter(ce.Current)) {
				tmp.Append(ce.Current);
				continue;
			}
			if (ce.Current == '\\') {
				tmp.Append(ce.Current);
				if (!nextchar()) {
					return malformed("identifier", tmp);
				}
				tmp.Append(ce.Current);
				errorFlag = true;
				char ch = unicodeEscape(ref errorFlag);
				if (errorFlag) {
					return malformed("identifier", tmp);
				}
				verbatimFlag = true;
				continue;
			}
			break;
		}
		if (verbatimFlag) {
			return ret("identifier", tmp);
		}
		string str = System.String.Intern(tmp.ToString());
		string t = keyword(str);
		if (t != null) {
			return ret(t, t);
		}
		return ret("identifier", str);
	}

	protected virtual string keyword(string s) {
		return KeywordHelp.keywordTag(s);
	}

	private bool slashstarComment() {
		while (nextchar()) {
		CONT:	tmp.Append(ce.Current);
			while (ce.Current == '*') {	// evil
				if (!nextchar()) {
					return malformed("COMMENT", tmp);
				}
				tmp.Append(ce.Current);
				if (ce.Current == '/') {
					nextchar();
					return ret("COMMENT", tmp);
				}
			}
			switch (ce.Current) {
			case '\u000d':
				if (!nextchar()) {
					lineno++;
					startColumn = ce.Location;
					return malformed("COMMENT", tmp);
				}
				if (ce.Current != '\u000a') { // count new-line on the \u000a of \u000d\u000a
					lineno++;
					startColumn = ce.Location;
				}
				goto CONT;	// evil, evil, evil
			case '\u000a':
			case '\u2028':
			case '\u2029':
				lineno++;
				startColumn = ce.Location;
				break;
			}
		}
		return malformed("COMMENT", tmp);
	}

	private bool slashslashComment() {
		while (nextchar()) {
			switch (ce.Current) {
			case '\u000d':
			case '\u000a':
			case '\u2028':
			case '\u2029':
				return ret("COMMENT", tmp);
			}
			tmp.Append(ce.Current);
		}
		return ret("COMMENT", tmp);
	}

	private bool characterLiteral() {
		bool errorFlag;
		char tmpChar;

		if (!nextchar()) {
			return malformed("character-literal", tmp);
		}
		tmp.Append(ce.Current);
		switch (ce.Current) {
		case '\x0027':
			return malformed("character-literal", tmp);
		case '\u000d':
		case '\u000a':
		case '\u2028':
		case '\u2029':
			return malformed("character-literal", tmp);
		case '\\':
			errorFlag = false;
			tmpChar = escapeChar(ref errorFlag);
			if (errorFlag) {
				return malformed("character-literal", tmp);
			}
			// tmp.Append(tmpChar);
			if (atEOI) {
				return malformed("character-literal", tmp);
			}
			if (ce.Current != '\'') {
				return malformed("character-literal", tmp);
			}
			tmp.Append(ce.Current);
			nextchar();
			return ret("character-literal", tmp);
		default:
			if (!nextchar()) {
				return malformed("character-literal", tmp);
			}
			if (ce.Current != '\'') {
				return malformed("character-literal", tmp);
			}
			tmp.Append(ce.Current);
			nextchar();
			return ret("character-literal", tmp);
		}
	}

	protected virtual bool stringLiteral() {
		bool errorFlag;
		char tmpChar;

		if (!nextchar()) {
			return malformed("string-literal", tmp);
		}
		for (;;) {
			tmp.Append(ce.Current);
			switch (ce.Current) {
			case '\u000d':
			case '\u000a':
			case '\u2028':
			case '\u2029':
				return malformed("string-literal", tmp);
			case '\\':
				errorFlag = false;
				tmpChar = escapeChar(ref errorFlag);
				if (errorFlag) {
					return malformed("string-literal", tmp);
				}
				// tmp.Append(tmpChar);
				break;
			case '"':
				nextchar();
				return ret("string-literal", tmp);
			default:
				if (!nextchar()) {
					return malformed("string-literal", tmp);
				}
				break;
			}
		}
	}

	private bool preproc() {
		while (nextchar()) {
			tmp.Append(ce.Current);
			switch (ce.Current) {
			case '\u000a':
			case '\u2028':
			case '\u2029':
				nextchar();
				startColumn = ce.Location;
				lineno++;
				return ret("PREPROC", tmp);
			case '\u000d':
				if (nextchar()) {
					if (ce.Current == '\u000a') {
						tmp.Append(ce.Current);
						nextchar();
					}
				}
				startColumn = ce.Location;
				lineno++;
				return ret("PREPROC", tmp);
			}
				
		}
		return ret("PREPROC", tmp);
	}

	private bool number() {
		if (ce.Current == '0') {
			tmp.Append(ce.Current);
			if (!nextchar()) {
				// just zero
				return ret("integer-literal", tmp);
			}
			if (ce.Current == 'x' || ce.Current == 'X') {
				// hex literal
				tmp.Append(ce.Current);
				while (nextchar()) {
					if ((ce.Current >= '0' && ce.Current <= '9') ||
					    (ce.Current >= 'a' && ce.Current <= 'f') ||
					    (ce.Current >= 'A' && ce.Current <= 'F')) {
						tmp.Append(ce.Current);
						continue;
					}
					break;
				}
				integerSuffix();
				return ret("integer-literal", tmp);
			}
		}
		while (ce.Current >= '0' && ce.Current <= '9') {
			tmp.Append(ce.Current);
			if (!nextchar()) {
				return ret("integer-literal", tmp);
			}
		}
		if (integerSuffix()) {
			return ret("integer-literal", tmp);
		}
		if (realSuffix()) {
			return ret("real-literal", tmp);
		}
		if (ce.Current == '.') {
			if (!nextchar()) {
				buffered = new InputElement(".", ".", file, lineno, colno, file, fileOffset);
				return ret("integer-literal", tmp);
			}
			if (ce.Current < '0' || ce.Current > '9') {
				buffered = new InputElement(".", ".", file, lineno, colno, file, fileOffset);
				return ret("integer-literal", tmp);
			}
			tmp.Append('.');
			tmp.Append(ce.Current);
			while (nextchar() && ce.Current >= '0' && ce.Current <= '9') {
				tmp.Append(ce.Current);
			}
			// START cut-n-paste
			if (ce.Current == 'e' || ce.Current == 'E') {
				tmp.Append(ce.Current);
				if (!nextchar()) {
					return malformed("real-literal", tmp);
				}
				if (ce.Current == '-' || ce.Current == '+') {
					tmp.Append(ce.Current);
					if (!nextchar()) {
						return malformed("real-literal", tmp);
					}
				}
				if (ce.Current < '0' || ce.Current > '9') {
					return malformed("real-literal", tmp);
				}
				tmp.Append(ce.Current);
				while (nextchar() && ce.Current >= '0' && ce.Current <= '9') {
					tmp.Append(ce.Current);
				}
			}
			realSuffix();
			return ret("real-literal", tmp);
			// END cut-n-paste
		}
		// START cut-n-paste
		if (ce.Current == 'e' || ce.Current == 'E') {
			tmp.Append(ce.Current);
			if (!nextchar()) {
				return malformed("real-literal", tmp);
			}
			if (ce.Current == '-' || ce.Current == '+') {
				tmp.Append(ce.Current);
				if (!nextchar()) {
					return malformed("real-literal", tmp);
				}
			}
			if (ce.Current < '0' || ce.Current > '9') {
				return malformed("real-literal", tmp);
			}
			tmp.Append(ce.Current);
			while (nextchar() && ce.Current >= '0' && ce.Current <= '9') {
				tmp.Append(ce.Current);
			}
			realSuffix();
			return ret("real-literal", tmp);
		}
		// END cut-n-paste almost
		return ret("integer-literal", tmp);
	}

	private bool integerSuffix() {
		if (ce.Current == 'u' || ce.Current == 'U') {
			tmp.Append(ce.Current);
			if (nextchar() && (ce.Current == 'l' || ce.Current == 'L')) {
				tmp.Append(ce.Current);
				nextchar();
				return true;
			}
			return true;
		}
		if (ce.Current == 'l' || ce.Current == 'L') {
			tmp.Append(ce.Current);
			if (nextchar() && (ce.Current == 'u' || ce.Current == 'U')) {
				tmp.Append(ce.Current);
				nextchar();
				return true;
			}
			return true;
		}
		return false;
	}

	private bool realSuffix() {
		switch (ce.Current) {
		case 'M':
		case 'm':
		case 'D':
		case 'd':
		case 'F':
		case 'f':
			tmp.Append(ce.Current);
			nextchar();
			return true;
		}
		return false;
	}

	private char escapeChar(ref bool errorFlag) {
		if (ce.Current != '\\') {
			errorFlag = true;
			return '\xffff';
		}
		if (!nextchar()) {
			errorFlag = true;
			return '\xffff';
		}
		tmp.Append(ce.Current);
		switch (ce.Current) {
		default:
			errorFlag = true;
			nextchar();
			return '\xffff';
		case '\'':
			errorFlag = false;
			nextchar();
			return '\'';
		case '\"':
			errorFlag = false;
			nextchar();
			return '\"';
		case '\\':
			errorFlag = false;
			nextchar();
			return '\\';
		case '0':
			errorFlag = false;
			nextchar();
			return '\0';
		case 'a':
			errorFlag = false;
			nextchar();
			return '\a';
		case 'b':
			errorFlag = false;
			nextchar();
			return '\b';
		case 'f':
			errorFlag = false;
			nextchar();
			return '\f';
		case 'n':
			errorFlag = false;
			nextchar();
			return '\n';
		case 'r':
			errorFlag = false;
			nextchar();
			return '\r';
		case 't':
			errorFlag = false;
			nextchar();
			return '\t';
		case 'v':
			errorFlag = false;
			nextchar();
			return '\v';
		case 'x':
			errorFlag = false;
			return hexEscape(ref errorFlag);
		case 'u':
		case 'U':
			errorFlag = false;
			char t = unicodeEscape(ref errorFlag);
			nextchar();
			return t;
		}
	}

	private char hexEscape(ref bool errorFlag) {
		if (ce.Current != 'x') {
			errorFlag = true;
			return '\uffff';
		}
		int acc = 0;
		int count;
		for (count = 0; nextchar() && count < 4; count++) {
			switch (ce.Current) {
			default:
				break;
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9':
				tmp.Append(ce.Current);
				acc = (acc << 4) + ce.Current - '0';
				continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
				tmp.Append(ce.Current);
				acc = (acc << 4) + ce.Current - 'a' + 10;
				continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
				tmp.Append(ce.Current);
				acc = (acc << 4) + ce.Current - 'A' + 10;
				continue;
			}
			break;
		}
		if (count > 0) {
			errorFlag = false;
			return (char)acc;
		}
		errorFlag = true;
		return '\uffff';
	}

	private char unicodeEscape(ref bool errorFlag) {
		if (ce.Current != 'u' && ce.Current != 'U') {
			errorFlag = true;
			return '\uffff';
		}
		int len;
		if (ce.Current == 'U') {
			len = 8;
		} else {
			len = 4;
		}
		int acc = 0;
		for (int i = 0; i < len; i++) {
			if (!nextchar()) {
				errorFlag = true;
				return '\uffff';
			}
			tmp.Append(ce.Current);
			switch (ce.Current) {
			default:
				errorFlag = true;
				return '\uffff';
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9':
				acc = (acc << 4) + ce.Current - '0';
				break;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
				acc = (acc << 4) + ce.Current - 'a' + 10;
				break;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
				acc = (acc << 4) + ce.Current - 'A' + 10;
				break;
			}
		}
		errorFlag = false;
		return (char)acc;
	}

	protected bool nextchar() {
		if (ce.MoveNext()) {
			return true;
		} else {
			atEOI = true;
			return false;
		}
	}

	private InputElement _current;
	public override InputElement Current {
		get {
			if (success) {
				return _current;
			} else {
				throw new System.InvalidOperationException();
			}
		}
	}

	object System.Collections.IEnumerator.Current {
		get {
			return Current;
		}
	}

	public virtual void Reset() {
	}
}

public class PreprocessorInputElementEnumerator : Char2InputElementEnumerator {
	public PreprocessorInputElementEnumerator(CharEnumerator ce, string file) 
		: base(ce, file) {
		// do nothing special
	}

	protected override string keyword(string s) {
		return PPKeywordHelp.keywordTag(s);
	}

	override protected bool stringLiteral() {
		for (;;) {
			if (!nextchar()) {
				return malformed("string-literal", tmp);
			}
			switch (ce.Current) {
			case '\u000d':
			case '\u000a':
			case '\u2028':
			case '\u2029':
				return malformed("string-literal", tmp);
			case '"':
				nextchar();
				return ret("string-literal", tmp);
			default:
				tmp.Append(ce.Current);
				break;
			}
		}
	}
}
