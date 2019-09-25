DOTNETDIR=$(WINDIR)\Microsoft.NET\Framework\v2.0.50727
BIN=bin^\
B=Debug^\
RM=del /q
ICONT=$(BIN)nticont -u
CSC="$(DOTNETDIR)\csc" -nologo
CSCFLAGS=-d:DEBUG -debug -lib:Debug -lib:base

GRAMMAR = \
	csharp-gram.xls \
	typeswitch\typeswitch-gram.xls

PARSER = \
	parser\disambiguate.cs \
	parser\Enumerators.cs \
	parser\Filters.cs \
	parser\glr.cs \
	parser\Image.cs \
	parser\InputElementEnumerator.cs \
	parser\KeywordHelp.cs \
	parser\lexer.cs \
	parser\parse2AST.cs \
	parser\parser.cs \
	parser\PPKeywordHelp.cs \
	parser\Preprocessor.cs \
	parser\tables.cs \
	parser\UnicodeHelp.cs

BASE = \
	base\AST.cs base\typeswitch-AST.cs \
	base\ASTRoot.cs \
	base\Attributes.cs \
	base\BartokReader.cs \
	base\BuiltinTypes.cs \
	base\Debug.cs \
	base\Imports.cs \
	base\InputElement.cs \
	base\Lists.cs \
	base\MessageWriter.cs \
	base\NullReader.cs \
	base\ReflectionReader.cs \
	base\SymbolRoot.cs \
	base\Symbols.cs \
	base\SymbolTable.cs \
	base\Tracking.cs \
	base\Types.cs \
	base\VisitorDelegate.cs \

BROWSER = \
	Browser\Browser.cs \
	Browser\BrowserForm.cs \
	Browser\BrowserVisitor.cs \
	Browser\CodeDomTreeView.cs \
	Browser\HistoryView.cs \
	Browser\ILTextView.cs \
	Browser\ObjectTreeView.cs \
	Browser\ObjectBrowserForm.cs \
	Browser\ParentView.cs \
	Browser\SourceTabView.cs \
	Browser\SourceTextView.cs \
	Browser\tracking-ilgen.cs

GENS = \
	$(BIN)Excel.dll \
	$(BIN)excel2gram.exe \
	$(BIN)mkKeyword.exe \
	$(BIN)mkOperator.exe \
	$(BIN)mkUnicode.exe \
	$(BIN)mkvisitor.exe \
	$(BIN)pgen.exe \
	$(BIN)tlist.exe \
	base\base.dll \
	bind\bind.dll \
	codedom\codedom.dll \
	parser\parser.dll \
	$BSHDocVw.dll \
	rewrite\rewrite.dll \
	typecheck\typecheck.dll \
	xml\xml.dll \
	csharp-gram.keywords \
	csharp.g \
	parser\KeywordHelp.cs \
	keywords.txt \
	lcsc.exe \
	base\Lists.cs \
	operators.txt \
	parser\parse2AST.cs \
	parser\PPKeywordHelp.cs \
	parser\UnicodeHelp.cs

.SUFFIXES:

all:: lcsc.exe $(BIN)mkvisitor.exe operators.txt \
		bind\bind.dll \
		Browser\Browser.dll \
		codedom\codedom.dll \
		Compiler\Compiler.dll \
		emit\emit.dll \
		ilgen\ilgen.dll \
		parser\parser.dll \
		rewrite\rewrite.dll \
		sortmembers\sortmembers.dll \
		source\source.dll \
		typecheck\typecheck.dll \
		xml\xml.dll

prereqs:	$(PARSER) $(BASE)

clean::
	-$(RM) $(GENS) $B*.pdb $(BIN)*.pdb *.pdb

clobber:
	$(RM) /s base.dll
	$(RM) /s bind.dll
	$(RM) /s Browser.dll
	$(RM) /s codedom.dll
	$(RM) /s Compiler.dll
	$(RM) /s emit.dll
	$(RM) /s ilgen.dll
	$(RM) /s mkvisitor.dll
	$(RM) /s parser.dll
	$(RM) /s rewrite.dll
	$(RM) /s sortmembers.dll
	$(RM) /s source.dll
	$(RM) /s typecheck.dll
	$(RM) /s typeswitch.dll
	$(RM) /s xml.dll
	$(RM) /s base.pdb
	$(RM) /s bind.pdb
	$(RM) /s Browser.pdb
	$(RM) /s codedom.pdb
	$(RM) /s Compiler.pdb
	$(RM) /s emit.pdb
	$(RM) /s ilgen.pdb
	$(RM) /s mkvisitor.pdb
	$(RM) /s parser.pdb
	$(RM) /s rewrite.pdb
	$(RM) /s sortmembers.pdb
	$(RM) /s source.pdb
	$(RM) /s typecheck.pdb
	$(RM) /s typeswitch.pdb
	$(RM) /s xml.pdb
	$(RM) csic.exe
	$(RM) csic.pdb
	$(RM) parser\tables.cs

lcsc.exe: driver.cs Compiler\Compiler.dll base\base.dll bind\bind.dll ilgen\ilgen.dll typecheck\typecheck.dll
	$(CSC) $(CSCFLAGS) -lib:Compiler,ilgen,bind,typecheck /r:Compiler.dll,base.dll,bind.dll,ilgen.dll,typecheck.dll /out:$@ driver.cs

Compiler\Compiler.dll:	Compiler\Compiler.cs parser\parser.dll base\base.dll
	$(CSC) $(CSCFLAGS) -lib:parser /r:parser.dll,base.dll /out:$@ /target:library /out:$@ Compiler\Compiler.cs

parser\parser.dll: $(PARSER) base\base.dll
	$(CSC) $(CSCFLAGS) /r:base.dll /target:library /out:$@ $(PARSER)

base\base.dll: $(BASE) $BSHDocVw.dll
	$(CSC) $(CSCFLAGS) /r:Bartok.MSIL.dll,SHDocVw.dll /target:library /out:$@ $(BASE)

$BSHDocVw.dll:
	tlbimp %WINDIR%/system32/shdocvw.dll /out:$@

bind\bind.dll: bind\bind.cs base\base.dll bind\csi-bind.cs
	$(CSC) $(CSCFLAGS) /target:library /r:base.dll /out:$@ bind\bind.cs bind\csi-bind.cs

typecheck\typecheck.dll: typecheck\typecheck.cs parser\parser.dll bind\bind.dll base\base.dll typecheck\csi-typecheck.cs
	$(CSC) $(CSCFLAGS) /target:library -lib:bind -lib:parser /r:parser.dll,bind.dll,base.dll /out:$@ typecheck\typecheck.cs typecheck\csi-typecheck.cs

xml\xml.dll: xml\xml.cs base\base.dll
	$(CSC) $(CSCFLAGS) /r:base.dll /target:library /out:$@ xml\xml.cs

codedom\codedom.dll: codedom\codedom2.cs base\base.dll
	$(CSC) $(CSCFLAGS) /target:library /r:base.dll /out:$@ codedom\codedom2.cs

emit\emit.dll: emit\emit.cs emit\gen.cs emit\execute.cs emit\save.cs base\base.dll
	$(CSC) $(CSCFLAGS) /target:library /r:base.dll /out:$@ emit\emit.cs emit\gen.cs emit\execute.cs emit\save.cs

ilgen\ilgen.dll: ilgen\ilgen.cs emit\emit.dll source\source.dll base\base.dll ilgen\csi-ilgen.cs
	$(CSC) $(CSCFLAGS) /target:library -lib:source -lib:emit /r:emit.dll,source.dll,base.dll,Bartok.MSIL.dll /out:$@ ilgen\ilgen.cs ilgen\csi-ilgen.cs

rewrite\rewrite.dll: rewrite\rewrite.cs base\base.dll
	$(CSC) $(CSCFLAGS) /nowarn:0642 /target:library /r:base.dll /out:$@ rewrite\rewrite.cs

source\source.dll: source\source.cs base\base.dll
	$(CSC) $(CSCFLAGS) /target:library /r:base.dll /out:$@ source\source.cs

sortmembers\sortmembers.dll: sortmembers\sortmembers.cs base\base.dll
	$(CSC) $(CSCFLAGS) /target:library /r:base.dll /out:$@ sortmembers\sortmembers.cs

Browser\Browser.dll: $(BROWSER) codedom\codedom.dll ilgen\ilgen.dll base\base.dll
	$(CSC) $(CSCFLAGS) /target:library -lib:codedom -lib:ilgen /r:codedom.dll,ilgen.dll,base.dll /out:$@ $(BROWSER)

$(BIN)tlist.exe: tlist.cs
	$(CSC) $(CSCFLAGS) /out:$@ tlist.cs

$(BIN)mkvisitor.exe:	mkvisitor.cs
	$(CSC) $(CSCFLAGS) /r:base.dll /out:$@ mkvisitor.cs

base\Lists.cs: $(BIN)tlist.exe Makefile
	$(BIN)tlist accessor_declaration attribute attribute_section expression \
		argument statement declarator \
		declaration using_directive parameter type event_accessor \
		enum_member_declaration catch_clause switch_section switch_label switch_expression \
		typeswitch_section variable_initializer named_argument compilation_unit \
		int string InputElement VisitorDelegate InterfaceType Symbol Method Formal AST \
		type_parameter type_parameter_constraints_clause >$@

operators.txt: $(BIN)mkOperator.exe OperatorData.txt
	$(BIN)mkOperator < OperatorData.txt > operators.txt

parser\PPKeywordHelp.cs: $(BIN)mkKeyword.exe ppkeywords.txt
	$(BIN)mkKeyword PPKeywordHelp < ppkeywords.txt > $@

parser\KeywordHelp.cs: $(BIN)mkKeyword.exe csharp-gram.keywords
	$(BIN)mkKeyword KeywordHelp < csharp-gram.keywords > $@

parser\UnicodeHelp.cs: $(BIN)mkUnicode.exe UnicodeData.txt
	$(BIN)mkUnicode < UnicodeData.txt > $@

parser\parse2AST.cs: $(GRAMMAR) $(BIN)excel2gram.exe
	$(BIN)excel2gram rewrite $(GRAMMAR) > $@

csharp.g: $(GRAMMAR) $(BIN)excel2gram.exe
	$(BIN)excel2gram gram $(GRAMMAR) > csharp.g

parser\tables.cs: $(BIN)pgen.exe csharp.g
	$(BIN)pgen < csharp.g > $@

csharp-gram.keywords: $(GRAMMAR) $(BIN)excel2gram.exe
	$(BIN)excel2gram keywords $(GRAMMAR) > csharp-gram.keywords

PGENSRCS = \
	glr.icn \
	main.icn

$(BIN)pgen.exe: $(PGENSRCS)
	$(ICONT) -o $@ $(PGENSRCS)

# Excel.dll is checked in.
# $(BIN)Excel.dll:
#	tlbimp /out:$@ $(EXCEL)

$(BIN)excel2gram.exe: excel2gram.cs $(BIN)Excel.dll
	$(CSC) $(CSCFLAGS) /out:$@ /r:$(BIN)Excel.dll excel2gram.cs

$(BIN)mkKeyword.exe: mkKeyword.icn
	$(ICONT) -o $@ mkKeyword.icn

$(BIN)mkOperator.exe: mkOperator.icn
	$(ICONT) -o $@ mkOperator.icn

$(BIN)mkUnicode.exe: mkUnicode.icn
	$(ICONT) -o $@ mkUnicode.icn

# typeswitch

all::	typeswitch\typeswitch.dll

typeswitch\typeswitch.dll: \
	typeswitch\typeswitch-bind.cs \
	typeswitch\typeswitch-typecheck.cs \
	typeswitch\typeswitch-rewrite.cs \
	typeswitch\typeswitch-ilgen.cs \
	typeswitch\typeswitch-source.cs \
	base\base.dll \
	parser\parser.dll \
	bind\bind.dll \
	typecheck\typecheck.dll \
	rewrite\rewrite.dll \
	emit\emit.dll \
	ilgen\ilgen.dll \
	source\source.dll
	$(CSC) $(CSCFLAGS) /target:library \
		/r:base.dll,bind\bind.dll,typecheck\typecheck.dll,rewrite\rewrite.dll \
		/r:ilgen\ilgen.dll,emit\emit.dll,source\source.dll /out:$@ \
		typeswitch\typeswitch-bind.cs \
		typeswitch\typeswitch-typecheck.cs \
		typeswitch\typeswitch-rewrite.cs \
		typeswitch\typeswitch-ilgen.cs \
		typeswitch\typeswitch-source.cs

clean::	
	-$(RM) typeswitch\typeswitch.dll
