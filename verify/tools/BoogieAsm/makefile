#
# Copyright (c) 2007 Microsoft Corporation.   All rights reserved.
#

BUILD = ..\..\build
FSC = $(BUILD)\fsc -g
FSLEX = $(BUILD)\fslex
FSYACC = $(BUILD)\fsyacc
OBJ = ..\..\obj\boogieasm
BIN = ..\..\bin\boogieasm
CORE = .

SRC = \
	$(CORE)\ast.fs \
	$(CORE)\parse_util.fs \
	$(OBJ)\parse.fs \
	$(OBJ)\lex.fs \
	$(CORE)\main.fs \

all: $(OBJ) $(BIN) $(BIN)\boogieasm.exe

$(OBJ):
	mkdir $(OBJ)

$(BIN):
	mkdir $(BIN)

$(OBJ)\lex.fsi $(OBJ)\lex.fs: $(CORE)\lex.fsl
	$(FSLEX) $(CORE)\lex.fsl -o $(OBJ)\lex.fs

$(OBJ)\parse.fsi $(OBJ)\parse.fs: $(CORE)\parse.fsy
  	$(FSYACC) -v $(CORE)\parse.fsy -o $(OBJ)\parse.fs

$(BIN)\boogieasm.exe: $(SRC)
	$(FSC) --standalone --mlcompatibility -O $(SRC) -o $(BIN)\boogieasm.exe -r FSharp.PowerPack.dll

clean:
	del /q $(BIN)\boogieasm.exe
	del /q $(OBJ)\*.fs
