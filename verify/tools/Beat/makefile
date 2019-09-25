#
# Copyright (c) 2007 Microsoft Corporation.   All rights reserved.
#

BUILD = ..\..\build
FSC = $(BUILD)\fsc -g
FSLEX = $(BUILD)\fslex
FSYACC = $(BUILD)\fsyacc
OBJ = ..\..\obj\beat
BIN = ..\..\bin\beat
SRC = .

BEAT_SOURCES = \
	$(SRC)\ast.fs \
	$(SRC)\parse_util.fs \
	$(OBJ)\parse.fs \
	$(OBJ)\lex.fs \
	$(SRC)\main.fs \

beat: $(OBJ) $(BIN) $(BIN)\beat.exe

$(OBJ):
	mkdir $(OBJ)

$(BIN):
	mkdir $(BIN)

$(OBJ)\lex.fsi $(OBJ)\lex.fs: $(OBJ) $(SRC)\lex.fsl
	$(FSLEX) $(SRC)\lex.fsl -o $(OBJ)\lex.fs

$(OBJ)\parse.fsi $(OBJ)\parse.fs: $(OBJ) $(SRC)\parse.fsy
	$(FSYACC) -v $(SRC)\parse.fsy -o $(OBJ)\parse.fs

$(BIN)\beat.exe: $(BEAT_SOURCES)
	$(FSC) --standalone --mlcompatibility -O $(BEAT_SOURCES) -o $(BIN)\beat.exe -r FSharp.PowerPack.dll


