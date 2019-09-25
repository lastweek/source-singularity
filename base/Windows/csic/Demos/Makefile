B=Debug/
CSC=csc -nologo
CSCFLAGS=-d:DEBUG -debug -lib:Debug -lib:base -lib:parser

all:	find-typeswitch.exe find-typeswitch.exe.config \
	find-assert.exe find-assert.exe.config

find-typeswitch.exe:	Demos/find-typeswitch.cs
	$(CSC) $(CSCFLAGS) /r:base.dll,parser.dll /out:$@ Demos\find-typeswitch.cs

find-typeswitch.exe.config:	Demos/config;	cmd /C copy Demos\config $@

find-assert.exe:	Demos/find-assert.cs
	$(CSC) $(CSCFLAGS) /r:base.dll,parser.dll /out:$@ Demos\find-assert.cs

find-assert.exe.config:	Demos/config;	cmd /C copy Demos\config $@

clean:
	del /q find-typeswitch.* find-assert.*
