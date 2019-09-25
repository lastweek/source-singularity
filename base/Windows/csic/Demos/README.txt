To build the demos:

	cd .../csharp/compiler
	nmake	(builds lcsc.exe)
	nmake -f Demos/Makefile

To run the demos from .../csharp/compiler:

Searching for Idiomatic Usage

	./find-assert parser/disambiguate.cs
	./find-typeswitch base/Imports.cs

Emitting XML

	./lcsc -visitor:XML Demos/hello.cs

Extending C#

	Show grammar in Excel spreadsheet, perhaps nodes in AST.cs
	./lcsc Demos/typeswitch-sample.cs

Source-to-Source Transformations

	./lcsc -visitor:source Demos/hello.cs
	./lcsc -visitor:typeswitch_source,typeswitch/typeswitch.dll Demos/typeswitch-sample.cs

drh@microsoft.com

