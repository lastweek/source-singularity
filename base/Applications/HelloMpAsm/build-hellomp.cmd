
mkdir obj

cl.exe /nologo /c /Oxs /GFy /Gd /Gy /W3 /Zi /Zl /GS- /I..\include /FAsc  /Faobj\HelloMpAsm.lst  /Fdobj\HelloMpAsm.pdb  /Foobj\HelloMpAsm.obj HelloMpAsm.cpp 

link /nologo /out:obj\HelloMpAsm.exe obj\HelloMpAsm.obj /pdb:obj\HelloMpAsm.pdb /map:obj\HelloMpAsm.map  /fixed /entry:main /incremental:no  /machine:ix86 /subsystem:native /ignore:4078 /merge:.rdata=.data /merge:.bss=.data /merge:.data=.text

rename obj\hellompasm.pdb a
rename obj\a HelloMpAsm.pdb
