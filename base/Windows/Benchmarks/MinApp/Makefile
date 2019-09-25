#
# Attempt to build minimal sized executables.
# Makes static and dynamically-linked versions of both C and CPP programs.
#
all:
    cl /O2 /MT /Gy- /I..\..\inc HelloC.c /FoHelloCStatic.obj \
    /link /libpath:..\..\lib /incremental:no /subsystem:console \
    /out:HelloCStatic.exe

    cl /O2 /MD /Gy- /I..\..\inc HelloC.c /FoHelloCDynamic.obj \
    /link /libpath:..\..\lib /incremental:no /subsystem:console \
    /out:HelloCDynamic.exe

    cl /O2 /MT /Gy- /I..\..\inc HelloCPP.cpp /FoHelloCPPStatic.obj \
    /link /libpath:..\..\lib /incremental:no /subsystem:console \
    /out:HelloCPPStatic.exe

    cl /O2 /MD /Gy- /I..\..\inc HelloCPP.cpp /FoHelloCPPDynamic.obj \
    /link /libpath:..\..\lib /incremental:no /subsystem:console \
    /out:HelloCPPDynamic.exe

#
# Tool to measure stats of above exes.
#
    cl /O2 /MT /Gy- /I..\..\inc ProcStats.c /FoProcStats.obj \
    /link /libpath:..\..\lib psapi.lib /incremental:no /subsystem:console \
    /out:ProcStats.exe

clean:
    @-del /f /q *~ 2> nul
    @-del /f /q *.obj 2> nul
    @-del /f /q *.exe 2> nul
