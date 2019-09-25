all: uclient.exe userver.exe

CFLAGS=$(CFLAGS) /Ox /D_X86_
LIBS=ntdll.lib
HOST_LINKFLAGS= $(HOST_LINKFLAGS)

{.}.c.obj:
    cl /c $(CFLAGS) /Fo$@ $<

{.}.obj.exe:
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

uclient.obj: uclient.c ulpc.h

userver.obj: userver.c ulpc.h

clean:
    -del /q *.obj *.exe *.pdb
