OBJ = ..\..\..\..\obj\Trusted\BootLoader
BUILD = ..\..\..\..\..\base\build

AS = $(BUILD)\x86_x86\ml.exe
LINK16 = $(BUILD)\x86_x86\link16.exe

ASM = etfs.asm
OBJS = $(OBJ)\Etfs_BS.obj

all: $(OBJ) $(OBJ)\etfs.bin

$(OBJ):
  mkdir $(OBJ)

.asm{$(OBJS)}.obj:
	$(AS) /nologo /c /omf /Cp /AT /Fl$*.lst /Fo$*.obj $<

$(OBJ)\etfs.bin: $(OBJS)
	$(LINK16) /nologo /tiny $(OBJS),$(OBJ)\etfs.bin;

clean:
	cd $(OBJ)
	del *.lst *.obj *.bin
