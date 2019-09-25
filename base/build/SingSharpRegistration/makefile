all: IPropertyPane.dll \
  ContractsPropertyPane.dll \
  ITaskManager.dll \
  Microsoft.VisualStudio.OLE.Interop.dll \
  Microsoft.VisualStudio.Designer.Interfaces.dll \
  Microsoft.VisualStudio.Shell.Interop.dll  \
  Microsoft.VisualStudio.TextManager.Interop.dll \
  Microsoft.VisualStudio.Package.dll \
  Microsoft.VisualStudio.IntegrationHelper.dll \
  PropertyPage.dll \
  1033\PropertyPageUI.dll \
  System.Compiler.dll \
  System.Compiler.Runtime.dll \
  System.Compiler.Framework.dll \
  Microsoft.SingSharp.Runtime.dll \
  Microsoft.SingSharp.dll \
  Mscorlib.Contracts.dll \
  System.Contracts.dll \
  System.Compiler.Contracts.dll \
  System.Compiler.Framework.Contracts.dll \
  1033\Microsoft.SingSharp.resources.dll \
  TaskManager.dll \
  1033\TaskManagerUI.dll \


ContractsPropertyPane.dll: ..\sgc\$@
  Register ..\sgc\$@ $@
  
IPropertyPane.dll: ..\sgc\$@
  CopyBits ..\sgc\$@ $@

ITaskManager.dll: ..\sgc\$@
  CopyBits ..\sgc\$@ $@

Microsoft.VisualStudio.OLE.Interop.dll: ..\sgc\$@  
  CopyBits ..\sgc\$@ $@

Microsoft.VisualStudio.Designer.Interfaces.dll: ..\sgc\$@  
  CopyBits ..\sgc\$@ $@

Microsoft.VisualStudio.Shell.Interop.dll: ..\sgc\$@
  CopyBits ..\sgc\$@ $@

Microsoft.VisualStudio.TextManager.Interop.dll: ..\sgc\$@
  CopyBits ..\sgc\$@ $@
  
Microsoft.VisualStudio.Package.dll: ..\sgc\$@
  Register ..\sgc\$@ $@
  
Microsoft.VisualStudio.IntegrationHelper.dll: ..\sgc\$@
  CopyBits ..\sgc\$@ $@
  
PropertyPage.dll: ..\sgc\$@
  CopyBits ..\sgc\$@ $@

1033\PropertyPageUI.dll: ..\sgc\PropertyPageUI.dll
  if not exist 1033 mkdir 1033
  copy ..\sgc\PropertyPageUI.dll $@
    
System.Compiler.dll : ..\sgc\$@
  CopyBits ..\sgc\$@ $@

System.Compiler.Runtime.dll : ..\sgc\$@  
  CopyBits ..\sgc\$@ $@

System.Compiler.Framework.dll : ..\sgc\$@
  CopyBits ..\sgc\$@ $@

Microsoft.SingSharp.Runtime.dll : ..\sgc\$@
  CopyBits ..\sgc\$@ $@

Microsoft.SingSharp.dll : ..\sgc\$@
  Register ..\sgc\$@ $@

Mscorlib.Contracts.dll : ..\sgc\$@
  CopyBits ..\sgc\$@ $@

System.Contracts.dll : ..\sgc\$@
  CopyBits ..\sgc\$@ $@

System.Compiler.Contracts.dll : ..\sgc\$@
  CopyBits ..\sgc\$@ $@

System.Compiler.Framework.Contracts.dll : ..\sgc\$@
  CopyBits ..\sgc\$@ $@

1033\Microsoft.SingSharp.resources.dll: ..\sgc\Microsoft.SingSharp.resources.dll
  if not exist 1033 mkdir 1033
  copy ..\sgc\Microsoft.SingSharp.resources.dll $@
  rem devenv /setup
  
TaskManager.dll: ..\sgc\$@ 
  CopyBits ..\sgc\$@ $@
  
1033\TaskManagerUI.dll: ..\sgc\TaskManagerUI.dll
  if not exist 1033 mkdir 1033
  copy ..\sgc\TaskManagerUI.dll $@
  
