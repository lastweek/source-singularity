'-----------------------------------------------------------------------
' Singularity RDK configuration tool
' (c) 2008 - Microsoft Corporation
'-----------------------------------------------------------------------


'-----------------------------------------------------------------------
' Splash

WScript.Echo "------------------------------------------------------------------"
WScript.Echo "-                                                                -"
WScript.Echo "-          S   I   N   G   U   L   A   R   I   T   Y             -"
WScript.Echo "-                                                                -"
WScript.Echo "-                          RDK 2.0                               -"
WScript.Echo "-                                                                -"
WScript.Echo "------------------------------------------------------------------"
WScript.Echo
WScript.Echo
WScript.Echo "This script will configure Singularity RDK build to the"
WScript.Echo "following location:"
WScript.Echo


'-----------------------------------------------------------------------
' Objects

set WshShell = WScript.CreateObject("WScript.Shell")
Set objShell = CreateObject("Shell.Application")


'-----------------------------------------------------------------------
' Running from this location

If WScript.Arguments.Count = 1 Then
	runningFrom = WScript.Arguments(0)
Else
	runningFrom = WshShell.CurrentDirectory
End If

WScript.Echo chr(9) & runningFrom


'-----------------------------------------------------------------------
' Wait for input

WScript.Echo
WScript.Echo "Press ENTER to start..."
WScript.StdIn.Read(1)



'-----------------------------------------------------------------------
WScript.Echo
WScript.Echo

'-----------------------------------------------------------------------
' Determine desktop location

Set objFolder = objShell.Namespace(&H0)
Set objFolderItem = objFolder.Self
desktop = objFolderItem.Path
CreateIcon desktop

Set objFolder = objShell.Namespace(&H17)
Set objFolderItem = objFolder.Self
programs = objFolderItem.Path
CreateIcon programs



Sub CreateIcon(base)
	On Error Resume Next
	'-----------------------------------------------------------------------
	' Add build icon to desktop
	set oShellLink = WshShell.CreateShortcut(base & "\Singularity RDK 2.0.lnk")
	'Define where you would like the shortcut to point to. This can be a program, Web site, etc.
	oShellLink.TargetPath = "%windir%\system32\cmd.exe"
	oShellLink.Arguments = "/k " & Chr(34) & "base\setenv.cmd" & Chr(34)
	oShellLink.WindowStyle = 1
	'Define what icon the shortcut should use. Here we use the explorer.exe icon.
	oShellLink.IconLocation = runningFrom & "\singularity.ico"
	oShellLink.Description = "Singularity environment build window"
	oShellLink.WorkingDirectory = runningFrom
	oShellLink.Save

	If Err <> 0 Then
		WScript.Echo
		WScript.Echo "*** ERROR: A problem occurred while creating the shortcut."
		WScript.Echo chr(9) & "Please make sure you ran this program with administrator privileges."
		WScript.Echo
	End If	
End Sub