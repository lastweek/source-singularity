Option Explicit
on error resume next
Dim objShell, key, ipsecName, objADsDomain, strADsPath, objADs, objADs2, ScriptHost, objRegister, strComputer, ArgObj, wbemComputerSystem, wbemObjectSet, wbemObject, Domain, ds_policy_path

const ERROR_NOREGKEY = -2147024894
const DOMAIN_IPSEC_VERSION_OBJECT_DN = "CN=ipsecFilter{aa3d274e-da18-45c9-907d-9f6ba31ae361},CN=IP Security,CN=System,"
const LOCAL_IPSEC_VERSION_KEY = "SOFTWARE\Policies\Microsoft\Windows\IPSec\Policy\Cache\ipsecFilter{aa3d274e-da18-45c9-907d-9f6ba31ae361}"
const DS_IPSEC_PATH_KEY = "SOFTWARE\Policies\Microsoft\Windows\IPSec\GPTIPSECPolicy"

Const HKEY_LOCAL_MACHINE = &H80000002


'''''''''''''''''''''''''''''''''''''''''''''''''''''''''
' Make sure we're running from cscript instead of wscript
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''
ScriptHost = WScript.FullName
ScriptHost = Right(ScriptHost, Len(ScriptHost) - InStrRev(ScriptHost, "\"))

If (UCase(ScriptHost) = "WSCRIPT.EXE") Then
    WScript.Echo "This script does not work with WScript."
    WScript.Echo "To run this script using CScript, type: ""CScript.exe " & WScript.ScriptName & " [target]"""
    wscript.quit
end if


''''''''''''''''''''''''''''''''
' Get the computer name to check
''''''''''''''''''''''''''''''''
Set ArgObj = WScript.Arguments
If ArgObj.Count > 1 Then
    WScript.Echo "To run this script using CScript, type: ""CScript.exe " & WScript.ScriptName & " [target]"""
    wscript.quit
    WScript.Quit
End If

if ArgObj.Count = 1 Then
    strComputer = ArgObj.Item(0)
else
    strComputer = "localhost"
End If


''''''''''''''''''''''''''''''''
' Get the domain of the computer
''''''''''''''''''''''''''''''''
Set wbemComputerSystem = GetObject("winmgmts:{impersonationLevel=impersonate}!\\" & strComputer)
if Err.Number <> 0 then
    wscript.echo strComputer & ": Error # " & CStr(Err.Number) & " " & Err.Description
    wscript.quit
end if

Set wbemObjectSet = wbemComputerSystem.InstancesOf("Win32_ComputerSystem")
if Err.Number <> 0 then
    wscript.echo strComputer & ": Error # " & CStr(Err.Number) & " " & Err.Description
    wscript.quit
end if

For Each wbemObject In wbemObjectSet
    domain = wbemObject.Domain
Next


''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
' Get the version information from the computer's registry
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
Set objRegister = GetObject("winmgmts:{impersonationLevel=impersonate}!\\" & strComputer & "\root\default:StdRegProv")
if Err.Number <> 0 then
    wscript.echo strComputer & ": Error # " & CStr(Err.Number) & " " & Err.Description
    wscript.quit
end if

objRegister.GetStringValue  HKEY_LOCAL_MACHINE, LOCAL_IPSEC_VERSION_KEY, "ipsecName", ipsecName
if Err.Number <> 0 then
    wscript.echo strComputer & ": Error # " & CStr(Err.Number) & " " & Err.Description
    wscript.quit
end if
' wscript.echo strComputer & ": Local version:  " & ipsecName


'''''''''''''''''''''''''''''''''''''''''''''''''''''''
' Get the version information from the Active Directory
'''''''''''''''''''''''''''''''''''''''''''''''''''''''
Set objADsDomain = GetObject("LDAP://" & domain)
if Err.Number <> 0 then
    wscript.echo strComputer & ": Error # " & CStr(Err.Number) & " " & Err.Description
    wscript.quit
end if

strADsPath = "LDAP://" & domain & "/" & DOMAIN_IPSEC_VERSION_OBJECT_DN & objADsDomain.distinguishedName
Set objADs = GetObject(strADsPath)
if Err.Number <> 0 then
    wscript.echo strComputer & ": Error # " & CStr(Err.Number) & " " & Err.Description
    wscript.quit
end if
' wscript.echo strComputer & ": Domain version: " & objADs.ipsecName


'''''''''''''''''''''''''''''''''''''''''''''''
' Get the policy name from the Active Directory
'''''''''''''''''''''''''''''''''''''''''''''''
Set objRegister = GetObject("winmgmts:{impersonationLevel=impersonate}!\\" & strComputer & "\root\default:StdRegProv")
if Err.Number <> 0 then
    wscript.echo strComputer & ": Error # " & CStr(Err.Number) & " " & Err.Description
    wscript.quit
end if

objRegister.GetStringValue  HKEY_LOCAL_MACHINE, DS_IPSEC_PATH_KEY, "DSIPSECPolicyPath", ds_policy_path
if Err.Number <> 0 then
    wscript.echo strComputer & ": Error # " & CStr(Err.Number) & " " & Err.Description
    wscript.quit
end if

strADsPath = "LDAP://" & domain & "/" & MID(ds_policy_path, 8)
Set objADs2 = GetObject(strADsPath)
if Err.Number <> 0 then
    wscript.echo strComputer & ": Error # " & CStr(Err.Number) & " " & Err.Description
    wscript.quit
end if
wscript.echo strComputer & ": " & objADs2.ipsecName


''''''''''''''''''''''''''''''''''''''''''''
' Compare local vs Active Directory versions
''''''''''''''''''''''''''''''''''''''''''''
if ipsecName = objADs.ipsecName then
    wscript.echo strComputer & ": IPsec policy is up-to-date."
else 
    wscript.echo strComputer & ": IPsec policy is not up-to-date."
end if