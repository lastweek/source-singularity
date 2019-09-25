@echo off

set DDKDIR=c:\WINDDK\2600.1106

set NTSRC=c:\ntsrc
set INCLUDE=%INCLUDE%;%NTSRC%\public\sdk\inc
set LIB=%LIB%;%DDKDIR%\lib\wxp\i386

doskey VC=cd "C:\Program Files\Microsoft Visual Studio .NET 2003\Vc7"
doskey LPC=cd c:\ntsrc\base\ntos\lpc
doskey PUB=cd c:\ntsrc\base\published
doskey DDK=cd %DDKDIR%
doskey WORK=cd c:\work\lrpc\example2
doskey ALIAS=echo "VC | LPC | PUB | DDK | WORK"

