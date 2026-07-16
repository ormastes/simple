@echo off
setlocal EnableExtensions

set "RESOLVER=%~dp0resolve_native_tool.ps1"
set "POWERSHELL=%SystemRoot%\System32\WindowsPowerShell\v1.0\powershell.exe"
if not exist "%RESOLVER%" goto :missing
if not exist "%POWERSHELL%" goto :missing

set "EXE="
for /f "usebackq delims=" %%P in (`"%POWERSHELL%" -NoProfile -NonInteractive -ExecutionPolicy Bypass -File "%RESOLVER%" -Kind simple`) do if not defined EXE set "EXE=%%P"
if not defined EXE goto :missing

"%EXE%" %*
exit /b %ERRORLEVEL%

:missing
echo error: no admitted pure-Simple Windows runtime found 1>&2
exit /b 127
