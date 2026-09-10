@echo off
setlocal

rem Windows cannot execute the extensionless POSIX bin\devhub file directly.
rem Route through sh so the existing wrapper keeps runtime/provenance admission.
set "SCRIPT_DIR=%~dp0"
if not "%DEVHUB_SH%"=="" goto devhub_have_shell
for /f "delims=" %%S in ('where sh.exe 2^>nul') do if "%DEVHUB_SH%"=="" set "DEVHUB_SH=%%S"
if not "%DEVHUB_SH%"=="" goto devhub_have_shell
echo error: DevHub requires sh.exe (for example, Git for Windows) 1>&2
exit /b 127

:devhub_have_shell
"%ComSpec%" /d /c call "%DEVHUB_SH%" "%SCRIPT_DIR%devhub" %*
exit /b %ERRORLEVEL%
