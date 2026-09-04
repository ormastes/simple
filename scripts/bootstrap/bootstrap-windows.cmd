@echo off
setlocal
set "BOOTSTRAP_BASH="

rem Prefer the Bash shipped beside Git.  Windows' System32 bash.exe is the
rem WSL launcher and cannot consume the native path passed below.
for /f "delims=" %%G in ('where git.exe 2^>nul') do call :bash_from_git "%%~dpG"
if not defined BOOTSTRAP_BASH if exist "C:\msys64\usr\bin\bash.exe" set "BOOTSTRAP_BASH=C:\msys64\usr\bin\bash.exe"
if not defined BOOTSTRAP_BASH for /f "delims=" %%B in ('where bash.exe 2^>nul') do call :bash_from_path "%%~fB"

if not defined BOOTSTRAP_BASH (
  echo error: bootstrap-windows.cmd requires Git Bash or MSYS2 bash.exe 1>&2
  exit /b 1
)
"%BOOTSTRAP_BASH%" "%~dp0bootstrap-windows.sh" %*
exit /b %ERRORLEVEL%

:bash_from_git
if defined BOOTSTRAP_BASH exit /b 0
if exist "%~1..\bin\bash.exe" set "BOOTSTRAP_BASH=%~1..\bin\bash.exe"
exit /b 0

:bash_from_path
if defined BOOTSTRAP_BASH exit /b 0
if /i "%~1"=="%SystemRoot%\System32\bash.exe" exit /b 0
if /i "%~1"=="%LocalAppData%\Microsoft\WindowsApps\bash.exe" exit /b 0
set "BOOTSTRAP_BASH=%~1"
exit /b 0
