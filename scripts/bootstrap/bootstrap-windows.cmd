@echo off
setlocal
set "BASH_EXE="
for /f "delims=" %%G in ('where git.exe 2^>nul') do if not defined BASH_EXE (
  for %%B in ("%%~dpG..\bin\bash.exe") do if exist "%%~fB" set "BASH_EXE=%%~fB"
)
if not defined BASH_EXE if exist "C:\Program Files\Git\bin\bash.exe" set "BASH_EXE=C:\Program Files\Git\bin\bash.exe"
if not defined BASH_EXE if exist "C:\msys64\usr\bin\bash.exe" set "BASH_EXE=C:\msys64\usr\bin\bash.exe"
if not defined BASH_EXE (
  echo error: bootstrap-windows.cmd requires Git Bash or MSYS2 bash.exe 1>&2
  exit /b 1
)
pushd "%~dp0"
"%BASH_EXE%" "./bootstrap-windows.sh" %*
set "BOOTSTRAP_RC=%ERRORLEVEL%"
popd
exit /b %BOOTSTRAP_RC%
