@echo off
setlocal
set "SCRIPT_DIR=%~dp0"
for %%I in ("%SCRIPT_DIR%..") do set "REPO_ROOT=%%~fI"
set "RUNTIME=%REPO_ROOT%\src\compiler_rust\target\bootstrap\simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%REPO_ROOT%\bin\simple.cmd"
set "ENTRY=%REPO_ROOT%\src\app\mcp\main.spl"
set "SIMPLE_LIB=%REPO_ROOT%\src"
"%RUNTIME%" run "%ENTRY%" %* 2>nul
exit /b %ERRORLEVEL%
