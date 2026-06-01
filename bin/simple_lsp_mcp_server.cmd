@echo off
setlocal
set "SCRIPT_DIR=%~dp0"
for %%I in ("%SCRIPT_DIR%..") do set "REPO_ROOT=%%~fI"
set "RUNTIME=%REPO_ROOT%\src\compiler_rust\target\bootstrap\simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%REPO_ROOT%\bin\simple.cmd"
set "ENTRY=%REPO_ROOT%\src\app\simple_lsp_mcp\main.spl"
set "SIMPLE_LIB=%REPO_ROOT%\src"
set "SIMPLE_BINARY=%RUNTIME%"
"%RUNTIME%" run "%ENTRY%" %* 2>nul
exit /b %ERRORLEVEL%
