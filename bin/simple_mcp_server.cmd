@echo off
setlocal
set "SCRIPT_DIR=%~dp0"
set "RUNTIME=%SCRIPT_DIR%release\simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%SCRIPT_DIR%release\simple"
set "ENTRY=%SCRIPT_DIR%..\src\app\mcp\main.spl"
set "SIMPLE_LIB=%SCRIPT_DIR%..\src"
set "SIMPLE_LOG=error"
set "RUST_LOG=error"
"%RUNTIME%" "%ENTRY%" %* 2>nul
