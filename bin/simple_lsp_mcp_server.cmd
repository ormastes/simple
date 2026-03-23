@echo off
setlocal

set "SCRIPT_DIR=%~dp0"
set "RUNTIME=%SCRIPT_DIR%simple.exe"
set "ENTRY=%SCRIPT_DIR%..\src\app\simple_lsp_mcp\main.spl"

if not exist "%RUNTIME%" set "RUNTIME=%SCRIPT_DIR%simple"

set "SIMPLE_LIB=%SCRIPT_DIR%..\src"
set "SIMPLE_BINARY=%RUNTIME%"
set "SIMPLE_LOG=error"
set "RUST_LOG=error"

"%RUNTIME%" "%ENTRY%" %*
