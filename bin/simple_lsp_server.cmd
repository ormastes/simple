@echo off
setlocal

set "SCRIPT_DIR=%~dp0"
set "REPO_ROOT=%SCRIPT_DIR%.."
set "ENTRY=%REPO_ROOT%\src\app\lsp\main.spl"

set "RUNTIME=%REPO_ROOT%\src\compiler_rust\target\release\simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%REPO_ROOT%\src\compiler_rust\target\bootstrap\simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%SCRIPT_DIR%simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%SCRIPT_DIR%simple"

if not exist "%RUNTIME%" (
    echo error: no runtime found for simple_lsp_server >&2
    exit /b 1
)

set "SIMPLE_LIB=%REPO_ROOT%\src"
set "SIMPLE_LOG=error"
set "RUST_LOG=error"

"%RUNTIME%" "%ENTRY%" %* 2>nul
