@echo off
setlocal

set "SCRIPT_DIR=%~dp0"
set "REPO_ROOT=%SCRIPT_DIR%.."
set "RUNTIME=%SCRIPT_DIR%simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%SCRIPT_DIR%simple"

if not exist "%RUNTIME%" (
    echo error: no runtime found for obsidian_lsp_mcp_server >&2
    exit /b 1
)

set "SIMPLE_LIB=%REPO_ROOT%\examples\obsidian-search\src;%REPO_ROOT%\src"
set "SIMPLE_BINARY=%RUNTIME%"
if not defined SIMPLE_LOG set "SIMPLE_LOG=error"
set "RUST_LOG=error"

rem Mode: bridge (default) or mcp
set "MODE=bridge"
if "%~1"=="bridge" (
    set "MODE=bridge"
    shift
) else if "%~1"=="mcp" (
    set "MODE=mcp"
    shift
)

if "%MODE%"=="mcp" (
    set "ENTRY=%REPO_ROOT%\examples\obsidian-search\src\main.spl"
) else (
    set "ENTRY=%REPO_ROOT%\examples\obsidian-search\src\main_bridge.spl"
)

pushd "%REPO_ROOT%"
"%RUNTIME%" "%ENTRY%" %* 2>nul
