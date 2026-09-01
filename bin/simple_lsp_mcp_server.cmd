@echo off
setlocal
if not [%2]==[] goto :after_fast_options
if "%~1"=="--version" (
    echo simple-lsp-mcp-server 0.9.8
    exit /b 0
)
if "%~1"=="-v" (
    echo simple-lsp-mcp-server 0.9.8
    exit /b 0
)
if "%~1"=="--help" (
    echo simple-lsp-mcp-server 0.9.8
    echo Usage: simple_lsp_mcp_server
    echo        simple_lsp_mcp_server --version
    exit /b 0
)
if "%~1"=="-h" (
    echo simple-lsp-mcp-server 0.9.8
    echo Usage: simple_lsp_mcp_server
    echo        simple_lsp_mcp_server --version
    exit /b 0
)
:after_fast_options
rem The native simple_lsp_mcp_server.exe fails every tools/call ("Missing tool
rem name", AOT arg-extraction codegen bug). Default to source mode: 10/11 LSP
rem tools work; lsp_diagnostics is gated off and returns a message. Opt into
rem native with SIMPLE_LSP_MCP_PREFER_NATIVE=1 once a real tools/call probe passes.
if not "%SIMPLE_LSP_MCP_PREFER_NATIVE%"=="1" goto :source

set "EXE=%~dp0release\x86_64-pc-windows-msvc\simple_lsp_mcp_server.exe"
if exist "%EXE%" (
    "%EXE%" %*
    exit /b %ERRORLEVEL%
)
call "%~dp0release\x86_64-pc-windows-msvc\simple_lsp_mcp_server.cmd" %*
exit /b %ERRORLEVEL%

:source
if "%SIMPLE_LIB%"=="" set "SIMPLE_LIB=%~dp0..\src"
if "%SIMPLE_LOG%"=="" set "SIMPLE_LOG=error"
if "%RUST_LOG%"=="" set "RUST_LOG=error"
rem Load-bearing: inherited by the query_visibility child; dropping it
rem regressed lsp_symbols from 3.68s to 7.96s (see .mcp.json _info).
if "%SIMPLE_EXECUTION_MODE%"=="" set "SIMPLE_EXECUTION_MODE=interpreter"
rem Pick the runtime directly. Do NOT go through bin\simple.cmd: its
rem release-candidate order prefers bin\release\x86_64-pc-windows-msvc\simple.exe,
rem which (Apr 23 build) exits 127 silently on any `run` (measured 2026-09-01).
set "RUNTIME="
if not "%SIMPLE_BINARY%"=="" if exist "%SIMPLE_BINARY%" set "RUNTIME=%SIMPLE_BINARY%"
if not defined RUNTIME if exist "%~dp0simple.exe" set "RUNTIME=%~dp0simple.exe"
if not defined RUNTIME if exist "%~dp0..\src\compiler_rust\target\release\simple.exe" set "RUNTIME=%~dp0..\src\compiler_rust\target\release\simple.exe"
if not defined RUNTIME if exist "%~dp0..\src\compiler_rust\target\bootstrap\simple.exe" set "RUNTIME=%~dp0..\src\compiler_rust\target\bootstrap\simple.exe"
if not defined RUNTIME (
    echo error: no Simple runtime found for simple_lsp_mcp_server source mode 1>&2
    exit /b 127
)
set "SIMPLE_BINARY=%RUNTIME%"
set "LOG_DIR=%~dp0..\.simple\logs"
if not exist "%LOG_DIR%" mkdir "%LOG_DIR%" >nul 2>&1
"%RUNTIME%" run "%~dp0..\src\app\simple_lsp_mcp\main.spl" %* 2>>"%LOG_DIR%\simple_lsp_mcp_stderr.log"
exit /b %ERRORLEVEL%
