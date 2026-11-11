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
    goto :done
)
call "%~dp0release\x86_64-pc-windows-msvc\simple_lsp_mcp_server.cmd" %*
goto :done

:source
if "%SIMPLE_LIB%"=="" set "SIMPLE_LIB=%~dp0..\src"
if "%SIMPLE_LOG%"=="" set "SIMPLE_LOG=error"
if "%RUST_LOG%"=="" set "RUST_LOG=error"
if "%SIMPLE_EXECUTION_MODE%"=="" set "SIMPLE_EXECUTION_MODE=interpreter"
call "%~dp0simple.cmd" run "%~dp0..\src\app\simple_lsp_mcp\main.spl" %*
set "LSP_MCP_RC=%ERRORLEVEL%"
rem Answer the client with one JSON-RPC error frame instead of a silent close.
if not "%LSP_MCP_RC%"=="0" echo {"jsonrpc":"2.0","id":null,"error":{"code":-32000,"message":"simple_lsp_mcp_server runtime exited %LSP_MCP_RC%; see stderr"}}
if not "%LSP_MCP_RC%"=="0" 1>&2 echo simple_lsp_mcp_server: exited %LSP_MCP_RC%
exit /b %LSP_MCP_RC%

:done
exit /b %ERRORLEVEL%
