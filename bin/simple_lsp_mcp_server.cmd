@echo off
setlocal
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
set "EXE=%~dp0release\x86_64-pc-windows-msvc\simple_lsp_mcp_server.exe"
if exist "%EXE%" (
    "%EXE%" %*
    exit /b %ERRORLEVEL%
)
call "%~dp0release\x86_64-pc-windows-msvc\simple_lsp_mcp_server.cmd" %*
