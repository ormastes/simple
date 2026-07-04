@echo off
setlocal
set "EXE=%~dp0release\x86_64-pc-windows-msvc\t32_mcp_server.exe"
if exist "%EXE%" (
    "%EXE%" %*
    exit /b %ERRORLEVEL%
)
call "%~dp0release\x86_64-pc-windows-msvc\t32_mcp_server.cmd" %*
