@echo off
setlocal
rem The native simple_mcp_server.exe core-dumps on every tools/call (full-program
rem codegen bug; only the initialize/tools/list handshake survives). Default to
rem source mode, which is a FULL fallback. Opt back into native with
rem SIMPLE_MCP_PREFER_NATIVE=1 once a real tools/call probe passes.
rem See doc/08_tracking/bug/mcp_full_program_native_codegen_and_arg_extract_2026-06-16.md
if not "%SIMPLE_MCP_PREFER_NATIVE%"=="1" goto :source

set "EXE=%~dp0release\x86_64-pc-windows-msvc\simple_mcp_server.exe"
if exist "%EXE%" (
    "%EXE%" %*
    exit /b %ERRORLEVEL%
)
call "%~dp0release\x86_64-pc-windows-msvc\simple_mcp_server.cmd" %*
exit /b %ERRORLEVEL%

:source
if "%SIMPLE_LIB%"=="" set "SIMPLE_LIB=%~dp0..\src"
if "%SIMPLE_LOG%"=="" set "SIMPLE_LOG=error"
if "%RUST_LOG%"=="" set "RUST_LOG=error"
call "%~dp0simple.cmd" run "%~dp0..\src\app\mcp\main.spl" %*
exit /b %ERRORLEVEL%
