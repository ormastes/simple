@echo off
setlocal
rem Native Windows server first (explicit override, then deployed artifact).
set "EXE=%~dp0release\x86_64-pc-windows-msvc\simple_mcp_server.exe"
if not "%SIMPLE_MCP_NATIVE%"=="" set "EXE=%SIMPLE_MCP_NATIVE%"
if exist "%EXE%" (
    "%EXE%" %*
    exit /b %ERRORLEVEL%
)
if not "%SIMPLE_MCP_NATIVE%"=="" (
    echo error: SIMPLE_MCP_NATIVE not found: %SIMPLE_MCP_NATIVE% 1>&2
    exit /b 127
)
rem No native Windows simple_mcp_server exists (the msvc exe is .disabled), so
rem interpreted source mode IS the deployed path on Windows. Do NOT route
rem through bin\release\...\simple_mcp_server.cmd: that gitignored inner
rem wrapper prefers a stale runtime and hides stderr with 2>nul, which
rem produced rc=0 with zero protocol output (silent green, 2026-09-01).
if "%SIMPLE_LIB%"=="" set "SIMPLE_LIB=%~dp0..\src"
if "%SIMPLE_LOG%"=="" set "SIMPLE_LOG=error"
if "%RUST_LOG%"=="" set "RUST_LOG=error"
set "RUNTIME="
if not "%SIMPLE_BINARY%"=="" if exist "%SIMPLE_BINARY%" set "RUNTIME=%SIMPLE_BINARY%"
if not defined RUNTIME if exist "%~dp0simple.exe" set "RUNTIME=%~dp0simple.exe"
if not defined RUNTIME if exist "%~dp0..\src\compiler_rust\target\release\simple.exe" set "RUNTIME=%~dp0..\src\compiler_rust\target\release\simple.exe"
if not defined RUNTIME if exist "%~dp0..\src\compiler_rust\target\bootstrap\simple.exe" set "RUNTIME=%~dp0..\src\compiler_rust\target\bootstrap\simple.exe"
if not defined RUNTIME (
    echo error: no Simple runtime found for simple_mcp_server source mode 1>&2
    exit /b 127
)
set "LOG_DIR=%~dp0..\.simple\logs"
if not exist "%LOG_DIR%" mkdir "%LOG_DIR%" >nul 2>&1
rem stderr goes to a log, never nul: MCP uses stdout only, and a swallowed
rem startup error is exactly the silent-green failure mode this repo produces.
"%RUNTIME%" run "%~dp0..\src\app\mcp\main.spl" %* 2>>"%LOG_DIR%\simple_mcp_stderr.log"
exit /b %ERRORLEVEL%
