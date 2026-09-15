@echo off
setlocal
rem TRACE32 MCP server launcher (Windows). Self-contained: until 2026-09-13
rem the source path hopped through bin\release\<triple>\t32_mcp_server.cmd,
rem which is gitignored (bin/release/), so any fresh checkout or worktree
rem exited with "The system cannot find the path specified" before replying
rem and MCP clients reported CONNECTION_CLOSED.
set "REL=%~dp0release\x86_64-pc-windows-msvc"
set "EXE=%REL%\t32_mcp_server.exe"
if exist "%EXE%" (
    "%EXE%" %*
    exit /b %ERRORLEVEL%
)
set "SEED=%~dp0..\src\compiler_rust\target"
set "SIMPLE_RUNTIME=%SIMPLE_BINARY%"
if not exist "%SIMPLE_RUNTIME%" set "SIMPLE_RUNTIME=%REL%\simple.exe"
if not exist "%SIMPLE_RUNTIME%" set "SIMPLE_RUNTIME=%SEED%\release\simple.exe"
if not exist "%SIMPLE_RUNTIME%" set "SIMPLE_RUNTIME=%SEED%\bootstrap\simple.exe"
if not exist "%SIMPLE_RUNTIME%" (
    echo error: no t32_mcp_server.exe and no Simple runtime found. Tried: 1>&2
    echo   %%SIMPLE_BINARY%%=%SIMPLE_BINARY% 1>&2
    echo   %REL%\simple.exe 1>&2
    echo   %SEED%\release\simple.exe 1>&2
    echo   %SEED%\bootstrap\simple.exe 1>&2
    exit /b 127
)
set "TOOLS=%~dp0..\examples\10_tooling\trace32_tools"
set "SIMPLE_LIB=%TOOLS%"
if "%SIMPLE_LOG%"=="" set "SIMPLE_LOG=error"
if "%RUST_LOG%"=="" set "RUST_LOG=error"
rem The seed wall-clock-kills any entry under examples\ after 10s
rem (driver/src/cli/examples_safety.rs); a long-lived stdio server must opt out.
set "SIMPLE_TIMEOUT_SECONDS=0"
pushd "%~dp0.."
"%SIMPLE_RUNTIME%" "%TOOLS%\t32_mcp\main.spl" %*
set "RC=%ERRORLEVEL%"
popd
exit /b %RC%
