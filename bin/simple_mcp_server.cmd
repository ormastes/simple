@echo off
setlocal
rem Simple MCP server launcher (Windows). Mirrors bin/simple_mcp_server:
rem   1. an admitted native exe, hash-checked against its .sha256 sidecar
rem   2. otherwise the pure-Simple source entry on the deployed runtime.
rem Every instance inherits stderr. Until 2026-09-12 the source path hopped
rem through bin\release\<triple>\simple_mcp_server.cmd, which redirected stderr
rem to ONE process-global %TEMP%\simple_mcp_server.err; the second client
rem (Codex + Claude Code) then died with "The process cannot access the file
rem because it is being used by another process" and never answered.
set "REL=%~dp0release\x86_64-pc-windows-msvc"
set "EXE=%REL%\simple_mcp_server.exe"
if not "%SIMPLE_MCP_NATIVE%"=="" set "EXE=%SIMPLE_MCP_NATIVE%"
if "%SIMPLE_LOG%"=="" set "SIMPLE_LOG=error"
if "%RUST_LOG%"=="" set "RUST_LOG=error"
rem Same default as the POSIX wrapper: advertise the full table on the first
rem tools/list instead of auto-mode's 19-tool core set + list_changed upgrade.
if "%SIMPLE_MCP_TOOL_SET%"=="" set "SIMPLE_MCP_TOOL_SET=all"
if not exist "%EXE%" goto :no_exe
if not exist "%EXE%.sha256" (
    echo error: %EXE% has no .sha256 sidecar; refusing an unadmitted native server 1>&2
    exit /b 2
)
set "EXPECTED="
set /p EXPECTED=<"%EXE%.sha256"
for /f "tokens=1" %%h in ("%EXPECTED%") do set "EXPECTED=%%h"
set "ACTUAL="
for /f "skip=1 tokens=1" %%h in ('certutil -hashfile "%EXE%" SHA256') do if not defined ACTUAL set "ACTUAL=%%h"
if /i not "%ACTUAL%"=="%EXPECTED%" (
    echo error: sha256 mismatch for %EXE% 1>&2
    echo   expected %EXPECTED% 1>&2
    echo   actual   %ACTUAL% 1>&2
    exit /b 2
)
"%EXE%" %*
exit /b %ERRORLEVEL%

:no_exe
if not "%SIMPLE_MCP_NATIVE%"=="" (
    echo error: SIMPLE_MCP_NATIVE not found: %SIMPLE_MCP_NATIVE% 1>&2
    exit /b 127
)
set "SIMPLE_RUNTIME=%REL%\simple.exe"
if not "%SIMPLE_BINARY%"=="" set "SIMPLE_RUNTIME=%SIMPLE_BINARY%"
if not exist "%SIMPLE_RUNTIME%" (
    echo error: no admitted simple_mcp_server.exe and no runtime at %SIMPLE_RUNTIME% 1>&2
    exit /b 127
)
if "%SIMPLE_LIB%"=="" set "SIMPLE_LIB=%~dp0..\src"
rem Same default as bin\simple_lsp_mcp_server.cmd. On the source path this is
rem CORRECTNESS, not tuning: under the Rust seed's default JIT the explicit
rem `Some(x)` optional constructor lowers to a corrupt value, so
rem storage_root_environment_snapshot()'s LOCALAPPDATA/HOME fields read back as
rem neither nil nor their text, _default_user() answers nil, and every CLI
rem passthrough tool returns "centralized child storage environment is
rem unavailable". Interpreter mode is also FASTER to first reply here
rem (measured 2026-09-13, initialize: 1.20s interpreter vs 3.27s JIT).
rem Seed defect: doc/08_tracking/bug/seed_jit_some_constructor_corrupts_value_2026-09-13.md
if "%SIMPLE_EXECUTION_MODE%"=="" set "SIMPLE_EXECUTION_MODE=interpreter"
echo simple_mcp_server: no admitted native exe; serving src\app\mcp\main.spl on %SIMPLE_RUNTIME% 1>&2
"%SIMPLE_RUNTIME%" run "%~dp0..\src\app\mcp\main.spl" %*
exit /b %ERRORLEVEL%
