@echo off
setlocal EnableExtensions DisableDelayedExpansion
if "%~2" NEQ "" goto :usage
if /I "%~1"=="cli" goto :resolve
if /I "%~1"=="mcp" goto :resolve
if /I "%~1"=="lsp-mcp" goto :resolve
goto :usage

:resolve
for %%I in ("%~dp0..") do set "REPO_ROOT=%%~fI"
set "RESOLVED="
for /f "delims=" %%P in ('set SIMPLE_STAGE4_RESOLVE_NATIVE_WINDOWS=1^&^& sh "%REPO_ROOT%\scripts\bootstrap\promote-stage4-local.shs" --resolve "%~1"') do set "RESOLVED=%%P"
if not defined RESOLVED exit /b 127
echo %RESOLVED%
exit /b 0

:usage
echo Usage: stage4_local_resolve.cmd cli^|mcp^|lsp-mcp 1>&2
exit /b 64
