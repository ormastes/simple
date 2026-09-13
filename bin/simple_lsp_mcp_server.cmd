@echo off
setlocal EnableExtensions DisableDelayedExpansion
set "EXE="
for /f "delims=" %%P in ('call "%~dp0stage4_local_resolve.cmd" lsp-mcp') do set "EXE=%%P"
if not defined EXE exit /b 127
"%EXE%" %*
exit /b %ERRORLEVEL%
