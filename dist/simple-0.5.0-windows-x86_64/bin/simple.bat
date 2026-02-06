@echo off
setlocal
set SCRIPT_DIR=%~dp0
"%SCRIPT_DIR%simple_runtime.exe" %*
endlocal
