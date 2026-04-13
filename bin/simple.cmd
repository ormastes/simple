@echo off
setlocal

set "SCRIPT_DIR=%~dp0"

rem Detect Windows target triple
set "ARCH=x86_64"
if "%PROCESSOR_ARCHITECTURE%"=="ARM64" set "ARCH=aarch64"
set "TRIPLE=%ARCH%-pc-windows-msvc"

set "RUNTIME=%SCRIPT_DIR%release\%TRIPLE%\simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%SCRIPT_DIR%release\simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%SCRIPT_DIR%simple.exe"

if not exist "%RUNTIME%" (
    echo error: simple runtime not found. Run scripts\setup.cmd first. >&2
    exit /b 1
)

"%RUNTIME%" %*
