@echo off
setlocal EnableExtensions EnableDelayedExpansion

set "TOOL=%SIMPLE_RISCV64_GXX%"
if "%TOOL%"=="" if exist "C:\dev\tool\msys2\mingw64\bin\riscv64-unknown-elf-g++.exe" set "TOOL=C:\dev\tool\msys2\mingw64\bin\riscv64-unknown-elf-g++.exe"
if "%TOOL%"=="" set "TOOL=riscv64-unknown-elf-g++.exe"

set "ARGS="
:arg_loop
if "%~1"=="" goto run_tool
if /I "%~1"=="--target=riscv64-unknown-elf" (
    shift
    goto arg_loop
)
if /I "%~1"=="--target" (
    shift
    if not "%~1"=="" shift
    goto arg_loop
)
set "ARGS=!ARGS! "%~1""
shift
goto arg_loop

:run_tool
"%TOOL%" %ARGS%
exit /b %ERRORLEVEL%
