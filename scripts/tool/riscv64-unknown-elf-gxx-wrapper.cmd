@echo off
setlocal EnableExtensions
"%~dp0..\..\bin\simple.exe" run "%~dp0riscv64-unknown-elf-tool-wrapper.spl" -- gxx %*
exit /b %ERRORLEVEL%
