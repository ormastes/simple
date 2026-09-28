@echo off
setlocal EnableExtensions
python "%~dp0riscv64-unknown-elf-tool-wrapper.py" gxx %*
exit /b %ERRORLEVEL%
