@echo off
REM Windows twin of the rust_worker rustc fixture: only --version is valid.
if not "%~1"=="--version" exit /b 64
echo rustc 1.90.0 (fixture)
