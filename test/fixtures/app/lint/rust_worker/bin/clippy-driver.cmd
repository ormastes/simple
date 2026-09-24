@echo off
REM Windows twin of the rust_worker clippy-driver fixture: only --version is valid.
if not "%~1"=="--version" exit /b 64
echo clippy 0.1.90 (fixture)
