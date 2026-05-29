@echo off
setlocal

set "SCRIPT_DIR=%~dp0"
for %%I in ("%SCRIPT_DIR%..") do set "REPO_ROOT=%%~fI"

set "BOOTSTRAP_BIN="
if exist "%REPO_ROOT%\src\compiler_rust\target\bootstrap\simple.exe" (
    set "BOOTSTRAP_BIN=%REPO_ROOT%\src\compiler_rust\target\bootstrap\simple.exe"
)

set "RELEASE_BIN="
for %%P in (
    "%REPO_ROOT%\bin\release\x86_64-pc-windows-msvc\simple.exe"
    "%REPO_ROOT%\bin\release\x86_64-pc-windows-gnu\simple.exe"
    "%REPO_ROOT%\bin\release\aarch64-pc-windows-msvc\simple.exe"
    "%REPO_ROOT%\bin\release\aarch64-pc-windows-gnu\simple.exe"
    "%REPO_ROOT%\bin\release\simple.exe"
) do (
    if not defined RELEASE_BIN if exist %%~fP (
        set "RELEASE_BIN=%%~fP"
    )
)

if /I "%~1"=="lint" if defined BOOTSTRAP_BIN (
    "%BOOTSTRAP_BIN%" %*
    exit /b %ERRORLEVEL%
)

if defined RELEASE_BIN (
    "%RELEASE_BIN%" %*
    exit /b %ERRORLEVEL%
)

if defined BOOTSTRAP_BIN (
    "%BOOTSTRAP_BIN%" %*
    exit /b %ERRORLEVEL%
)

echo error: no Simple runtime found 1>&2
exit /b 1
