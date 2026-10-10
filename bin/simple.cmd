@echo off
setlocal

set "SCRIPT_DIR=%~dp0"
for %%I in ("%SCRIPT_DIR%..") do set "REPO_ROOT=%%~fI"

rem An explicit SIMPLE_BINARY always wins: the operator named the compiler to use,
rem and no locally discovered binary (which may be older than the source tree,
rem BUG-IT-1 2026-10-10) may shadow it.
rem Never when it names this wrapper itself: that would recurse until cmd dies.
set "SELF_REFERENCE="
if defined SIMPLE_BINARY for %%S in ("%SIMPLE_BINARY%") do if /I "%%~fS"=="%~f0" set "SELF_REFERENCE=1"
if defined SELF_REFERENCE (
    echo error: SIMPLE_BINARY points at this wrapper ^(%~f0^); set it to a simple.exe 1>&2
    exit /b 1
)
if defined SIMPLE_BINARY if exist "%SIMPLE_BINARY%" (
    "%SIMPLE_BINARY%" %*
    goto :done
)

set "BOOTSTRAP_BIN="
if exist "%REPO_ROOT%\src\compiler_rust\target\bootstrap\simple.exe" (
    for %%P in ("%REPO_ROOT%\src\compiler_rust\target\bootstrap\simple.exe") do if %%~zP GTR 0 (
        set "BOOTSTRAP_BIN=%%~fP"
    )
)

set "CURRENT_DRIVER_BIN="
if exist "%REPO_ROOT%\src\compiler_rust\target\debug\simple.exe" (
    for %%P in ("%REPO_ROOT%\src\compiler_rust\target\debug\simple.exe") do if %%~zP GTR 0 (
        set "CURRENT_DRIVER_BIN=%%~fP"
    )
)

set "RELEASE_BIN="
for %%P in (
    "%REPO_ROOT%\bin\release\x86_64-pc-windows-msvc\simple.exe"
    "%REPO_ROOT%\bin\release\x86_64-pc-windows-gnu\simple.exe"
    "%REPO_ROOT%\bin\release\aarch64-pc-windows-msvc\simple.exe"
    "%REPO_ROOT%\bin\release\aarch64-pc-windows-gnu\simple.exe"
    "%REPO_ROOT%\bin\release\simple.exe"
) do (
    if not defined RELEASE_BIN if exist %%~fP if %%~zP GTR 0 (
        set "RELEASE_BIN=%%~fP"
    )
)

if /I "%~1"=="lint" if defined BOOTSTRAP_BIN (
    "%BOOTSTRAP_BIN%" %*
    goto :done
)

if /I "%~x1"==".spl" if defined CURRENT_DRIVER_BIN (
    "%CURRENT_DRIVER_BIN%" %*
    goto :done
)

if defined RELEASE_BIN (
    "%RELEASE_BIN%" %*
    goto :done
)

if defined BOOTSTRAP_BIN (
    "%BOOTSTRAP_BIN%" %*
    goto :done
)

echo error: no Simple runtime found under %REPO_ROOT% 1>&2
echo   set SIMPLE_BINARY to a seed built from this tree, or deploy one: 1>&2
echo   sh scripts/bootstrap/bootstrap-windows.sh --msvc ^&^& sh scripts/setup/setup.shs 1>&2
echo   check a deployed binary with: sh scripts/check/check-deployed-simple-runnable.shs 1>&2
exit /b 1

:done
exit /b %ERRORLEVEL%
