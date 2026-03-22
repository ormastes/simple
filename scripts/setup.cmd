@echo off
REM Simple Language — Windows setup (CMD/PowerShell)
REM
REM Creates dual links:
REM   bin\simple.exe → bin\release\<arch>-pc-windows-msvc\simple.exe  (MSVC, for CMD)
REM   bin\simple     → bin\release\<arch>-pc-windows-gnu\simple.exe   (MinGW, for bash)
REM
REM Usage:
REM   scripts\setup.cmd [--dry-run]

setlocal enabledelayedexpansion

set "REPO_ROOT=%~dp0.."
set "DRY_RUN=0"

:parse_args
if "%~1"=="" goto detect
if "%~1"=="--dry-run" set "DRY_RUN=1" & shift & goto parse_args
if "%~1"=="--help" goto usage
if "%~1"=="-h" goto usage
echo error: unknown option '%~1' >&2
goto usage

:detect
REM Architecture
set "ARCH=x86_64"
if "%PROCESSOR_ARCHITECTURE%"=="AMD64" set "ARCH=x86_64"
if "%PROCESSOR_ARCHITECTURE%"=="ARM64" set "ARCH=aarch64"
if "%PROCESSOR_ARCHITECTURE%"=="x86"   set "ARCH=i686"

set "MSVC_TRIPLE=%ARCH%-pc-windows-msvc"
set "MINGW_TRIPLE=%ARCH%-pc-windows-gnu"
set "RELEASE_DIR=%REPO_ROOT%\bin\release"

echo Architecture: %ARCH%

REM Locate MSVC binary
set "MSVC_BIN="
if exist "%RELEASE_DIR%\%MSVC_TRIPLE%\simple.exe" (
    set "MSVC_BIN=%MSVC_TRIPLE%\simple.exe"
) else if exist "%RELEASE_DIR%\simple.exe" (
    set "MSVC_BIN=simple.exe"
)

REM Locate MinGW binary
set "MINGW_BIN="
if exist "%RELEASE_DIR%\%MINGW_TRIPLE%\simple.exe" (
    set "MINGW_BIN=%MINGW_TRIPLE%\simple.exe"
)

if not defined MSVC_BIN if not defined MINGW_BIN (
    echo error: no release binary found for Windows >&2
    echo. >&2
    echo Searched: >&2
    echo   %RELEASE_DIR%\%MSVC_TRIPLE%\simple.exe >&2
    echo   %RELEASE_DIR%\%MINGW_TRIPLE%\simple.exe >&2
    echo   %RELEASE_DIR%\simple.exe >&2
    echo. >&2
    echo Run the bootstrap first: >&2
    echo   scripts\bootstrap\bootstrap-windows.sh --msvc --deploy >&2
    echo   scripts\bootstrap\bootstrap-windows.sh --mingw --deploy >&2
    exit /b 1
)

if defined MSVC_BIN  echo MSVC binary:  bin\release\%MSVC_BIN%
if defined MINGW_BIN echo MinGW binary: bin\release\%MINGW_BIN%

if "%DRY_RUN%"=="1" (
    echo.
    echo [dry-run] would create:
    if defined MSVC_BIN  echo   bin\simple.exe -^> release\%MSVC_BIN%
    if defined MINGW_BIN echo   bin\simple     -^> release\%MINGW_BIN%
    exit /b 0
)

echo.

REM === Create bin\simple.exe → MSVC binary ===
if defined MSVC_BIN (
    if exist "%REPO_ROOT%\bin\simple.exe" del "%REPO_ROOT%\bin\simple.exe"
    REM Try symlink, then hardlink, then copy
    mklink "%REPO_ROOT%\bin\simple.exe" "release\%MSVC_BIN%" >nul 2>&1
    if !errorlevel! neq 0 (
        mklink /H "%REPO_ROOT%\bin\simple.exe" "%RELEASE_DIR%\%MSVC_BIN%" >nul 2>&1
        if !errorlevel! neq 0 (
            copy "%RELEASE_DIR%\%MSVC_BIN%" "%REPO_ROOT%\bin\simple.exe" >nul
            echo Created: bin\simple.exe [copy] -^> release\%MSVC_BIN%
        ) else (
            echo Created: bin\simple.exe [hardlink] -^> release\%MSVC_BIN%
        )
    ) else (
        echo Created: bin\simple.exe -^> release\%MSVC_BIN%
    )
)

REM === Create bin\simple → MinGW binary (for Git Bash / MSYS2) ===
if defined MINGW_BIN (
    if exist "%REPO_ROOT%\bin\simple" del "%REPO_ROOT%\bin\simple"
    mklink "%REPO_ROOT%\bin\simple" "release\%MINGW_BIN%" >nul 2>&1
    if !errorlevel! neq 0 (
        mklink /H "%REPO_ROOT%\bin\simple" "%RELEASE_DIR%\%MINGW_BIN%" >nul 2>&1
        if !errorlevel! neq 0 (
            copy "%RELEASE_DIR%\%MINGW_BIN%" "%REPO_ROOT%\bin\simple" >nul
            echo Created: bin\simple [copy] -^> release\%MINGW_BIN%
        ) else (
            echo Created: bin\simple [hardlink] -^> release\%MINGW_BIN%
        )
    ) else (
        echo Created: bin\simple -^> release\%MINGW_BIN%
    )
)

:verify
echo.
echo Verify:
if defined MSVC_BIN  echo   bin\simple.exe --version   (MSVC, for CMD/PowerShell)
if defined MINGW_BIN echo   bin\simple --version        (MinGW, for Git Bash)
echo.
echo Setup complete.
exit /b 0

:usage
echo Usage: scripts\setup.cmd [--dry-run]
echo.
echo Creates dual links for Windows:
echo   bin\simple.exe  -^> MSVC binary   (for CMD / PowerShell)
echo   bin\simple      -^> MinGW binary  (for Git Bash / MSYS2)
echo.
echo Options:
echo   --dry-run   Show what would be done
exit /b 0
