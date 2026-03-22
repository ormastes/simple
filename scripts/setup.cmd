@echo off
REM Simple Language — Windows setup (CMD/PowerShell)
REM
REM Creates bin\simple.exe junction to bin\release\<triple>\simple.exe
REM
REM Usage:
REM   scripts\setup.cmd [--mingw] [--msvc] [--dry-run]

setlocal enabledelayedexpansion

set "REPO_ROOT=%~dp0.."
set "DRY_RUN=0"
set "FORCE_ABI="

:parse_args
if "%~1"=="" goto detect
if "%~1"=="--mingw" set "FORCE_ABI=gnu" & shift & goto parse_args
if "%~1"=="--msvc"  set "FORCE_ABI=msvc" & shift & goto parse_args
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

REM ABI detection
if defined FORCE_ABI (
    set "ABI=%FORCE_ABI%"
) else (
    set "ABI=msvc"
    if defined MSYSTEM (
        echo %MSYSTEM% | findstr /i "MINGW" >nul && set "ABI=gnu"
    )
    where gcc >nul 2>&1 && if not defined MSYSTEM set "ABI=gnu"
    where cl.exe >nul 2>&1 && set "ABI=msvc"
    where clang-cl >nul 2>&1 && set "ABI=msvc"
)

set "PLATFORM=%ARCH%-pc-windows-%ABI%"
echo Platform: %PLATFORM%

REM Locate release binary
set "RELEASE_DIR=%REPO_ROOT%\bin\release"
set "RELEASE_BIN="

if exist "%RELEASE_DIR%\%PLATFORM%\simple.exe" (
    set "RELEASE_BIN=%PLATFORM%\simple.exe"
) else if exist "%RELEASE_DIR%\windows-%ARCH%\simple.exe" (
    set "RELEASE_BIN=windows-%ARCH%\simple.exe"
) else if exist "%RELEASE_DIR%\simple.exe" (
    set "RELEASE_BIN=simple.exe"
) else (
    echo error: no release binary found for %PLATFORM% >&2
    echo. >&2
    echo Run the bootstrap first: >&2
    echo   scripts\bootstrap\bootstrap-windows.sh --deploy >&2
    exit /b 1
)

echo Release binary: bin\release\%RELEASE_BIN%

if "%DRY_RUN%"=="1" (
    echo.
    echo [dry-run] would create:
    echo   bin\simple.exe -^> release\%RELEASE_BIN%
    exit /b 0
)

REM Create copy (Windows symlinks need admin; use copy as fallback)
if exist "%REPO_ROOT%\bin\simple.exe" del "%REPO_ROOT%\bin\simple.exe"

REM Try symlink first (works in developer mode or elevated)
mklink "%REPO_ROOT%\bin\simple.exe" "release\%RELEASE_BIN%" >nul 2>&1
if %errorlevel% neq 0 (
    REM Fallback: hardlink
    mklink /H "%REPO_ROOT%\bin\simple.exe" "%RELEASE_DIR%\%RELEASE_BIN%" >nul 2>&1
    if %errorlevel% neq 0 (
        REM Fallback: copy
        copy "%RELEASE_DIR%\%RELEASE_BIN%" "%REPO_ROOT%\bin\simple.exe" >nul
        echo Created: bin\simple.exe (copy of release\%RELEASE_BIN%)
        goto verify
    )
    echo Created: bin\simple.exe (hardlink to release\%RELEASE_BIN%)
    goto verify
)
echo Created: bin\simple.exe -^> release\%RELEASE_BIN%

:verify
echo.
echo Verify:
echo   bin\simple.exe --version
echo.
echo Setup complete.
exit /b 0

:usage
echo Usage: scripts\setup.cmd [--msvc] [--mingw] [--dry-run]
echo.
echo Creates bin\simple.exe pointing to the correct release binary.
echo.
echo Options:
echo   --msvc      Force MSVC ABI detection
echo   --mingw     Force MinGW/GNU ABI detection
echo   --dry-run   Show what would be done
exit /b 0
