@echo off
REM Link binaries from bin/rust/ to bin/simple/ for Windows

setlocal enabledelayedexpansion

set "SCRIPT_DIR=%~dp0"
set "PROJECT_ROOT=%SCRIPT_DIR%.."
set "BIN_RUST=%PROJECT_ROOT%\bin\rust"
set "BIN_SIMPLE=%PROJECT_ROOT%\bin\simple"

echo Creating binary symlinks...

REM Create bin/simple directory if it doesn't exist
if not exist "%BIN_SIMPLE%" mkdir "%BIN_SIMPLE%"

REM Define binaries to link
set BINARIES=simple.exe simple-fmt.exe simple-lint.exe simple-test.exe smh_coverage.exe

REM Create symlinks
for %%b in (%BINARIES%) do (
    if exist "%BIN_RUST%\%%b" (
        echo   Linking %%b...
        mklink "%BIN_SIMPLE%\%%b" "%BIN_RUST%\%%b"
    ) else (
        echo   Warning: %BIN_RUST%\%%b not found, skipping
    )
)

echo.
echo Binary links created in %BIN_SIMPLE%
echo.
echo Add to your PATH:
echo   set PATH=%BIN_SIMPLE%;%%PATH%%

endlocal
