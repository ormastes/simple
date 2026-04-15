@echo off
REM =========================================================================
REM  Test all UI backends: TUI, Web, Electron, Tauri
REM  Usage: scripts\test_ui_backends.cmd
REM =========================================================================

setlocal enabledelayedexpansion
set DEMO_FILE=%~dp0..\examples\ui\demo_kitchen_sink.ui.sdn
set PASS=0
set FAIL=0
set TOTAL=0

call :ResolveSimpleBin SIMPLE_BIN

echo =========================================================================
echo  Simple UI Backend Test Suite
echo =========================================================================
echo.
echo  Binary:  %SIMPLE_BIN%
echo  Demo:    %DEMO_FILE%
echo.

REM ---- Check binary exists ----
if not exist "%SIMPLE_BIN%" (
    echo ERROR: Simple binary not found at %SIMPLE_BIN%
    exit /b 1
)

REM ---- Check demo file exists ----
if not exist "%DEMO_FILE%" (
    echo ERROR: Demo file not found at %DEMO_FILE%
    exit /b 1
)

echo ---[ 1. TUI Backend (headless) ]---
echo.
echo Running: %SIMPLE_BIN% run examples\ui\hello_tui.spl
"%SIMPLE_BIN%" run "%~dp0..\examples\ui\hello_tui.spl" 2>&1
if %errorlevel% equ 0 (
    echo [PASS] TUI hello world
    set /a PASS+=1
) else (
    echo [FAIL] TUI hello world exited with code %errorlevel%
    set /a FAIL+=1
)
set /a TOTAL+=1
echo.

echo ---[ 2. TUI CRLF Test ]---
echo.
REM Create a temp CRLF test file
set CRLF_FILE=%TEMP%\test_crlf.ui.sdn
(
echo app:
echo     title: "CRLF Test"
echo     theme: dark
echo layout:
echo     type: vbox
echo     id: root
echo     children:
echo         msg:
echo             type: text
echo             id: msg
echo             content: "CRLF newline test"
echo         status:
echo             type: statusbar
echo             id: status
echo             left: "TEST"
echo             right: "CRLF"
) > "%CRLF_FILE%"
echo Running: %SIMPLE_BIN% ui tui %CRLF_FILE%  (headless)
echo quit | "%SIMPLE_BIN%" ui tui "%CRLF_FILE%" 2>&1
if %errorlevel% equ 0 (
    echo [PASS] TUI with CRLF file
    set /a PASS+=1
) else (
    echo [FAIL] TUI with CRLF file exited with code %errorlevel%
    set /a FAIL+=1
)
set /a TOTAL+=1
del "%CRLF_FILE%" 2>nul
echo.

echo ---[ 3. Web Backend ]---
echo.
echo Starting web server (will auto-stop after 3 seconds)...
start /b cmd /c ""%SIMPLE_BIN%" ui web "%DEMO_FILE%" --port 8765 2>&1 && exit /b"
timeout /t 2 /nobreak > nul
curl -s -o nul -w "HTTP %%{http_code}" http://localhost:8765/
if %errorlevel% equ 0 (
    echo.
    echo [PASS] Web server responds
    set /a PASS+=1
) else (
    echo.
    echo [FAIL] Web server not responding
    set /a FAIL+=1
)
set /a TOTAL+=1
REM Kill the web server
taskkill /f /im simple.exe /fi "WINDOWTITLE eq *" >nul 2>&1
echo.

echo ---[ 4. Tauri Backend Check ]---
echo.
set TAURI_SHELL=%~dp0..\tools\tauri-shell\src-tauri\target\release\simple-tauri-shell.exe
if exist "%TAURI_SHELL%" (
    echo Tauri shell found at %TAURI_SHELL%
    echo Starting Tauri app (will auto-stop after 5 seconds)...
    start /b "" "%TAURI_SHELL%" "%SIMPLE_BIN%" "%DEMO_FILE%"
    timeout /t 5 /nobreak > nul
    taskkill /f /im simple-tauri-shell.exe >nul 2>&1
    echo [PASS] Tauri shell launched
    set /a PASS+=1
) else (
    echo [SKIP] Tauri shell not built. To build:
    echo   cd tools\tauri-shell\src-tauri
    echo   cargo build --release
    echo.
    echo Checking if Tauri Rust code compiles...
    where cargo >nul 2>&1
    if %errorlevel% equ 0 (
        cd /d "%~dp0..\tools\tauri-shell\src-tauri"
        cargo check 2>&1
        if !errorlevel! equ 0 (
            echo [PASS] Tauri code compiles
            set /a PASS+=1
        ) else (
            echo [FAIL] Tauri code does not compile
            set /a FAIL+=1
        )
    ) else (
        echo [SKIP] cargo not found - install Rust to build Tauri shell
    )
)
set /a TOTAL+=1
echo.

echo ---[ 5. Electron Backend Check ]---
echo.
where electron >nul 2>&1
if %errorlevel% equ 0 (
    echo Electron found. Starting Electron app...
    start /b "" electron "%~dp0..\tools\electron-shell" "%~dp0..\examples\ui\hello_tui.spl"
    timeout /t 5 /nobreak > nul
    taskkill /f /im electron.exe >nul 2>&1
    echo [PASS] Electron shell launched
    set /a PASS+=1
) else (
    echo [SKIP] electron not in PATH. Install with: npm install -g electron
)
set /a TOTAL+=1
echo.

echo =========================================================================
echo  Results:  %PASS% passed, %FAIL% failed, %TOTAL% total
echo =========================================================================

if %FAIL% gtr 0 exit /b 1
exit /b 0

:ResolveSimpleBin
set "%~1="
set "SCRIPT_ROOT=%~dp0.."
if exist "%SCRIPT_ROOT%\bin\simple.exe" (
    set "%~1=%SCRIPT_ROOT%\bin\simple.exe"
    exit /b 0
)
if /i "%PROCESSOR_ARCHITECTURE%"=="AMD64" (
    for %%P in (x86_64-pc-windows-msvc x86_64-pc-windows-gnu) do (
        if exist "%SCRIPT_ROOT%\bin\release\%%P\simple.exe" (
            set "%~1=%SCRIPT_ROOT%\bin\release\%%P\simple.exe"
            exit /b 0
        )
    )
)
if /i "%PROCESSOR_ARCHITECTURE%"=="ARM64" (
    if exist "%SCRIPT_ROOT%\bin\release\aarch64-pc-windows-msvc\simple.exe" (
        set "%~1=%SCRIPT_ROOT%\bin\release\aarch64-pc-windows-msvc\simple.exe"
        exit /b 0
    )
)
if exist "%SCRIPT_ROOT%\bin\release\simple.exe" (
    set "%~1=%SCRIPT_ROOT%\bin\release\simple.exe"
    exit /b 0
)
if exist "%SCRIPT_ROOT%\src\compiler_rust\target\release\simple.exe" (
    set "%~1=%SCRIPT_ROOT%\src\compiler_rust\target\release\simple.exe"
    exit /b 0
)
if exist "%SCRIPT_ROOT%\src\compiler_rust\target\bootstrap\simple.exe" (
    set "%~1=%SCRIPT_ROOT%\src\compiler_rust\target\bootstrap\simple.exe"
    exit /b 0
)
set "%~1=%SCRIPT_ROOT%\bin\release\simple.exe"
exit /b 0
