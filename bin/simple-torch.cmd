@echo off
setlocal

set "SCRIPT_DIR=%~dp0"
set "REPO_ROOT=%SCRIPT_DIR%.."

rem Path to FFI library (DLL on Windows)
set "FFI_LIB_PATH=%REPO_ROOT%\.build\rust\ffi_torch\target\release"

if not exist "%FFI_LIB_PATH%\simple_torch_ffi.dll" (
    echo ERROR: PyTorch FFI library not found at: %FFI_LIB_PATH%\simple_torch_ffi.dll
    echo Please build the FFI library first:
    echo   cd %REPO_ROOT%\.build\rust\ffi_torch
    echo   cargo build --release
    exit /b 1
)

rem Add FFI library path to PATH so Windows can find the DLL
set "PATH=%FFI_LIB_PATH%;%PATH%"

rem Execute the Simple runtime with all arguments
call "%SCRIPT_DIR%simple.cmd" %*
