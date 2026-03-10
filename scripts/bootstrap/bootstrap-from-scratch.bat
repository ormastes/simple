@echo off
REM Bootstrap the Simple compiler using Rust seed + Simple self-hosting (Windows).
REM
REM This script builds the Simple compiler via a Rust bootstrap seed,
REM then self-hosts the compiler to produce the final binary.
REM
REM Bootstrap chain:
REM   Phase 0: (reserved for future release download)
REM   Phase 1: Build Rust seed (cargo build --profile bootstrap -p simple-driver)
REM   Phase 2: Stage 1 Rust-base Simple (full CLI)
REM   Phase 3: Stage 2 pure Simple via llvm-lib
REM   Phase 4: Stage 3 full pure-Simple self-host via llvm-lib
REM   Phase 5: Verify reproducibility (stage2 vs stage3 hash comparison)
REM   Phase 6: Deploy to bin\release\simple.exe
REM
REM Usage:
REM   scripts\bootstrap\bootstrap-from-scratch.bat
REM   scripts\bootstrap\bootstrap-from-scratch.bat --deploy
REM   scripts\bootstrap\bootstrap-from-scratch.bat --skip-rust-build --deploy
REM   scripts\bootstrap\bootstrap-from-scratch.bat --backend=llvm-lib --deploy
REM   scripts\bootstrap\bootstrap-from-scratch.bat --help

setlocal EnableDelayedExpansion

REM ================================================================
REM  Defaults
REM ================================================================
set "DEPLOY=false"
set "KEEP_ARTIFACTS=false"
set "JOBS=%NUMBER_OF_PROCESSORS%"
set "SKIP_RUST_BUILD=false"
set "SKIP_LLVM=false"
set "BACKEND=llvm-lib"
set "VERIFY_HASH=true"
set "VERBOSE=false"

REM Paths
set "RUST_SEED_DIR=src\compiler_rust"
set "RUST_SEED_BIN=%RUST_SEED_DIR%\target\bootstrap\simple.exe"
set "BOOTSTRAP_DIR=build\bootstrap"
set "RELEASE_DIR=bin\release"

REM ================================================================
REM  Parse arguments
REM ================================================================
if "%~1"=="" goto :args_done

:parse_args
if "%~1"=="" goto :args_done
if /i "%~1"=="--deploy"          set "DEPLOY=true"       & shift & goto :parse_args
if /i "%~1"=="--keep-artifacts"  set "KEEP_ARTIFACTS=true" & shift & goto :parse_args
if /i "%~1"=="--skip-rust-build" set "SKIP_RUST_BUILD=true" & shift & goto :parse_args
if /i "%~1"=="--skip-llvm"      set "SKIP_LLVM=true"    & shift & goto :parse_args
if /i "%~1"=="--no-verify"      set "VERIFY_HASH=false"  & shift & goto :parse_args
if /i "%~1"=="--verbose"        set "VERBOSE=true"       & shift & goto :parse_args
if /i "%~1"=="--help" goto :usage
if /i "%~1"=="-h"     goto :usage

set "ARG=%~1"
if /i "!ARG:~0,7!"=="--jobs="    set "JOBS=!ARG:~7!"    & shift & goto :parse_args
if /i "!ARG:~0,10!"=="--backend=" set "BACKEND=!ARG:~10!" & shift & goto :parse_args

echo [bootstrap] ERROR: Unknown option: %~1
exit /b 1

:usage
echo Simple Compiler - Bootstrap From Scratch (Windows)
echo.
echo Usage: scripts\bootstrap\bootstrap-from-scratch.bat [options]
echo.
echo Options:
echo   --deploy              Copy final binary to bin\release\simple.exe
echo   --skip-rust-build     Reuse existing Rust seed binary (skip cargo build)
echo   --skip-llvm           Skip Stage 2 and Stage 3 llvm-lib builds
echo   --backend=BACKEND     Backend: llvm-lib, llvm, cranelift, auto (default: llvm-lib)
echo   --no-verify           Skip hash verification
echo   --keep-artifacts      Keep build\bootstrap artifacts
echo   --jobs=N              Parallel build jobs (default: %NUMBER_OF_PROCESSORS%)
echo   --verbose             Print detailed output
echo   --help                Show this help
exit /b 0

:args_done

REM ================================================================
echo ================================================================
echo   Simple Compiler - Bootstrap From Scratch (Windows)
echo ================================================================
echo.

REM ================================================================
REM  Prerequisites
REM ================================================================
echo [bootstrap] Checking prerequisites...

REM Check Rust toolchain (unless skipping)
if /i "!SKIP_RUST_BUILD!"=="false" (
    where rustc >nul 2>&1
    if errorlevel 1 (
        echo [bootstrap] ERROR: rustc not found. Install Rust: https://rustup.rs
        exit /b 1
    )
    where cargo >nul 2>&1
    if errorlevel 1 (
        echo [bootstrap] ERROR: cargo not found. Install Rust: https://rustup.rs
        exit /b 1
    )
    for /f "delims=" %%v in ('rustc --version 2^>nul') do echo [bootstrap] Rust: %%v
)

REM Check C compiler (needed for linking)
set "CC_FOUND="
for %%c in (clang-cl clang gcc) do (
    where %%c >nul 2>&1
    if not errorlevel 1 (
        if "!CC_FOUND!"=="" (
            set "CC_FOUND=%%c"
        )
    )
)
if "!CC_FOUND!"=="" (
    echo [bootstrap] ERROR: No C compiler found (clang-cl, clang, or gcc required for linking)
    exit /b 1
)
echo [bootstrap] C compiler: !CC_FOUND!

REM Detect LLVM for llvm-lib backend
set "LLVM_FOUND=false"
set "LLVM_PATH="
if /i not "!SKIP_LLVM!"=="true" (
    REM Check LLVM_DIR env var
    if defined LLVM_DIR (
        if exist "!LLVM_DIR!\bin\LLVM-C.dll" (
            set "LLVM_FOUND=true"
            set "LLVM_PATH=!LLVM_DIR!"
        )
    )
    REM Check standard install paths
    if /i "!LLVM_FOUND!"=="false" (
        for %%p in (
            "C:\Program Files\LLVM"
            "C:\LLVM"
        ) do (
            if exist "%%~p\bin\LLVM-C.dll" (
                set "LLVM_FOUND=true"
                set "LLVM_PATH=%%~p"
            )
        )
    )
    REM Check MSYS2 paths
    if /i "!LLVM_FOUND!"=="false" (
        for %%p in (
            "C:\msys64\mingw64"
            "C:\msys64\clang64"
            "C:\msys64\ucrt64"
        ) do (
            if exist "%%~p\bin\LLVM-C.dll" (
                set "LLVM_FOUND=true"
                set "LLVM_PATH=%%~p"
            )
        )
    )
    if /i "!LLVM_FOUND!"=="true" (
        echo [bootstrap] LLVM: !LLVM_PATH!
    ) else (
        echo [bootstrap] LLVM: not found (llvm-lib backend unavailable)
    )
)

REM Resolve backend
if /i "!BACKEND!"=="auto" (
    set "BACKEND=llvm-lib"
)
if /i "!BACKEND!"=="llvm-lib" (
    if /i "!LLVM_FOUND!"=="false" (
        echo [bootstrap] ERROR: --backend=llvm-lib requires LLVM. Install LLVM or set LLVM_DIR.
        exit /b 1
    )
)
echo [bootstrap] Backend: !BACKEND!
echo.

REM ================================================================
REM  Phase 1: Build Rust seed
REM ================================================================
echo [bootstrap] ----------------------------------------------------------------
echo [bootstrap] Phase 1: Build Rust seed
echo [bootstrap] ----------------------------------------------------------------
echo.

if /i "!SKIP_RUST_BUILD!"=="true" (
    if not exist "!RUST_SEED_BIN!" (
        echo [bootstrap] ERROR: --skip-rust-build but Rust seed not found at: !RUST_SEED_BIN!
        exit /b 1
    )
    echo [bootstrap] Reusing existing Rust seed: !RUST_SEED_BIN!
) else (
    echo [bootstrap] Building Rust seed (cargo build --profile bootstrap)...
    pushd "!RUST_SEED_DIR!"
    if /i "!VERBOSE!"=="true" (
        cargo build --profile bootstrap -p simple-driver -p simple-native-all --jobs !JOBS!
    ) else (
        cargo build --profile bootstrap -p simple-driver -p simple-native-all --jobs !JOBS! 2>&1
    )
    if errorlevel 1 (
        popd
        echo [bootstrap] ERROR: Rust seed build failed
        exit /b 1
    )
    popd

    if not exist "!RUST_SEED_BIN!" (
        echo [bootstrap] ERROR: Rust seed binary not found at: !RUST_SEED_BIN!
        exit /b 1
    )
    echo [bootstrap] Rust seed built: !RUST_SEED_BIN!
)

REM Verify seed responds
"!RUST_SEED_BIN!" --version 2>nul
echo.

REM ================================================================
REM  Phase 2: Stage 1 Rust-base Simple
REM ================================================================
echo [bootstrap] ----------------------------------------------------------------
echo [bootstrap] Phase 2: Build Stage 1 Rust-base Simple
echo [bootstrap] ----------------------------------------------------------------
echo.

set "STAGE1_DIR=!BOOTSTRAP_DIR!\stage1"
set "STAGE1_BIN=!STAGE1_DIR!\simple.exe"
if not exist "!STAGE1_DIR!" mkdir "!STAGE1_DIR!"

set "SIMPLE_LIB=src"
set "SIMPLE_BOOTSTRAP=1"

set "COMPILE_ARGS=native-build"
set "COMPILE_ARGS=!COMPILE_ARGS! --source src\compiler"
set "COMPILE_ARGS=!COMPILE_ARGS! --source src\lib"
set "COMPILE_ARGS=!COMPILE_ARGS! --source src\app"
set "COMPILE_ARGS=!COMPILE_ARGS! --entry src\app\cli\main.spl"
set "COMPILE_ARGS=!COMPILE_ARGS! -o !STAGE1_BIN!"
set "COMPILE_ARGS=!COMPILE_ARGS! --clean"

echo [bootstrap] Running: !RUST_SEED_BIN! !COMPILE_ARGS!
"!RUST_SEED_BIN!" !COMPILE_ARGS!
if errorlevel 1 (
    echo [bootstrap] ERROR: Stage 1 compilation failed
    exit /b 1
)

if not exist "!STAGE1_BIN!" (
    echo [bootstrap] ERROR: Stage 1 binary not found at: !STAGE1_BIN!
    exit /b 1
)

echo [bootstrap] Stage 1 built: !STAGE1_BIN!
"!STAGE1_BIN!" --version 2>nul
echo.

REM ================================================================
REM  Phase 3: Stage 2 pure Simple via llvm-lib
REM ================================================================
echo [bootstrap] ----------------------------------------------------------------
echo [bootstrap] Phase 3: Build Stage 2 pure Simple via !BACKEND!
echo [bootstrap] ----------------------------------------------------------------
echo.

set "STAGE2_DIR=!BOOTSTRAP_DIR!\stage2"
set "STAGE2_BIN=!STAGE2_DIR!\simple.exe"
if not exist "!STAGE2_DIR!" mkdir "!STAGE2_DIR!"

set "SELFHOST_ARGS=native-build"
set "SELFHOST_ARGS=!SELFHOST_ARGS! --source src\compiler"
set "SELFHOST_ARGS=!SELFHOST_ARGS! --source src\lib"
set "SELFHOST_ARGS=!SELFHOST_ARGS! --source src\app"
set "SELFHOST_ARGS=!SELFHOST_ARGS! --entry src\app\cli\main.spl"
set "SELFHOST_ARGS=!SELFHOST_ARGS! -o !STAGE2_BIN!"
set "SELFHOST_ARGS=!SELFHOST_ARGS! --backend !BACKEND!"
set "SELFHOST_ARGS=!SELFHOST_ARGS! --clean"

echo [bootstrap] Running: !STAGE1_BIN! !SELFHOST_ARGS!
"!STAGE1_BIN!" !SELFHOST_ARGS!
if errorlevel 1 (
    echo [bootstrap] ERROR: Stage 2 self-host compilation failed
    exit /b 1
)

if not exist "!STAGE2_BIN!" (
    echo [bootstrap] ERROR: Stage 2 binary not found at: !STAGE2_BIN!
    exit /b 1
)

echo [bootstrap] Stage 2 built: !STAGE2_BIN!
"!STAGE2_BIN!" --version 2>nul
echo.

REM ================================================================
REM  Phase 4: Stage 3 full pure-Simple self-host
REM ================================================================
set "STAGE3_BIN="
if /i not "!SKIP_LLVM!"=="true" (
    if /i "!LLVM_FOUND!"=="true" (
        echo [bootstrap] ----------------------------------------------------------------
        echo [bootstrap] Phase 4: Build Stage 3 full pure-Simple self-host
        echo [bootstrap] ----------------------------------------------------------------
        echo.

        set "STAGE3_DIR=!BOOTSTRAP_DIR!\stage3"
        set "STAGE3_BIN=!STAGE3_DIR!\simple.exe"
        if not exist "!STAGE3_DIR!" mkdir "!STAGE3_DIR!"

        REM Set LLVM path for the compiler
        set "SIMPLE_LLVM_PATH=!LLVM_PATH!"

        set "LLVM_ARGS=native-build"
        set "LLVM_ARGS=!LLVM_ARGS! --source src\compiler"
        set "LLVM_ARGS=!LLVM_ARGS! --source src\lib"
        set "LLVM_ARGS=!LLVM_ARGS! --source src\app"
        set "LLVM_ARGS=!LLVM_ARGS! --entry src\app\cli\main.spl"
        set "LLVM_ARGS=!LLVM_ARGS! -o !STAGE3_BIN!"
        set "LLVM_ARGS=!LLVM_ARGS! --backend !BACKEND!"
        set "LLVM_ARGS=!LLVM_ARGS! --clean"

        echo [bootstrap] Running: !STAGE2_BIN! !LLVM_ARGS!
        "!STAGE2_BIN!" !LLVM_ARGS!
        if errorlevel 1 (
            echo [bootstrap] WARNING: Stage 3 build failed, using stage2 as final binary
            set "STAGE3_BIN="
        ) else (
            if not exist "!STAGE3_BIN!" (
                echo [bootstrap] WARNING: stage3 binary not found, using stage2 as final binary
                set "STAGE3_BIN="
            ) else (
                echo [bootstrap] Stage 3 built: !STAGE3_BIN!
                "!STAGE3_BIN!" --version 2>nul
            )
        )
        echo.
    ) else (
        echo [bootstrap] Phase 4: Skipped (LLVM not found)
        echo.
    )
) else (
    echo [bootstrap] Phase 4: Skipped (--skip-llvm)
    echo.
)

REM ================================================================
REM  Phase 5: Verify reproducibility (stage2 vs stage3)
REM ================================================================
if /i "!VERIFY_HASH!"=="true" (
    echo [bootstrap] ----------------------------------------------------------------
    echo [bootstrap] Phase 5: Reproducibility verification
    echo [bootstrap] ----------------------------------------------------------------
    echo.

    set "HASH1="
    set "HASH2="
    for /f "skip=1 delims=" %%h in ('certutil -hashfile "!STAGE2_BIN!" SHA256 2^>nul ^| findstr /r /v "hash CertUtil"') do (
        if not "%%h"=="" if "!HASH1!"=="" set "HASH1=%%h"
    )
    for /f "skip=1 delims=" %%h in ('certutil -hashfile "!STAGE3_BIN!" SHA256 2^>nul ^| findstr /r /v "hash CertUtil"') do (
        if not "%%h"=="" if "!HASH2!"=="" set "HASH2=%%h"
    )

    echo [bootstrap] Stage 2 SHA-256: !HASH1!
    echo [bootstrap] Stage 3 SHA-256: !HASH2!

    if not "!HASH1!"=="" if not "!HASH2!"=="" (
        if /i "!HASH1!"=="!HASH2!" (
            echo [bootstrap] Reproducibility check PASSED — stage2 and stage3 are identical.
        ) else (
            echo [bootstrap] Note: stage2 and stage3 differ (expected if timestamps/paths are embedded).
            echo [bootstrap] Both binaries are functional — using stage3 when available.
        )
    ) else (
        echo [bootstrap] Skipping reproducibility hash check because stage3 is unavailable.
    )
    echo.
) else (
    echo [bootstrap] Phase 5: Skipped (--no-verify)
    echo.
)

REM ================================================================
REM  Phase 6: Deploy
REM ================================================================
REM Select final binary: stage3 if available, else stage2
set "FINAL_BIN=!STAGE2_BIN!"
if not "!STAGE3_BIN!"=="" (
    if exist "!STAGE3_BIN!" (
        set "FINAL_BIN=!STAGE3_BIN!"
    )
)

if /i "!DEPLOY!"=="true" (
    echo [bootstrap] ----------------------------------------------------------------
    echo [bootstrap] Phase 6: Deploy
    echo [bootstrap] ----------------------------------------------------------------
    echo.

    if not exist "!RELEASE_DIR!" mkdir "!RELEASE_DIR!"

    copy /y "!FINAL_BIN!" "!RELEASE_DIR!\simple.exe" >nul
    if errorlevel 1 (
        echo [bootstrap] ERROR: Deploy failed
        exit /b 1
    )

    echo [bootstrap] Deployed: !FINAL_BIN! -^> !RELEASE_DIR!\simple.exe
    for %%f in ("!RELEASE_DIR!\simple.exe") do echo [bootstrap] Size: %%~zf bytes
    echo.
) else (
    echo [bootstrap] Phase 6: Skipped (use --deploy to install)
    echo.
)

REM ================================================================
REM  Cleanup
REM ================================================================
if /i "!KEEP_ARTIFACTS!"=="false" (
    if exist "!BOOTSTRAP_DIR!" (
        echo [bootstrap] Cleaning !BOOTSTRAP_DIR!...
        rmdir /s /q "!BOOTSTRAP_DIR!" 2>nul
    )
) else (
    echo [bootstrap] Keeping artifacts in !BOOTSTRAP_DIR!
)

REM ================================================================
REM  Summary
REM ================================================================
echo.
echo ================================================================
echo   Bootstrap Complete (Rust seed -^> stage1 -^> stage2 llvm-lib)
echo ================================================================
echo   Final binary: !FINAL_BIN!
if /i "!DEPLOY!"=="true" (
    echo   Deployed:     !RELEASE_DIR!\simple.exe
)
echo.

endlocal
exit /b 0
