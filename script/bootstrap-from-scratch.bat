@echo off
REM Bootstrap Simple Compiler From Scratch (Windows)
REM
REM Builds the Simple compiler on a machine with NO pre-existing Simple binary.
REM Only requires: cmake, clang++ (or MSVC cl.exe), and standard Windows tools.
REM
REM Bootstrap chain:
REM   1. cmake builds seed_cpp from seed\seed.cpp (C++ transpiler)
REM   2. seed_cpp transpiles src\compiler_core\*.spl -> C++
REM   3. clang++ compiles C++ + runtime -> Core1 (minimal native compiler)
REM   4. Core1 compiles compiler_core -> Core2 (self-hosting check)
REM   5. Core2 compiles full compiler -> Full1
REM   6. Full1 recompiles itself -> Full2 (reproducibility check)
REM
REM QEMU FreeBSD Support:
REM   --qemu-freebsd    Build in FreeBSD QEMU VM (requires qemu-system-x86_64)
REM   --qemu-vm=PATH    Path to FreeBSD QEMU VM image
REM   --qemu-port=N     SSH port for QEMU VM (default: 10022)
REM
REM Usage:
REM   script\bootstrap-from-scratch.bat [options]
REM
REM Options:
REM   --skip-verify     Skip reproducibility checks
REM   --jobs=N          Parallel build jobs (default: %NUMBER_OF_PROCESSORS%)
REM   --cc=PATH         C++ compiler path (default: auto-detect)
REM   --output=PATH     Final binary location (default: bin\simple.exe)
REM   --keep-artifacts  Keep build\bootstrap\ directory
REM   --verbose         Show detailed command output
REM   --qemu-freebsd    Build in FreeBSD QEMU VM
REM   --qemu-vm=PATH    FreeBSD QEMU VM image path
REM   --qemu-port=N     QEMU VM SSH port (default: 10022)
REM   --help            Show this help

setlocal enabledelayedexpansion

REM ============================================================================
REM Configuration
REM ============================================================================

set "SKIP_VERIFY=false"
set "JOBS=%NUMBER_OF_PROCESSORS%"
set "CXX="
set "OUTPUT=bin\simple.exe"
set "KEEP_ARTIFACTS=false"
set "VERBOSE=false"
set "BUILD_DIR=build\bootstrap"
set "SEED_DIR=seed"
set "COMPILER_CORE_DIR=src\compiler_core"

REM QEMU FreeBSD support
set "QEMU_FREEBSD=false"
set "QEMU_VM_PATH="
set "QEMU_PORT=10022"
set "QEMU_USER=freebsd"

REM ============================================================================
REM Argument parsing
REM ============================================================================

:parse_args
if "%~1"=="" goto :args_done
if "%~1"=="--skip-verify"    set "SKIP_VERIFY=true" & shift & goto :parse_args
if "%~1"=="--keep-artifacts" set "KEEP_ARTIFACTS=true" & shift & goto :parse_args
if "%~1"=="--verbose"        set "VERBOSE=true" & shift & goto :parse_args
if "%~1"=="--qemu-freebsd"   set "QEMU_FREEBSD=true" & shift & goto :parse_args
if "%~1"=="--help" (
    echo Simple Compiler — Bootstrap From Scratch (Windows)
    echo.
    echo Usage: script\bootstrap-from-scratch.bat [options]
    echo.
    echo Options:
    echo   --skip-verify     Skip reproducibility checks
    echo   --jobs=N          Parallel build jobs
    echo   --cc=PATH         C++ compiler path
    echo   --output=PATH     Final binary location (default: bin\simple.exe)
    echo   --keep-artifacts  Keep build\bootstrap\ directory
    echo   --verbose         Show detailed command output
    echo   --qemu-freebsd    Build in FreeBSD QEMU VM
    echo   --qemu-vm=PATH    FreeBSD QEMU VM image path
    echo   --qemu-port=N     QEMU VM SSH port (default: 10022)
    echo   --help            Show this help
    exit /b 0
)
REM Handle --key=value options
set "ARG=%~1"
if "!ARG:~0,7!"=="--jobs=" set "JOBS=!ARG:~7!" & shift & goto :parse_args
if "!ARG:~0,5!"=="--cc="   set "CXX=!ARG:~5!" & shift & goto :parse_args
if "!ARG:~0,9!"=="--output=" set "OUTPUT=!ARG:~9!" & shift & goto :parse_args
if "!ARG:~0,11!"=="--qemu-vm=" set "QEMU_VM_PATH=!ARG:~11!" & shift & goto :parse_args
if "!ARG:~0,13!"=="--qemu-port=" set "QEMU_PORT=!ARG:~13!" & shift & goto :parse_args

echo Unknown option: %~1
echo Run with --help for usage
exit /b 1

:args_done

REM ============================================================================
REM QEMU FreeBSD Support Functions
REM ============================================================================

:check_qemu_freebsd
if "!QEMU_FREEBSD!"=="false" goto :qemu_done

echo [bootstrap] QEMU FreeBSD mode enabled
echo.

REM Check for QEMU
where qemu-system-x86_64 >nul 2>&1
if errorlevel 1 (
    echo [bootstrap] ERROR: qemu-system-x86_64 not found
    echo [bootstrap] Install QEMU for Windows from https://www.qemu.org/download/
    exit /b 1
)

REM Auto-detect VM if not specified
if "!QEMU_VM_PATH!"=="" (
    if exist "build\freebsd\vm\FreeBSD-14.3-RELEASE-amd64.qcow2" (
        set "QEMU_VM_PATH=build\freebsd\vm\FreeBSD-14.3-RELEASE-amd64.qcow2"
    ) else if exist "%USERPROFILE%\.qemu\freebsd.qcow2" (
        set "QEMU_VM_PATH=%USERPROFILE%\.qemu\freebsd.qcow2"
    ) else (
        echo [bootstrap] ERROR: No FreeBSD VM found. Use --qemu-vm=PATH
        echo [bootstrap] Or run: bin\simple script\download_qemu.spl freebsd
        exit /b 1
    )
)

echo [bootstrap] Using FreeBSD VM: !QEMU_VM_PATH!
echo [bootstrap] SSH port: !QEMU_PORT!
echo.

REM Check if VM is already running
ssh -o ConnectTimeout=2 -o StrictHostKeyChecking=no -p !QEMU_PORT! !QEMU_USER!@localhost "echo VM alive" >nul 2>&1
if not errorlevel 1 (
    echo [bootstrap] FreeBSD VM already running
    goto :run_freebsd_bootstrap
)

REM Start QEMU VM
echo [bootstrap] Starting FreeBSD QEMU VM...
if not exist "build\freebsd\vm" mkdir "build\freebsd\vm"

start /b qemu-system-x86_64 -machine accel=whpx:tcg -cpu max -m 4G -smp 4 -drive file="!QEMU_VM_PATH!",format=qcow2,if=virtio -net nic,model=virtio -net user,hostfwd=tcp::!QEMU_PORT!-:22 -nographic

REM Wait for SSH
echo [bootstrap] Waiting for SSH on port !QEMU_PORT!...
set RETRIES=30
:wait_ssh
ssh -o ConnectTimeout=2 -o StrictHostKeyChecking=no -p !QEMU_PORT! !QEMU_USER!@localhost "echo SSH ready" >nul 2>&1
if not errorlevel 1 goto :ssh_ready
timeout /t 2 /nobreak >nul
set /a RETRIES-=1
if !RETRIES! gtr 0 goto :wait_ssh

echo [bootstrap] ERROR: Timeout waiting for SSH
exit /b 1

:ssh_ready
echo [bootstrap] SSH connection established
echo.

:run_freebsd_bootstrap
REM Sync project to VM (requires rsync or alternative)
echo [bootstrap] Syncing project to FreeBSD VM...
echo [bootstrap] NOTE: Install rsync on Windows or use WinSCP for file sync
echo [bootstrap] For now, assuming project is already synced or using shared folder
echo.

REM Run FreeBSD bootstrap in VM
echo [bootstrap] Running bootstrap in FreeBSD VM...
set "VM_OPTS="
if "!SKIP_VERIFY!"=="true" set "VM_OPTS=--skip-verify"
if "!KEEP_ARTIFACTS!"=="true" set "VM_OPTS=!VM_OPTS! --keep-artifacts"
if "!VERBOSE!"=="true" set "VM_OPTS=!VM_OPTS! --verbose"

ssh -o StrictHostKeyChecking=no -p !QEMU_PORT! !QEMU_USER!@localhost "cd ~/simple && script/bootstrap-from-scratch-freebsd.sh !VM_OPTS!"
if errorlevel 1 (
    echo [bootstrap] ERROR: FreeBSD VM bootstrap failed
    exit /b 1
)

REM Retrieve binary (requires scp)
echo [bootstrap] Retrieving built binary from FreeBSD VM...
if not exist "bin" mkdir "bin"
scp -P !QEMU_PORT! -o StrictHostKeyChecking=no !QEMU_USER!@localhost:~/simple/bin/simple !OUTPUT!
if errorlevel 1 (
    echo [bootstrap] ERROR: Failed to retrieve binary from VM
    exit /b 1
)

echo.
echo ================================================================
echo   FreeBSD Bootstrap Complete (via QEMU)
echo ================================================================
echo.
echo   Binary: !OUTPUT!
echo   Platform: FreeBSD (built in QEMU VM)
echo.
exit /b 0

:qemu_done

REM ============================================================================
REM Step 0: Prerequisites
REM ============================================================================

REM Check if QEMU FreeBSD mode is enabled
call :check_qemu_freebsd
if errorlevel 1 exit /b 1

echo ================================================================
echo   Simple Compiler — Bootstrap From Scratch (Windows)
echo ================================================================
echo.

echo [bootstrap] Step 0: Checking prerequisites
echo ----------------------------------------------------------------
echo.

REM Check cmake
where cmake >nul 2>&1
if errorlevel 1 (
    echo [bootstrap] ERROR: cmake not found. Install from https://cmake.org
    exit /b 1
)
for /f "tokens=*" %%i in ('cmake --version 2^>nul ^| findstr /n "." ^| findstr "^1:"') do (
    set "CMAKE_VER=%%i"
    set "CMAKE_VER=!CMAKE_VER:~2!"
)
echo [bootstrap] cmake: !CMAKE_VER!

REM Find C++ compiler
if not "!CXX!"=="" (
    where "!CXX!" >nul 2>&1
    if errorlevel 1 (
        echo [bootstrap] ERROR: Specified compiler not found: !CXX!
        exit /b 1
    )
    goto :cxx_found
)

where clang++ >nul 2>&1
if not errorlevel 1 (
    set "CXX=clang++"
    goto :cxx_found
)

where cl >nul 2>&1
if not errorlevel 1 (
    set "CXX=cl"
    goto :cxx_found
)

where g++ >nul 2>&1
if not errorlevel 1 (
    set "CXX=g++"
    goto :cxx_found
)

echo [bootstrap] ERROR: No C++ compiler found. Install clang++, MSVC, or g++.
exit /b 1

:cxx_found
echo [bootstrap] C++ compiler: !CXX!

REM Check seed source
if not exist "%SEED_DIR%\seed.cpp" (
    echo [bootstrap] ERROR: %SEED_DIR%\seed.cpp not found. Are you in the project root?
    exit /b 1
)
echo [bootstrap] Seed source: %SEED_DIR%\seed.cpp

REM Count compiler_core files
set "CORE_COUNT=0"
for /r "%COMPILER_CORE_DIR%" %%f in (*.spl) do set /a CORE_COUNT+=1
if !CORE_COUNT! equ 0 (
    echo [bootstrap] ERROR: %COMPILER_CORE_DIR% has no .spl files
    exit /b 1
)
echo [bootstrap] Compiler core: !CORE_COUNT! .spl files

echo.
echo [bootstrap] All prerequisites OK
echo.

REM ============================================================================
REM Step 1: Build seed compiler
REM ============================================================================

echo [bootstrap] ================================================================
echo [bootstrap] Step 1: Building seed compiler
echo [bootstrap] ================================================================
echo.

if not exist "%SEED_DIR%\build" mkdir "%SEED_DIR%\build"

echo [bootstrap] Configuring with cmake...
cmake -S "%SEED_DIR%" -B "%SEED_DIR%\build" >nul 2>&1
if errorlevel 1 (
    echo [bootstrap] cmake configure failed, retrying with verbose...
    cmake -S "%SEED_DIR%" -B "%SEED_DIR%\build"
    if errorlevel 1 (
        echo [bootstrap] ERROR: cmake configuration failed
        exit /b 1
    )
)

echo [bootstrap] Building seed_cpp + runtime (%JOBS% jobs)...
cmake --build "%SEED_DIR%\build" --parallel %JOBS%
if errorlevel 1 (
    echo [bootstrap] ERROR: seed build failed
    exit /b 1
)

REM Find the seed_cpp binary (could be .exe on Windows)
set "SEED_CPP="
if exist "%SEED_DIR%\build\seed_cpp.exe" set "SEED_CPP=%SEED_DIR%\build\seed_cpp.exe"
if exist "%SEED_DIR%\build\Debug\seed_cpp.exe" set "SEED_CPP=%SEED_DIR%\build\Debug\seed_cpp.exe"
if exist "%SEED_DIR%\build\Release\seed_cpp.exe" set "SEED_CPP=%SEED_DIR%\build\Release\seed_cpp.exe"
if "!SEED_CPP!"=="" (
    echo [bootstrap] ERROR: seed_cpp binary not found after build
    exit /b 1
)
echo [bootstrap] seed_cpp: !SEED_CPP!

REM Find runtime library
set "RUNTIME_LIB="
if exist "%SEED_DIR%\build\spl_runtime.lib" set "RUNTIME_LIB=%SEED_DIR%\build\spl_runtime.lib"
if exist "%SEED_DIR%\build\libspl_runtime.a" set "RUNTIME_LIB=%SEED_DIR%\build\libspl_runtime.a"
if exist "%SEED_DIR%\build\Debug\spl_runtime.lib" set "RUNTIME_LIB=%SEED_DIR%\build\Debug\spl_runtime.lib"
if exist "%SEED_DIR%\build\Release\spl_runtime.lib" set "RUNTIME_LIB=%SEED_DIR%\build\Release\spl_runtime.lib"
if "!RUNTIME_LIB!"=="" (
    echo [bootstrap] ERROR: Runtime library not found after build
    exit /b 1
)
echo [bootstrap] Runtime lib: !RUNTIME_LIB!

echo.
echo [bootstrap] Seed compiler built successfully
echo.

REM ============================================================================
REM Step 2: Core1 — seed_cpp transpiles compiler_core
REM ============================================================================

echo [bootstrap] ================================================================
echo [bootstrap] Step 2: Core1 (seed_cpp -^> C++ -^> native)
echo [bootstrap] ================================================================
echo.

if not exist "%BUILD_DIR%" mkdir "%BUILD_DIR%"

REM Discover and order .spl files: __init__.spl first, main.spl last
set "INIT_FILE="
set "MAIN_FILE="
set "SPL_FILES="

for /r "%COMPILER_CORE_DIR%" %%f in (*.spl) do (
    set "FNAME=%%~nxf"
    if "!FNAME!"=="__init__.spl" (
        set "INIT_FILE=%%f"
    ) else if "!FNAME!"=="main.spl" (
        set "MAIN_FILE=%%f"
    ) else (
        if "!SPL_FILES!"=="" (
            set "SPL_FILES=%%f"
        ) else (
            set "SPL_FILES=!SPL_FILES! %%f"
        )
    )
)

set "ORDERED_FILES="
if not "!INIT_FILE!"=="" set "ORDERED_FILES=!INIT_FILE!"
if not "!SPL_FILES!"=="" (
    if "!ORDERED_FILES!"=="" (
        set "ORDERED_FILES=!SPL_FILES!"
    ) else (
        set "ORDERED_FILES=!ORDERED_FILES! !SPL_FILES!"
    )
)
if not "!MAIN_FILE!"=="" (
    if "!ORDERED_FILES!"=="" (
        set "ORDERED_FILES=!MAIN_FILE!"
    ) else (
        set "ORDERED_FILES=!ORDERED_FILES! !MAIN_FILE!"
    )
)

echo [bootstrap] Transpiling with seed_cpp...
!SEED_CPP! !ORDERED_FILES! > "%BUILD_DIR%\core1.cpp"
if errorlevel 1 (
    echo [bootstrap] ERROR: seed_cpp transpilation failed
    exit /b 1
)

for %%f in ("%BUILD_DIR%\core1.cpp") do set "CPP_SIZE=%%~zf"
echo [bootstrap] Generated C++: !CPP_SIZE! bytes

if !CPP_SIZE! lss 1000 (
    echo [bootstrap] ERROR: C++ output too small — seed_cpp likely failed
    exit /b 1
)

echo [bootstrap] Compiling with !CXX!...

if "!CXX!"=="cl" (
    REM MSVC compilation
    cl /std:c++20 /O2 /EHsc /Fe:"%BUILD_DIR%\core1.exe" "%BUILD_DIR%\core1.cpp" /I"%SEED_DIR%" /link "!RUNTIME_LIB!"
) else (
    REM clang++ or g++ compilation
    !CXX! -std=c++20 -O2 -o "%BUILD_DIR%\core1.exe" "%BUILD_DIR%\core1.cpp" -I"%SEED_DIR%" -L"%SEED_DIR%\build" -lspl_runtime
)
if errorlevel 1 (
    echo [bootstrap] ERROR: C++ compilation failed
    exit /b 1
)

if not exist "%BUILD_DIR%\core1.exe" (
    echo [bootstrap] ERROR: Core1 binary not created
    exit /b 1
)

for %%f in ("%BUILD_DIR%\core1.exe") do echo [bootstrap] Core1 binary: %%~zf bytes

echo.
echo [bootstrap] Core1 built successfully
echo.

REM ============================================================================
REM Step 3: Core2 — Core1 recompiles compiler_core
REM ============================================================================

echo [bootstrap] ================================================================
echo [bootstrap] Step 3: Core2 (Core1 recompiles compiler_core)
echo [bootstrap] ================================================================
echo.

"%BUILD_DIR%\core1.exe" compile "%COMPILER_CORE_DIR%\main.spl" -o "%BUILD_DIR%\core2.exe"
if errorlevel 1 (
    echo [bootstrap] ERROR: Core1 compilation failed
    exit /b 1
)

if not exist "%BUILD_DIR%\core2.exe" (
    echo [bootstrap] ERROR: Core2 binary not created
    exit /b 1
)

for %%f in ("%BUILD_DIR%\core2.exe") do echo [bootstrap] Core2 binary: %%~zf bytes

echo.
echo [bootstrap] Core2 built successfully
echo.

REM ============================================================================
REM Step 4: Full1 — Core2 compiles full compiler
REM ============================================================================

echo [bootstrap] ================================================================
echo [bootstrap] Step 4: Full1 (Core2 compiles full compiler)
echo [bootstrap] ================================================================
echo.

"%BUILD_DIR%\core2.exe" compile src\app\cli\main.spl -o "%BUILD_DIR%\full1.exe"
if errorlevel 1 (
    echo [bootstrap] ERROR: Core2 compilation of full compiler failed
    exit /b 1
)

if not exist "%BUILD_DIR%\full1.exe" (
    echo [bootstrap] ERROR: Full1 binary not created
    exit /b 1
)

for %%f in ("%BUILD_DIR%\full1.exe") do echo [bootstrap] Full1 binary: %%~zf bytes

echo.
echo [bootstrap] Full1 built successfully
echo.

REM ============================================================================
REM Step 5: Full2 — Reproducibility check
REM ============================================================================

if "!SKIP_VERIFY!"=="true" (
    echo [bootstrap] Skipping Full2 (--skip-verify)
    echo.
    goto :install
)

echo [bootstrap] ================================================================
echo [bootstrap] Step 5: Full2 (reproducibility check)
echo [bootstrap] ================================================================
echo.

"%BUILD_DIR%\full1.exe" compile src\app\cli\main.spl -o "%BUILD_DIR%\full2.exe"
if errorlevel 1 (
    echo [bootstrap] ERROR: Full1 self-recompilation failed
    exit /b 1
)

if not exist "%BUILD_DIR%\full2.exe" (
    echo [bootstrap] ERROR: Full2 binary not created
    exit /b 1
)

for %%f in ("%BUILD_DIR%\full2.exe") do echo [bootstrap] Full2 binary: %%~zf bytes

REM Compare file sizes as basic reproducibility check
for %%f in ("%BUILD_DIR%\full1.exe") do set "FULL1_SIZE=%%~zf"
for %%f in ("%BUILD_DIR%\full2.exe") do set "FULL2_SIZE=%%~zf"

if "!FULL1_SIZE!"=="!FULL2_SIZE!" (
    echo [bootstrap] Reproducibility: sizes match (!FULL1_SIZE! bytes)
    REM Use certutil for hash comparison if available
    where certutil >nul 2>&1
    if not errorlevel 1 (
        for /f "skip=1 tokens=*" %%h in ('certutil -hashfile "%BUILD_DIR%\full1.exe" SHA256 2^>nul ^| findstr /v "hash"') do set "HASH1=%%h"
        for /f "skip=1 tokens=*" %%h in ('certutil -hashfile "%BUILD_DIR%\full2.exe" SHA256 2^>nul ^| findstr /v "hash"') do set "HASH2=%%h"
        if "!HASH1!"=="!HASH2!" (
            echo [bootstrap] Reproducibility: SHA256 MATCH (!HASH1!)
        ) else (
            echo [bootstrap] ERROR: SHA256 MISMATCH
            echo [bootstrap]   Full1: !HASH1!
            echo [bootstrap]   Full2: !HASH2!
            exit /b 1
        )
    )
) else (
    echo [bootstrap] ERROR: Size mismatch: Full1=!FULL1_SIZE!, Full2=!FULL2_SIZE!
    exit /b 1
)

echo.
echo [bootstrap] Reproducibility verified
echo.

REM ============================================================================
REM Step 6: Install
REM ============================================================================

:install
echo [bootstrap] ================================================================
echo [bootstrap] Step 6: Install
echo [bootstrap] ================================================================
echo.

set "SRC_BIN="
if exist "%BUILD_DIR%\full2.exe" (
    set "SRC_BIN=%BUILD_DIR%\full2.exe"
) else (
    set "SRC_BIN=%BUILD_DIR%\full1.exe"
)

REM Create output directory
for %%f in ("%OUTPUT%") do (
    if not exist "%%~dpf" mkdir "%%~dpf"
)

copy /y "!SRC_BIN!" "%OUTPUT%" >nul
echo [bootstrap] Installed: %OUTPUT%

echo.

REM ============================================================================
REM Cleanup
REM ============================================================================

if "!KEEP_ARTIFACTS!"=="false" (
    echo [bootstrap] Cleaning up %BUILD_DIR%...
    rmdir /s /q "%BUILD_DIR%" 2>nul
) else (
    echo [bootstrap] Artifacts kept in %BUILD_DIR%\
    dir "%BUILD_DIR%\"
)

echo.
echo ================================================================
echo   Bootstrap Complete
echo ================================================================
echo.
echo   Binary: %OUTPUT%
echo   Usage:  %OUTPUT% ^<command^>
echo.
echo   Try:    %OUTPUT% --version
echo           %OUTPUT% test
echo           %OUTPUT% build
echo.

endlocal
