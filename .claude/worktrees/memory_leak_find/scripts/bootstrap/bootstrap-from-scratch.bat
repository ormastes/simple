@echo off
REM Unified bootstrap from scratch (Windows / MSVC clang-cl / MinGW clang++)
REM
REM Stages:
REM   seed, core1, core2, full1, full2
REM
REM Examples:
REM   scripts\bootstrap\bootstrap-from-scratch.bat
REM   scripts\bootstrap\bootstrap-from-scratch.bat --step=core1 --deploy
REM   scripts\bootstrap\bootstrap-from-scratch.bat --step=full2 --deploy --keep-artifacts

setlocal EnableDelayedExpansion

set "STEP=full2"
set "STEP_RANK=5"
set "SKIP_VERIFY=false"
set "JOBS=%NUMBER_OF_PROCESSORS%"
set "CXX="
set "OUTPUT=bin\release\simple"
set "KEEP_ARTIFACTS=false"
set "VERBOSE=false"
set "DEPLOY=auto"
set "RUNTIME_DIR=src\compiler_cpp\runtime"
set "COMPILER_DIR=src\compiler"
set "BUILD_DIR=build\bootstrap"
set "SEED_CPP="
set "RUNTIME_LIB="

if not "%~1"=="" goto :parse_args
goto :args_done

:parse_args
if "%~1"=="" goto :args_done
if /i "%~1"=="--skip-verify"    set "SKIP_VERIFY=true" & shift & goto :parse_args
if /i "%~1"=="--keep-artifacts" set "KEEP_ARTIFACTS=true" & shift & goto :parse_args
if /i "%~1"=="--verbose"        set "VERBOSE=true" & shift & goto :parse_args
if /i "%~1"=="--deploy"         set "DEPLOY=true" & shift & goto :parse_args
if /i "%~1"=="--no-deploy"      set "DEPLOY=false" & shift & goto :parse_args
if /i "%~1"=="--help" goto :usage

set "ARG=%~1"
if /i "!ARG:~0,7!"=="--step="   set "STEP=!ARG:~7!" & shift & goto :parse_args
if /i "!ARG:~0,7!"=="--jobs="   set "JOBS=!ARG:~7!" & shift & goto :parse_args
if /i "!ARG:~0,5!"=="--cc="     set "CXX=!ARG:~5!" & shift & goto :parse_args
if /i "!ARG:~0,9!"=="--output=" set "OUTPUT=!ARG:~9!" & shift & goto :parse_args

echo [bootstrap] ERROR: Unknown option: %~1
exit /b 1

:usage
echo Simple Compiler - Bootstrap From Scratch (Windows)
echo.
echo Usage: scripts\bootstrap\bootstrap-from-scratch.bat [options]
echo.
echo Options:
echo   --step=seed^|core1^|core2^|full1^|full2  Stop after stage ^(default: full2^)
echo   --deploy                                  Copy selected stage output to bin\release\simple
echo   --no-deploy                               Do not copy output
echo   --skip-verify                             Skip full2 reproducibility check
echo   --jobs=N                                  Parallel build jobs
echo   --cc=PATH                                 Target C++ compiler ^(clang-cl, clang++^)
echo   --output=PATH                             Deploy output path ^(default: bin\release\simple^)
echo   --keep-artifacts                          Keep build\bootstrap artifacts
echo   --verbose                                 Print command output
echo   --help                                    Show this help
exit /b 0

:args_done

call :resolve_step_rank
if errorlevel 1 exit /b 1

if /i "!DEPLOY!"=="auto" (
    if !STEP_RANK! GEQ 4 (
        set "DEPLOY=true"
    ) else (
        set "DEPLOY=false"
    )
)

echo ================================================================
echo   Simple Compiler - Bootstrap From Scratch ^(Windows^)
echo ================================================================
echo.

call :step0_prerequisites
if errorlevel 1 exit /b 1

call :step1_seed
if errorlevel 1 exit /b 1
set "ARTIFACT=!SEED_CPP!"

if !STEP_RANK! GEQ 2 (
    call :step2_core1
    if errorlevel 1 exit /b 1
    set "ARTIFACT=%BUILD_DIR%\core1.exe"
)

if !STEP_RANK! GEQ 3 (
    call :step3_core2
    if errorlevel 1 exit /b 1
    set "ARTIFACT=%BUILD_DIR%\core2.exe"
)

if !STEP_RANK! GEQ 4 (
    call :step4_full1
    if errorlevel 1 exit /b 1
    set "ARTIFACT=%BUILD_DIR%\full1.exe"
)

if !STEP_RANK! GEQ 5 (
    call :step5_full2
    if errorlevel 1 exit /b 1
    if /i "!SKIP_VERIFY!"=="false" set "ARTIFACT=%BUILD_DIR%\full2.exe"
)

if /i "!DEPLOY!"=="true" (
    call :deploy_artifact "!ARTIFACT!"
    if errorlevel 1 exit /b 1
)

call :cleanup
if errorlevel 1 exit /b 1

echo ================================================================
echo   Bootstrap Complete
echo ================================================================
echo.
echo   Stage:    !STEP!
echo   Artifact: !ARTIFACT!
if /i "!DEPLOY!"=="true" (
    echo   Deployed: !OUTPUT!
)
echo.

endlocal
exit /b 0

:resolve_step_rank
if /i "!STEP!"=="seed"  set "STEP_RANK=1" & exit /b 0
if /i "!STEP!"=="core1" set "STEP_RANK=2" & exit /b 0
if /i "!STEP!"=="core2" set "STEP_RANK=3" & exit /b 0
if /i "!STEP!"=="full1" set "STEP_RANK=4" & exit /b 0
if /i "!STEP!"=="full2" set "STEP_RANK=5" & exit /b 0
echo [bootstrap] ERROR: Invalid --step value: !STEP!
exit /b 1

:step0_prerequisites
echo [bootstrap] ----------------------------------------------------------------
echo [bootstrap] Step 0: Checking prerequisites
echo [bootstrap] ----------------------------------------------------------------
echo.

if not exist "%SEED_DIR%\seed.cpp" (
    echo [bootstrap] ERROR: %SEED_DIR%\seed.cpp not found
    exit /b 1
)

where cmake >nul 2>&1
if errorlevel 1 (
    echo [bootstrap] ERROR: cmake not found
    exit /b 1
)

if not "%CXX%"=="" goto :cxx_check

for %%c in (clang-cl clang++) do (
    where %%c >nul 2>&1
    if not errorlevel 1 (
        set "CXX=%%c"
        goto :cxx_found
    )
)

echo [bootstrap] ERROR: No supported compiler found ^(clang-cl, clang++^)
exit /b 1

:cxx_check
if /i "%CXX%"=="cl" (
    echo [bootstrap] ERROR: 'cl' is not supported in this script. Use clang-cl for MSVC builds.
    exit /b 1
)
echo %CXX% | findstr /i "clang" >nul
if errorlevel 1 (
    echo [bootstrap] ERROR: Only clang-family compilers are supported ^(clang-cl or clang++^)
    exit /b 1
)
where "%CXX%" >nul 2>&1
if errorlevel 1 (
    echo [bootstrap] ERROR: Specified compiler not found: %CXX%
    exit /b 1
)

:cxx_found
echo [bootstrap] C++ compiler: !CXX!

set "CORE_COUNT=0"
for /r "%COMPILER_CORE_DIR%" %%f in (*.spl) do set /a CORE_COUNT+=1
for /r "%COMPILER_SHARED_DIR%" %%f in (*.spl) do set /a CORE_COUNT+=1
if !CORE_COUNT! EQU 0 (
    echo [bootstrap] ERROR: No .spl files found in %COMPILER_CORE_DIR% or %COMPILER_SHARED_DIR%
    exit /b 1
)

echo.
exit /b 0

:step1_seed
echo [bootstrap] ----------------------------------------------------------------
echo [bootstrap] Step 1: Building seed compiler
echo [bootstrap] ----------------------------------------------------------------
echo.

if not exist "%SEED_BUILD_DIR%" mkdir "%SEED_BUILD_DIR%"

if /i "!VERBOSE!"=="true" (
    cmake -S "%SEED_DIR%" -B "%SEED_BUILD_DIR%" -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_COMPILER="!CXX!"
) else (
    cmake -S "%SEED_DIR%" -B "%SEED_BUILD_DIR%" -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_COMPILER="!CXX!" >nul 2>&1
)
if errorlevel 1 (
    echo [bootstrap] ERROR: cmake configuration failed
    exit /b 1
)

cmake --build "%SEED_BUILD_DIR%" --parallel %JOBS% --target seed_cpp spl_runtime
if errorlevel 1 (
    echo [bootstrap] ERROR: seed build failed
    exit /b 1
)

set "SEED_CPP="
if exist "%SEED_BUILD_DIR%\seed_cpp.exe" set "SEED_CPP=%SEED_BUILD_DIR%\seed_cpp.exe"
if exist "%SEED_BUILD_DIR%\Release\seed_cpp.exe" set "SEED_CPP=%SEED_BUILD_DIR%\Release\seed_cpp.exe"
if exist "%SEED_BUILD_DIR%\Debug\seed_cpp.exe" set "SEED_CPP=%SEED_BUILD_DIR%\Debug\seed_cpp.exe"
if "!SEED_CPP!"=="" (
    echo [bootstrap] ERROR: seed_cpp not found after build
    exit /b 1
)

echo [bootstrap] seed_cpp: !SEED_CPP!

set "RUNTIME_LIB="
if exist "%SEED_BUILD_DIR%\spl_runtime.lib" set "RUNTIME_LIB=%SEED_BUILD_DIR%\spl_runtime.lib"
if exist "%SEED_BUILD_DIR%\libspl_runtime.a" set "RUNTIME_LIB=%SEED_BUILD_DIR%\libspl_runtime.a"
if exist "%SEED_BUILD_DIR%\Release\spl_runtime.lib" set "RUNTIME_LIB=%SEED_BUILD_DIR%\Release\spl_runtime.lib"
if exist "%SEED_BUILD_DIR%\Debug\spl_runtime.lib" set "RUNTIME_LIB=%SEED_BUILD_DIR%\Debug\spl_runtime.lib"
if "!RUNTIME_LIB!"=="" (
    echo [bootstrap] ERROR: Runtime library not found after build
    exit /b 1
)
echo [bootstrap] runtime: !RUNTIME_LIB!
echo.
exit /b 0

:step2_core1
echo [bootstrap] ----------------------------------------------------------------
echo [bootstrap] Step 2: Building Core1
echo [bootstrap] ----------------------------------------------------------------
echo.

if not exist "%BUILD_DIR%" mkdir "%BUILD_DIR%"

set "INIT_FILES="
set "MAIN_FILES="
set "SPL_FILES="

for /f "delims=" %%f in ('(dir /b /s "%COMPILER_CORE_DIR%\*.spl" 2^>nul ^& dir /b /s "%COMPILER_SHARED_DIR%\*.spl" 2^>nul) ^| sort') do (
    if /i "%%~nxf"=="__init__.spl" (
        if "!INIT_FILES!"=="" (
            set "INIT_FILES="%%f""
        ) else (
            set "INIT_FILES=!INIT_FILES! "%%f""
        )
    ) else if /i "%%~nxf"=="main.spl" (
        if "!MAIN_FILES!"=="" (
            set "MAIN_FILES="%%f""
        ) else (
            set "MAIN_FILES=!MAIN_FILES! "%%f""
        )
    ) else (
        if "!SPL_FILES!"=="" (
            set "SPL_FILES="%%f""
        ) else (
            set "SPL_FILES=!SPL_FILES! "%%f""
        )
    )
)

set "ORDERED_FILES="
if not "!INIT_FILES!"=="" set "ORDERED_FILES=!INIT_FILES!"
if not "!SPL_FILES!"=="" (
    if "!ORDERED_FILES!"=="" (
        set "ORDERED_FILES=!SPL_FILES!"
    ) else (
        set "ORDERED_FILES=!ORDERED_FILES! !SPL_FILES!"
    )
)
if not "!MAIN_FILES!"=="" (
    if "!ORDERED_FILES!"=="" (
        set "ORDERED_FILES=!MAIN_FILES!"
    ) else (
        set "ORDERED_FILES=!ORDERED_FILES! !MAIN_FILES!"
    )
)

"!SEED_CPP!" !ORDERED_FILES! > "%BUILD_DIR%\core1.cpp"
if errorlevel 1 (
    echo [bootstrap] ERROR: seed_cpp transpilation failed
    exit /b 1
)

if /i "!CXX!"=="clang-cl" goto :compile_core1_msvc

goto :compile_core1_gnu

:compile_core1_msvc
!CXX! /nologo /std:c++20 /O2 /EHsc /I"%SEED_DIR%" /I"%SEED_DIR%\platform" "%BUILD_DIR%\core1.cpp" /Fe"%BUILD_DIR%\core1.exe" /link "!RUNTIME_LIB!" ws2_32.lib bcrypt.lib
if errorlevel 1 (
    echo [bootstrap] ERROR: Core1 compilation failed
    exit /b 1
)
goto :core1_done

:compile_core1_gnu
!CXX! -std=c++20 -O2 -I"%SEED_DIR%" -I"%SEED_DIR%\platform" "%BUILD_DIR%\core1.cpp" -o "%BUILD_DIR%\core1.exe" -L"%SEED_BUILD_DIR%" -lspl_runtime -lws2_32 -lbcrypt
if errorlevel 1 (
    echo [bootstrap] ERROR: Core1 compilation failed
    exit /b 1
)

:core1_done
if not exist "%BUILD_DIR%\core1.exe" (
    echo [bootstrap] ERROR: Core1 artifact missing
    exit /b 1
)

echo [bootstrap] Core1: %BUILD_DIR%\core1.exe
echo.
exit /b 0

:step3_core2
echo [bootstrap] ----------------------------------------------------------------
echo [bootstrap] Step 3: Building Core2
echo [bootstrap] ----------------------------------------------------------------
echo.

"%BUILD_DIR%\core1.exe" compile "%COMPILER_CORE_DIR%\main.spl" -o "%BUILD_DIR%\core2.exe"
if errorlevel 1 (
    echo [bootstrap] ERROR: Core2 build failed
    exit /b 1
)

if not exist "%BUILD_DIR%\core2.exe" (
    echo [bootstrap] ERROR: Core2 artifact missing
    exit /b 1
)

echo [bootstrap] Core2: %BUILD_DIR%\core2.exe
echo.
exit /b 0

:step4_full1
echo [bootstrap] ----------------------------------------------------------------
echo [bootstrap] Step 4: Building Full1
echo [bootstrap] ----------------------------------------------------------------
echo.

"%BUILD_DIR%\core2.exe" compile src\app\cli\main.spl -o "%BUILD_DIR%\full1.exe"
if errorlevel 1 (
    echo [bootstrap] ERROR: Full1 build failed
    exit /b 1
)

if not exist "%BUILD_DIR%\full1.exe" (
    echo [bootstrap] ERROR: Full1 artifact missing
    exit /b 1
)

echo [bootstrap] Full1: %BUILD_DIR%\full1.exe
echo.
exit /b 0

:step5_full2
if /i "!SKIP_VERIFY!"=="true" (
    echo [bootstrap] Skipping full2 reproducibility ^(--skip-verify^)
    echo.
    exit /b 0
)

echo [bootstrap] ----------------------------------------------------------------
echo [bootstrap] Step 5: Building Full2 + reproducibility check
echo [bootstrap] ----------------------------------------------------------------
echo.

"%BUILD_DIR%\full1.exe" compile src\app\cli\main.spl -o "%BUILD_DIR%\full2.exe"
if errorlevel 1 (
    echo [bootstrap] ERROR: Full2 build failed
    exit /b 1
)

if not exist "%BUILD_DIR%\full2.exe" (
    echo [bootstrap] ERROR: Full2 artifact missing
    exit /b 1
)

for %%f in ("%BUILD_DIR%\full1.exe") do set "FULL1_SIZE=%%~zf"
for %%f in ("%BUILD_DIR%\full2.exe") do set "FULL2_SIZE=%%~zf"

if not "!FULL1_SIZE!"=="!FULL2_SIZE!" (
    echo [bootstrap] ERROR: Reproducibility size mismatch
    echo [bootstrap]   full1: !FULL1_SIZE!
    echo [bootstrap]   full2: !FULL2_SIZE!
    exit /b 1
)

where certutil >nul 2>&1
if not errorlevel 1 (
    set "HASH1="
    set "HASH2="
    for /f "skip=1 delims=" %%h in ('certutil -hashfile "%BUILD_DIR%\full1.exe" SHA256 ^| findstr /r /v "hash CertUtil"') do (
        if not "%%h"=="" if "!HASH1!"=="" set "HASH1=%%h"
    )
    for /f "skip=1 delims=" %%h in ('certutil -hashfile "%BUILD_DIR%\full2.exe" SHA256 ^| findstr /r /v "hash CertUtil"') do (
        if not "%%h"=="" if "!HASH2!"=="" set "HASH2=%%h"
    )
    if not "!HASH1!"=="" if not "!HASH2!"=="" (
        if /i not "!HASH1!"=="!HASH2!" (
            echo [bootstrap] ERROR: Reproducibility hash mismatch
            echo [bootstrap]   full1: !HASH1!
            echo [bootstrap]   full2: !HASH2!
            exit /b 1
        )
    )
)

echo [bootstrap] Reproducibility verified
echo.
exit /b 0

:deploy_artifact
set "SRC=%~1"
if not exist "!SRC!" (
    echo [bootstrap] ERROR: Cannot deploy missing artifact: !SRC!
    exit /b 1
)

for %%d in ("%OUTPUT%") do if not exist "%%~dpd" mkdir "%%~dpd"
call :deploy_copy_atomic "!SRC!" "%OUTPUT%"
if errorlevel 1 (
    echo [bootstrap] ERROR: Deploy failed to %OUTPUT%
    exit /b 1
)

call :deploy_copy_atomic "!SRC!" "%OUTPUT%.exe"

echo [bootstrap] Deployed: !SRC! -^> %OUTPUT%
exit /b 0

:deploy_copy_atomic
set "SRC=%~1"
set "DEST=%~2"
set "TMP=%~2.tmp.%RANDOM%%RANDOM%"

copy /y "!SRC!" "!TMP!" >nul
if errorlevel 1 exit /b 1

move /y "!TMP!" "!DEST!" >nul
if errorlevel 1 (
    del /q "!TMP!" >nul 2>&1
    exit /b 1
)

exit /b 0

:cleanup
if /i "%KEEP_ARTIFACTS%"=="true" (
    echo [bootstrap] Keeping artifacts in %BUILD_DIR%
    exit /b 0
)

if exist "%BUILD_DIR%" (
    rmdir /s /q "%BUILD_DIR%" 2>nul
)
exit /b 0
