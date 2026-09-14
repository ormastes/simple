@echo off
setlocal EnableExtensions EnableDelayedExpansion

rem Windows entry point.  The extensionless bin\devhub remains the POSIX
rem wrapper; this path launches an admitted native runtime directly so Git
rem for Windows (or any other sh.exe) is not a prerequisite.
set "SCRIPT_DIR=%~dp0"
for %%I in ("%SCRIPT_DIR%..") do set "REPO_ROOT=%%~fI"

set "MODE=%DEVHUB_MODE%"
if "%MODE%"=="" set "MODE=ordinary"
set "MODE_CONTROL=0"
if /I "%~1"=="--mode" (
    if "%~2"=="" (
        echo error: --mode requires ordinary or loading 1>&2
        exit /b 2
    )
    set "MODE=%~2"
    set "MODE_CONTROL=1"
    shift
    shift
) else if /I "%~1"=="--mode=ordinary" (
    set "MODE=ordinary"
    set "MODE_CONTROL=1"
    shift
) else if /I "%~1"=="--mode=loading" (
    set "MODE=loading"
    set "MODE_CONTROL=1"
    shift
) else if /I "%~1:~0,7%"=="--mode=" (
    set "MODE=%~1:~7%"
    set "MODE_CONTROL=1"
    shift
)

if /I "%MODE%"=="loading" (
    echo error: DevHub mode=loading is unsupported: no admitted in-tree loader implements this launch path 1>&2
    echo No runtime was launched. Use --mode ordinary with an admitted runnable runtime. 1>&2
    exit /b 78
)
if /I not "%MODE%"=="ordinary" (
    echo error: unsupported DevHub launch mode: %MODE%; choose ordinary or loading 1>&2
    exit /b 2
)

rem Keep the explicit shell override for installations that still want the
rem POSIX wrapper. Mode validation above guarantees loading never probes or
rem executes a shell/runtime, while this branch receives the original argv.
if not "%DEVHUB_SH%"=="" (
    "%ComSpec%" /d /c call "%DEVHUB_SH%" "%SCRIPT_DIR%devhub" %*
    exit /b %ERRORLEVEL%
)

rem Reconstruct only when a wrapper control was consumed. For ordinary
rem invocations without a control, %* is passed verbatim by cmd.exe.
set "FORWARD_ARGS="
if "%MODE_CONTROL%"=="0" set "FORWARD_ARGS=%*"
if "%MODE_CONTROL%"=="1" call :collect_forward_args "%~1" "%~2" "%~3" "%~4" "%~5" "%~6" "%~7" "%~8" "%~9"

:after_collect_forward_args

set "HOST_ARCH=%PROCESSOR_ARCHITEW6432%"
if "%HOST_ARCH%"=="" set "HOST_ARCH=%PROCESSOR_ARCHITECTURE%"
if /I "%HOST_ARCH%"=="AMD64" set "HOST_ARCH=x86_64"
if /I "%HOST_ARCH%"=="ARM64" set "HOST_ARCH=aarch64"
set "HOST_ABI=%SIMPLE_WINDOWS_ABI%"
if "%HOST_ABI%"=="" set "HOST_ABI=msvc"
if /I "%MSYSTEM:~0,5%"=="MINGW" if "%SIMPLE_WINDOWS_ABI%"=="" set "HOST_ABI=gnu"
if /I "%MSYSTEM:~0,4%"=="UCRT" if "%SIMPLE_WINDOWS_ABI%"=="" set "HOST_ABI=gnu"
set "HOST_TARGET=%HOST_ARCH%-pc-windows-%HOST_ABI%"

set "RUNTIME="
set "RECEIPT="
set "VERSION="
set "CHECKED="
for %%C in (
    "%SIMPLE_BINARY%"
    "%REPO_ROOT%\bin\simple.exe"
    "%REPO_ROOT%\bin\release\simple.exe"
    "%REPO_ROOT%\bin\release\x86_64-pc-windows-msvc\simple.exe"
    "%REPO_ROOT%\bin\release\x86_64-pc-windows-gnu\simple.exe"
    "%REPO_ROOT%\bin\release\aarch64-pc-windows-msvc\simple.exe"
    "%REPO_ROOT%\bin\release\aarch64-pc-windows-gnu\simple.exe"
) do if not defined RUNTIME call :try_runtime "%%~fC"

if not defined RUNTIME (
    echo error: no Simple runtime found for devhub 1>&2
    echo mode=ordinary; no fallback was attempted; deploy an admitted runnable runtime 1>&2
    echo checked: !CHECKED! 1>&2
    exit /b 127
)

echo [devhub] mode=ordinary runtime=!RUNTIME! receipt=!RECEIPT! version=!VERSION! 1>&2
if /I "!RUNTIME:~-4!"==".cmd" (
    call "!RUNTIME!" run "%REPO_ROOT%\src\app\devhub\main.spl" !FORWARD_ARGS!
) else if /I "!RUNTIME:~-4!"==".bat" (
    call "!RUNTIME!" run "%REPO_ROOT%\src\app\devhub\main.spl" !FORWARD_ARGS!
) else (
    "!RUNTIME!" run "%REPO_ROOT%\src\app\devhub\main.spl" !FORWARD_ARGS!
)
exit /b %ERRORLEVEL%

:collect_forward_args
if "%~1"=="" goto after_collect_forward_args
set "FORWARD_ARG=%~1"
set "FORWARD_ARGS=!FORWARD_ARGS! "!FORWARD_ARG!""
shift
goto collect_forward_args

:try_runtime
set "CANDIDATE=%~1"
if not exist "!CANDIDATE!" exit /b 0
set "CHECKED=!CHECKED! !CANDIDATE!"
set "CANDIDATE_EXT=!CANDIDATE:~-4!"
if /I not "!CANDIDATE_EXT!"==".exe" if not "%SIMPLE_HOST_RESOLVER_FIXTURE_MODE%"=="1" exit /b 0

set "CANDIDATE_HASH="
for /f "skip=1 tokens=1" %%H in ('certutil -hashfile "!CANDIDATE!" SHA256 2^>nul') do if not defined CANDIDATE_HASH set "CANDIDATE_HASH=%%H"
if not defined CANDIDATE_HASH exit /b 0
set "CANDIDATE_RECEIPT="
for %%R in (
    "!CANDIDATE!.provenance.env"
    "!CANDIDATE!.runtime-provenance.env"
    "!CANDIDATE!.exe.provenance.env"
    "!CANDIDATE!.exe.runtime-provenance.env"
    "%REPO_ROOT%\scripts\lib\runtime-provenance\!CANDIDATE_HASH!.env"
) do if not defined CANDIDATE_RECEIPT if exist "%%~fR" set "CANDIDATE_RECEIPT=%%~fR"
if not defined CANDIDATE_RECEIPT exit /b 0
findstr /b /c:"schema=simple-runtime-provenance-v1" "!CANDIDATE_RECEIPT!" >nul || exit /b 0
findstr /b /c:"status=admitted" "!CANDIDATE_RECEIPT!" >nul || exit /b 0
findstr /b /c:"implementation=pure-simple" "!CANDIDATE_RECEIPT!" >nul || exit /b 0
findstr /b /c:"artifact_sha256=!CANDIDATE_HASH!" "!CANDIDATE_RECEIPT!" >nul || exit /b 0
set "EXPECTED_TARGET=!HOST_TARGET!"
echo(!CANDIDATE!| findstr /i /c:"x86_64-pc-windows-msvc" >nul && set "EXPECTED_TARGET=x86_64-pc-windows-msvc"
echo(!CANDIDATE!| findstr /i /c:"x86_64-pc-windows-gnu" >nul && set "EXPECTED_TARGET=x86_64-pc-windows-gnu"
echo(!CANDIDATE!| findstr /i /c:"aarch64-pc-windows-msvc" >nul && set "EXPECTED_TARGET=aarch64-pc-windows-msvc"
echo(!CANDIDATE!| findstr /i /c:"aarch64-pc-windows-gnu" >nul && set "EXPECTED_TARGET=aarch64-pc-windows-gnu"
findstr /b /c:"target_triple=!EXPECTED_TARGET!" "!CANDIDATE_RECEIPT!" >nul || exit /b 0

set "VERSION_FILE=%TEMP%\devhub-version-%RANDOM%-%RANDOM%.tmp"
call :probe_runtime "!CANDIDATE!" --version >"!VERSION_FILE!" 2>&1
if errorlevel 1 (
    del /q "!VERSION_FILE!" >nul 2>&1
    exit /b 0
)
set "CANDIDATE_VERSION="
set /p CANDIDATE_VERSION=<"!VERSION_FILE!"
del /q "!VERSION_FILE!" >nul 2>&1
if not defined CANDIDATE_VERSION exit /b 0
echo(!CANDIDATE_VERSION!| findstr /i /c:"bootstrap seed only" /c:"Rust-built Simple binary" /c:"Rust-built" >nul && exit /b 0
findstr /b /c:"version_output=!CANDIDATE_VERSION!" "!CANDIDATE_RECEIPT!" >nul || exit /b 0

set "HELP_FILE=%TEMP%\devhub-help-%RANDOM%-%RANDOM%.tmp"
call :probe_runtime "!CANDIDATE!" --help >"!HELP_FILE!" 2>&1
if errorlevel 1 (
    del /q "!HELP_FILE!" >nul 2>&1
    exit /b 0
)
findstr /i /c:"simple test" "!HELP_FILE!" >nul || (
    del /q "!HELP_FILE!" >nul 2>&1
    exit /b 0
)
del /q "!HELP_FILE!" >nul 2>&1
set "RUNTIME=!CANDIDATE!"
set "RECEIPT=!CANDIDATE_RECEIPT!"
set "VERSION=!CANDIDATE_VERSION!"
exit /b 0

:probe_runtime
if /I "%~x1"==".cmd" (
    call "%~1" %2
) else if /I "%~x1"==".bat" (
    call "%~1" %2
) else (
    "%~1" %2
)
exit /b %ERRORLEVEL%
