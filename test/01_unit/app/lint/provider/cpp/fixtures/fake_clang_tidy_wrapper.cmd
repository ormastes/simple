@echo off
setlocal
REM Windows twin of fake_clang_tidy_wrapper.shs (see that file for the
REM contract). Parses the worker's long options, validates that the compile
REM database and translation unit are present and both SHA-256 fingerprints
REM are 64 hex chars, then emits one structured diagnostic with one fix.
set "database="
set "translation_unit="
set "configuration_sha="
set "toolchain_sha="
:args
if "%~1"=="" goto validate
if /I "%~1"=="--compile-database" (set "database=%~2" & shift & shift & goto args)
if /I "%~1"=="--translation-unit" (set "translation_unit=%~2" & shift & shift & goto args)
if /I "%~1"=="--configuration-sha256" (set "configuration_sha=%~2" & shift & shift & goto args)
if /I "%~1"=="--toolchain-sha256" (set "toolchain_sha=%~2" & shift & shift & goto args)
if /I "%~1"=="--configuration-id" (shift & shift & goto args)
if /I "%~1"=="--revision" (shift & shift & goto args)
exit /b 64
:validate
if "%database%"=="" exit /b 64
if "%translation_unit%"=="" exit /b 64
call :strlen "%configuration_sha%" sha_len
if not "%sha_len%"=="64" exit /b 64
call :strlen "%toolchain_sha%" tool_len
if not "%tool_len%"=="64" exit /b 64
echo [{"rule":"modernize-use-nullptr","severity":"warning","path":"%translation_unit%","start_byte":10,"end_byte":14,"message":"use nullptr","fixes":[{"start_byte":10,"end_byte":14,"replacement":"nullptr","machine_applicable":true}]}]
exit /b 0
:strlen
setlocal enabledelayedexpansion
set "s=%~1"
set "len=0"
:strlen_loop
if not "%s%"=="" (
    set "s=%s:~1%"
    set /a len+=1
    goto strlen_loop
)
endlocal & set "%~2=%len%"
exit /b 0
