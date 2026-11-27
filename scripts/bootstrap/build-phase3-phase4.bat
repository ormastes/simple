@echo off
rem ==============================================================================
rem PROTECTED BOOTSTRAP SCRIPT — DO NOT MODIFY UNLESS EXPLICITLY REQUESTED BY USER
rem Guarded by: scripts/check/fast-verify-bootstrap-scripts.shs
rem ==============================================================================
rem Windows Batch Entrypoint for Shared Cross-Platform Phased Build (Phase 3 / Phase 4).
rem Supports 2 Windows configs (mingw = DEFAULT, msvc = optional) and forwards to
rem scripts/bootstrap/build-phase3-phase4.sh so all platforms share ONE script!

setlocal
set "SCRIPT_DIR=%~dp0"
set "WIN_CFG=%SIMPLE_WIN_CONFIG%"
if not defined WIN_CFG set "WIN_CFG=mingw"

for %%A in (%*) do (
  if /i "%%~A"=="/msvc" set "WIN_CFG=msvc"
  if /i "%%~A"=="--msvc" set "WIN_CFG=msvc"
  if /i "%%~A"=="--win-config=msvc" set "WIN_CFG=msvc"
  if /i "%%~A"=="/mingw" set "WIN_CFG=mingw"
  if /i "%%~A"=="--mingw" set "WIN_CFG=mingw"
  if /i "%%~A"=="--win-config=mingw" set "WIN_CFG=mingw"
)

set "BOOTSTRAP_BASH="
for /f "delims=" %%G in ('where git.exe 2^>nul') do call :bash_from_git "%%~dpG"
if not defined BOOTSTRAP_BASH if exist "C:\Program Files\Git\bin\bash.exe" set "BOOTSTRAP_BASH=C:\Program Files\Git\bin\bash.exe"
if not defined BOOTSTRAP_BASH if exist "C:\msys64\usr\bin\bash.exe" set "BOOTSTRAP_BASH=C:\msys64\usr\bin\bash.exe"
if not defined BOOTSTRAP_BASH for /f "delims=" %%B in ('where bash.exe 2^>nul') do call :bash_from_path "%%~fB"

if not defined BOOTSTRAP_BASH (
  echo error: build-phase3-phase4.bat requires Git Bash or MSYS2 bash.exe 1>&2
  exit /b 1
)

set "MSYS2_ARG_CONV_EXCL=/msvc;/mingw;--win-config=;CL="
"%BOOTSTRAP_BASH%" "%SCRIPT_DIR%build-phase3-phase4.sh" --win-config=%WIN_CFG% %*
exit /b %ERRORLEVEL%

:bash_from_git
if defined BOOTSTRAP_BASH exit /b 0
if exist "%~1..\bin\bash.exe" set "BOOTSTRAP_BASH=%~1..\bin\bash.exe"
exit /b 0

:bash_from_path
if defined BOOTSTRAP_BASH exit /b 0
if /i "%~1"=="%SystemRoot%\System32\bash.exe" exit /b 0
if /i "%~1"=="%LocalAppData%\Microsoft\WindowsApps\bash.exe" exit /b 0
set "BOOTSTRAP_BASH=%~1"
exit /b 0
