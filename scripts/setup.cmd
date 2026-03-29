@echo off
REM Simple Language — Windows setup (CMD/PowerShell)
REM
REM Creates dual links:
REM   bin\simple.exe → bin\release\<arch>-pc-windows-msvc\simple.exe  (MSVC, for CMD)
REM   bin\simple     → bin\release\<arch>-pc-windows-gnu\simple.exe   (MinGW, for bash)
REM
REM Usage:
REM   scripts\setup.cmd [--dry-run]

setlocal enabledelayedexpansion

set "REPO_ROOT=%~dp0.."
set "DRY_RUN=0"

:parse_args
if "%~1"=="" goto detect
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

set "MSVC_TRIPLE=%ARCH%-pc-windows-msvc"
set "MINGW_TRIPLE=%ARCH%-pc-windows-gnu"
set "RELEASE_DIR=%REPO_ROOT%\bin\release"

echo Architecture: %ARCH%

REM Locate MSVC binary
set "MSVC_BIN="
if exist "%RELEASE_DIR%\%MSVC_TRIPLE%\simple.exe" (
    set "MSVC_BIN=%MSVC_TRIPLE%\simple.exe"
) else if exist "%RELEASE_DIR%\simple.exe" (
    set "MSVC_BIN=simple.exe"
)

REM Locate MinGW binary
set "MINGW_BIN="
if exist "%RELEASE_DIR%\%MINGW_TRIPLE%\simple.exe" (
    set "MINGW_BIN=%MINGW_TRIPLE%\simple.exe"
)

if not defined MSVC_BIN if not defined MINGW_BIN (
    echo error: no release binary found for Windows >&2
    echo. >&2
    echo Searched: >&2
    echo   %RELEASE_DIR%\%MSVC_TRIPLE%\simple.exe >&2
    echo   %RELEASE_DIR%\%MINGW_TRIPLE%\simple.exe >&2
    echo   %RELEASE_DIR%\simple.exe >&2
    echo. >&2
    echo Run the bootstrap first: >&2
    echo   scripts\bootstrap\bootstrap-windows.sh --msvc --deploy >&2
    echo   scripts\bootstrap\bootstrap-windows.sh --mingw --deploy >&2
    exit /b 1
)

if defined MSVC_BIN  echo MSVC binary:  bin\release\%MSVC_BIN%
if defined MINGW_BIN echo MinGW binary: bin\release\%MINGW_BIN%

if "%DRY_RUN%"=="1" (
    echo.
    echo [dry-run] would create:
    if defined MSVC_BIN  echo   bin\simple.exe -^> release\%MSVC_BIN%
    if defined MINGW_BIN echo   bin\simple     -^> release\%MINGW_BIN%
    exit /b 0
)

echo.

REM === Create bin\simple.exe → MSVC binary ===
if defined MSVC_BIN (
    if exist "%REPO_ROOT%\bin\simple.exe" del "%REPO_ROOT%\bin\simple.exe"
    REM Try symlink, then hardlink, then copy
    mklink "%REPO_ROOT%\bin\simple.exe" "release\%MSVC_BIN%" >nul 2>&1
    if !errorlevel! neq 0 (
        mklink /H "%REPO_ROOT%\bin\simple.exe" "%RELEASE_DIR%\%MSVC_BIN%" >nul 2>&1
        if !errorlevel! neq 0 (
            copy "%RELEASE_DIR%\%MSVC_BIN%" "%REPO_ROOT%\bin\simple.exe" >nul
            echo Created: bin\simple.exe [copy] -^> release\%MSVC_BIN%
        ) else (
            echo Created: bin\simple.exe [hardlink] -^> release\%MSVC_BIN%
        )
    ) else (
        echo Created: bin\simple.exe -^> release\%MSVC_BIN%
    )
)

REM === Create bin\simple → MinGW binary (for Git Bash / MSYS2) ===
if defined MINGW_BIN (
    if exist "%REPO_ROOT%\bin\simple" del "%REPO_ROOT%\bin\simple"
    mklink "%REPO_ROOT%\bin\simple" "release\%MINGW_BIN%" >nul 2>&1
    if !errorlevel! neq 0 (
        mklink /H "%REPO_ROOT%\bin\simple" "%RELEASE_DIR%\%MINGW_BIN%" >nul 2>&1
        if !errorlevel! neq 0 (
            copy "%RELEASE_DIR%\%MINGW_BIN%" "%REPO_ROOT%\bin\simple" >nul
            echo Created: bin\simple [copy] -^> release\%MINGW_BIN%
        ) else (
            echo Created: bin\simple [hardlink] -^> release\%MINGW_BIN%
        )
    ) else (
        echo Created: bin\simple -^> release\%MINGW_BIN%
    )
)

REM === Generate MCP launcher .cmd scripts in bin\release\ ===
echo Generating MCP launcher scripts in bin\release\...

REM simple_mcp_server.cmd
(
echo @echo off
echo setlocal
echo set "SCRIPT_DIR=%%~dp0"
echo set "RUNTIME=%%SCRIPT_DIR%%simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%simple"
echo set "ENTRY=%%SCRIPT_DIR%%..\..\src\app\mcp\main.spl"
echo set "SIMPLE_LIB=%%SCRIPT_DIR%%..\..\src"
echo set "SIMPLE_LOG=error"
echo set "RUST_LOG=error"
echo "%%RUNTIME%%" "%%ENTRY%%" %%* 2^>nul
) > "%RELEASE_DIR%\simple_mcp_server.cmd"
echo   simple_mcp_server.cmd

REM simple_lsp_mcp_server.cmd
(
echo @echo off
echo setlocal
echo set "SCRIPT_DIR=%%~dp0"
echo set "RUNTIME=%%SCRIPT_DIR%%simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%simple"
echo set "ENTRY=%%SCRIPT_DIR%%..\..\src\app\simple_lsp_mcp\main.spl"
echo set "SIMPLE_LIB=%%SCRIPT_DIR%%..\..\src"
echo set "SIMPLE_BINARY=%%RUNTIME%%"
echo set "SIMPLE_LOG=error"
echo set "RUST_LOG=error"
echo "%%RUNTIME%%" "%%ENTRY%%" %%* 2^>nul
) > "%RELEASE_DIR%\simple_lsp_mcp_server.cmd"
echo   simple_lsp_mcp_server.cmd

REM t32_mcp_server.cmd
(
echo @echo off
echo setlocal
echo set "SCRIPT_DIR=%%~dp0"
echo set "RUNTIME=%%SCRIPT_DIR%%simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%simple"
echo set "REPO_ROOT=%%SCRIPT_DIR%%..\.."
echo set "ENTRY=%%REPO_ROOT%%\examples\10_tooling\trace32_tools\t32_mcp\main.spl"
echo set "SIMPLE_LIB=%%REPO_ROOT%%\examples\10_tooling\trace32_tools"
echo set "SIMPLE_LOG=error"
echo set "RUST_LOG=error"
echo pushd "%%REPO_ROOT%%"
echo "%%RUNTIME%%" "%%ENTRY%%" %%* 2^>nul
) > "%RELEASE_DIR%\t32_mcp_server.cmd"
echo   t32_mcp_server.cmd

REM t32_lsp_mcp_server.cmd
(
echo @echo off
echo setlocal
echo set "SCRIPT_DIR=%%~dp0"
echo set "RUNTIME=%%SCRIPT_DIR%%simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%simple"
echo set "REPO_ROOT=%%SCRIPT_DIR%%..\.."
echo set "TRACE32_ROOT=%%REPO_ROOT%%\examples\10_tooling\trace32_tools"
echo set "ENTRY=%%TRACE32_ROOT%%\t32_lsp_mcp\main.spl"
echo set "SIMPLE_LIB=%%TRACE32_ROOT%%"
echo set "SIMPLE_RUNTIME=%%RUNTIME%%"
echo set "T32_LSP_MCP_TOOL_RUNNER=examples\10_tooling\trace32_tools\t32_lsp_mcp\tool_runner.spl"
echo set "T32_LSP_MCP_TOOL_DAEMON=examples\10_tooling\trace32_tools\cmm_lsp\mcp_daemon.spl"
echo set "T32_LSP_MCP_TOOL_DAEMON_DIR=%%TEMP%%\t32_lsp_mcp_shared"
echo set "SIMPLE_LOG=error"
echo set "RUST_LOG=error"
echo pushd "%%REPO_ROOT%%"
echo "%%RUNTIME%%" "%%ENTRY%%" %%* 2^>nul
) > "%RELEASE_DIR%\t32_lsp_mcp_server.cmd"
echo   t32_lsp_mcp_server.cmd

REM Create bin\ symlinks/copies for MCP launchers
for %%M in (simple_mcp_server simple_lsp_mcp_server t32_mcp_server t32_lsp_mcp_server) do (
    if exist "%REPO_ROOT%\bin\%%M.cmd" del "%REPO_ROOT%\bin\%%M.cmd"
    mklink "%REPO_ROOT%\bin\%%M.cmd" "release\%%M.cmd" >nul 2>&1
    if !errorlevel! neq 0 (
        copy "%RELEASE_DIR%\%%M.cmd" "%REPO_ROOT%\bin\%%M.cmd" >nul
    )
)
echo   Linked bin\*_mcp_server.cmd

echo.

REM === Create .claude\commands\ symlinks → .claude\skills\ ===
echo.
echo Setting up Claude command symlinks...
set "SKILLS_DIR=%REPO_ROOT%\.claude\skills"
set "COMMANDS_DIR=%REPO_ROOT%\.claude\commands"

if not exist "%SKILLS_DIR%" (
    echo warning: .claude\skills\ not found, skipping command symlinks >&2
    goto verify
)

if not exist "%COMMANDS_DIR%" mkdir "%COMMANDS_DIR%"

set "LINK_COUNT=0"
set "LINK_METHOD="
for %%F in ("%SKILLS_DIR%\*.md") do (
    set "FNAME=%%~nxF"
    if exist "%COMMANDS_DIR%\!FNAME!" del "%COMMANDS_DIR%\!FNAME!"
    mklink "%COMMANDS_DIR%\!FNAME!" "..\skills\!FNAME!" >nul 2>&1
    if !errorlevel! neq 0 (
        copy "%%F" "%COMMANDS_DIR%\!FNAME!" >nul
        set "LINK_METHOD=copy"
    ) else (
        set "LINK_METHOD=symlink"
    )
    set /a LINK_COUNT+=1
)

if "!LINK_METHOD!"=="copy" (
    echo Created: !LINK_COUNT! command files [copy] in .claude\commands\
    echo   Note: Enable Developer Mode for symlinks instead of copies.
) else (
    echo Created: !LINK_COUNT! command symlinks in .claude\commands\
)

:verify
echo.
echo Verify:
if defined MSVC_BIN  echo   bin\simple.exe --version   (MSVC, for CMD/PowerShell)
if defined MINGW_BIN echo   bin\simple --version        (MinGW, for Git Bash)
echo.
echo Setup complete.
exit /b 0

:usage
echo Usage: scripts\setup.cmd [--dry-run]
echo.
echo Creates dual links for Windows:
echo   bin\simple.exe  -^> MSVC binary   (for CMD / PowerShell)
echo   bin\simple      -^> MinGW binary  (for Git Bash / MSYS2)
echo.
echo Options:
echo   --dry-run   Show what would be done
exit /b 0
