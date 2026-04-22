@echo off
REM Simple Language — Windows setup (CMD/PowerShell)
REM
REM Creates runtime entries:
REM   bin\simple.exe
REM   bin\simple
REM   bin\simple.cmd
REM   bin\release\simple.exe
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
)
if not defined MSVC_BIN (
    if exist "%RELEASE_DIR%\simple.exe" (
        set "MSVC_BIN=simple.exe"
    )
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
    if defined MINGW_BIN echo   bin\simple     ^(copied from scripts\setup\bin_scripts\simple^)
    if defined MSVC_BIN  echo   bin\simple.cmd ^(copied from scripts\setup\bin_scripts\simple.cmd^)
    if defined MSVC_BIN  echo   bin\simple.exe -^> release\%MSVC_BIN%
    if defined MSVC_BIN  echo   bin\release\simple.exe -^> %RELEASE_DIR%\%MSVC_BIN%
    if not defined MSVC_BIN if defined MINGW_BIN echo   bin\release\simple.exe -^> %RELEASE_DIR%\%MINGW_BIN%
    exit /b 0
)

echo.

REM === Create bin\simple.exe → MSVC binary ===
if defined MSVC_BIN (
    if exist "%REPO_ROOT%\bin\simple.exe" del "%REPO_ROOT%\bin\simple.exe"
    mklink "%REPO_ROOT%\bin\simple.exe" "release\%MSVC_BIN%" >nul 2>&1
    if !errorlevel! neq 0 (
        echo error: failed to create symlink bin\simple.exe -^> release\%MSVC_BIN% >&2
        echo Enable Developer Mode or run elevated so mklink can create symlinks. >&2
        exit /b 1
    ) else (
        echo Created: bin\simple.exe -^> release\%MSVC_BIN%
    )
)

REM === Create bin\release\simple.exe root link ===
set "ROOT_RELEASE_BIN="
if defined MSVC_BIN (
    set "ROOT_RELEASE_BIN=%MSVC_BIN%"
)
if not defined ROOT_RELEASE_BIN (
    if defined MINGW_BIN (
        set "ROOT_RELEASE_BIN=%MINGW_BIN%"
    )
)
if defined ROOT_RELEASE_BIN (
    if exist "%REPO_ROOT%\bin\release\simple.exe" del "%REPO_ROOT%\bin\release\simple.exe"
    mklink "%REPO_ROOT%\bin\release\simple.exe" "%RELEASE_DIR%\%ROOT_RELEASE_BIN%" >nul 2>&1
    if !errorlevel! neq 0 (
        echo error: failed to create symlink bin\release\simple.exe >&2
        echo Enable Developer Mode or run elevated so mklink can create symlinks. >&2
        exit /b 1
    ) else (
        echo Created: bin\release\simple.exe -^> %RELEASE_DIR%\%ROOT_RELEASE_BIN%
    )
)

set "ACTIVE_MCP_TRIPLE="
if defined MSVC_BIN (
    set "ACTIVE_MCP_TRIPLE=%MSVC_TRIPLE%"
) else if defined MINGW_BIN (
    set "ACTIVE_MCP_TRIPLE=%MINGW_TRIPLE%"
)

REM === Generate MCP launcher .cmd scripts in bin\release\<platform>\ ===
echo Generating MCP launcher scripts in bin\release\platform\...
if defined MSVC_BIN call :generate_mcp_wrappers "%MSVC_TRIPLE%"
if defined MINGW_BIN call :generate_mcp_wrappers "%MINGW_TRIPLE%"

REM Remove stale flat release wrappers
for %%M in (simple_mcp_server simple_lsp_mcp_server t32_mcp_server t32_lsp_mcp_server) do (
    if exist "%RELEASE_DIR%\%%M.cmd" del "%RELEASE_DIR%\%%M.cmd"
)

REM Generate bin\ MCP wrappers with absolute exe paths (not symlinks — %~dp0 breaks with symlinks)
call :generate_bin_mcp_wrappers "%ACTIVE_MCP_TRIPLE%"
echo   Generated bin\*_mcp_server.cmd for %ACTIVE_MCP_TRIPLE%

REM === Copy hand-authored simple wrappers ===
if exist "%REPO_ROOT%\scripts\setup\bin_scripts\simple" (
    if exist "%REPO_ROOT%\bin\simple" del "%REPO_ROOT%\bin\simple"
    copy /y "%REPO_ROOT%\scripts\setup\bin_scripts\simple" "%REPO_ROOT%\bin\simple" >nul
    echo   Copied: bin\simple
)
if exist "%REPO_ROOT%\scripts\setup\bin_scripts\simple.cmd" (
    if exist "%REPO_ROOT%\bin\simple.cmd" del "%REPO_ROOT%\bin\simple.cmd"
    copy /y "%REPO_ROOT%\scripts\setup\bin_scripts\simple.cmd" "%REPO_ROOT%\bin\simple.cmd" >nul
    echo   Copied: bin\simple.cmd
)

REM Codex MCP helper launchers for manual debug and startup parity
(
echo @echo off
echo setlocal
echo node "%%~dp0codex_chrome_devtools_mcp.js" %%*
) > "%REPO_ROOT%\bin\codex_chrome_devtools_mcp.cmd"
echo   codex_chrome_devtools_mcp.cmd

(
echo @echo off
echo setlocal
echo node "%%~dp0codex_stitch_mcp.js" %%*
) > "%REPO_ROOT%\bin\codex_stitch_mcp.cmd"
echo   codex_stitch_mcp.cmd

where node >nul 2>&1
if errorlevel 1 (
    echo warning: node.exe not found in PATH; Codex chrome/stitch MCP launchers will not start >&2
) else (
    echo   Verified: node.exe found for Codex MCP launchers
    where codex >nul 2>&1
    if errorlevel 1 (
        echo   Codex CLI not found; skipped global Codex MCP registration
    ) else (
        codex mcp remove chrome-devtools >nul 2>&1
        codex mcp add chrome-devtools -- node "%REPO_ROOT%\bin\codex_chrome_devtools_mcp.js" >nul
        codex mcp remove stitch-mcp >nul 2>&1
        codex mcp add stitch-mcp -- node "%REPO_ROOT%\bin\codex_stitch_mcp.js" >nul
        echo   Registered global Codex MCP launchers: chrome-devtools, stitch-mcp
    )
)

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
echo Creates runtime entries for Windows:
echo   bin\simple.exe
echo   bin\simple
echo   bin\simple.cmd
echo   bin\release\simple.exe
echo.
echo Options:
echo   --dry-run   Show what would be done
exit /b 0

:generate_mcp_wrappers
set "MCP_RELEASE_DIR=%RELEASE_DIR%\%~1"
if not exist "%MCP_RELEASE_DIR%" mkdir "%MCP_RELEASE_DIR%"
echo   %~1\

(
echo @echo off
echo setlocal
echo set "SCRIPT_DIR=%%~dp0"
echo set "SIMPLE_LOG=error"
echo set "RUST_LOG=error"
echo if exist "%%SCRIPT_DIR%%simple_mcp_server.exe" ^(
echo     "%%SCRIPT_DIR%%simple_mcp_server.exe" %%*
echo     exit /b %%ERRORLEVEL%%
echo ^)
echo set "RUNTIME=%%SCRIPT_DIR%%simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\..\src\compiler_rust\target\release\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\..\src\compiler_rust\target\bootstrap\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\release\simple.exe"
echo set "ENTRY=%%SCRIPT_DIR%%..\..\..\src\app\mcp\main.spl"
echo set "SIMPLE_LIB=%%SCRIPT_DIR%%..\..\..\src"
echo "%%RUNTIME%%" run "%%ENTRY%%" %%* 2^>nul
) > "%MCP_RELEASE_DIR%\simple_mcp_server.cmd"

(
echo @echo off
echo setlocal
echo set "SCRIPT_DIR=%%~dp0"
echo set "SIMPLE_LOG=error"
echo set "RUST_LOG=error"
echo if exist "%%SCRIPT_DIR%%simple_lsp_mcp_server.exe" ^(
echo     "%%SCRIPT_DIR%%simple_lsp_mcp_server.exe" %%*
echo     exit /b %%ERRORLEVEL%%
echo ^)
echo set "RUNTIME=%%SCRIPT_DIR%%simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\..\src\compiler_rust\target\release\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\..\src\compiler_rust\target\bootstrap\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\release\simple.exe"
echo set "ENTRY=%%SCRIPT_DIR%%..\..\..\src\app\simple_lsp_mcp\main.spl"
echo set "SIMPLE_LIB=%%SCRIPT_DIR%%..\..\..\src"
echo set "SIMPLE_BINARY=%%RUNTIME%%"
echo "%%RUNTIME%%" run "%%ENTRY%%" %%* 2^>nul
) > "%MCP_RELEASE_DIR%\simple_lsp_mcp_server.cmd"

(
echo @echo off
echo setlocal
echo set "SCRIPT_DIR=%%~dp0"
echo set "RUNTIME=%%SCRIPT_DIR%%..\..\..\src\compiler_rust\target\release\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\..\src\compiler_rust\target\bootstrap\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\release\simple.exe"
echo set "REPO_ROOT=%%SCRIPT_DIR%%..\..\.."
echo set "ENTRY=%%REPO_ROOT%%\examples\10_tooling\trace32_tools\t32_mcp\main.spl"
echo set "SIMPLE_LIB=%%REPO_ROOT%%\examples\10_tooling\trace32_tools"
echo set "SIMPLE_LOG=error"
echo set "RUST_LOG=error"
echo pushd "%%REPO_ROOT%%"
echo "%%RUNTIME%%" "%%ENTRY%%" %%* 2^>nul
) > "%MCP_RELEASE_DIR%\t32_mcp_server.cmd"

(
echo @echo off
echo setlocal
echo set "SCRIPT_DIR=%%~dp0"
echo set "RUNTIME=%%SCRIPT_DIR%%..\..\..\src\compiler_rust\target\release\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\..\src\compiler_rust\target\bootstrap\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\simple.exe"
echo if not exist "%%RUNTIME%%" set "RUNTIME=%%SCRIPT_DIR%%..\..\release\simple.exe"
echo set "REPO_ROOT=%%SCRIPT_DIR%%..\..\.."
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
) > "%MCP_RELEASE_DIR%\t32_lsp_mcp_server.cmd"
exit /b 0

:generate_bin_mcp_wrappers
REM Generate bin\ level .cmd wrappers using %~dp0-relative paths to the triple exe.
REM Symlinks don't work here: %~dp0 in a symlinked .cmd resolves to the symlink's dir (bin\),
REM not the target dir, so the exe lookup must navigate from bin\ to release\<triple>\.
call :write_bin_mcp_wrapper simple_mcp_server "%~1"
call :write_bin_mcp_wrapper simple_lsp_mcp_server "%~1"
call :write_bin_mcp_wrapper t32_mcp_server "%~1"
call :write_bin_mcp_wrapper t32_lsp_mcp_server "%~1"
exit /b 0

:write_bin_mcp_wrapper
REM %~1 = server name (e.g. simple_mcp_server)
REM %~2 = triple (e.g. x86_64-pc-windows-msvc) — embedded into generated path
REM Generated wrapper uses %%~dp0 so it resolves correctly relative to bin\ at runtime.
set "BMW_NAME=%~1"
set "BMW_TRIPLE=%~2"
if exist "%REPO_ROOT%\bin\%BMW_NAME%.cmd" del "%REPO_ROOT%\bin\%BMW_NAME%.cmd"
(
echo @echo off
echo setlocal
echo set "EXE=%%~dp0release\%BMW_TRIPLE%\%BMW_NAME%.exe"
echo if exist "%%EXE%%" ^(
echo     "%%EXE%%" %%*
echo     exit /b %%ERRORLEVEL%%
echo ^)
echo call "%%~dp0release\%BMW_TRIPLE%\%BMW_NAME%.cmd" %%*
) > "%REPO_ROOT%\bin\%BMW_NAME%.cmd"
exit /b 0
