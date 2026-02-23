@echo off
REM Apply directory write restrictions (Windows)
REM Prevents creating/deleting files directly in specified directories
REM while allowing modifications and full access to subdirectories
REM
REM Usage: Run as Administrator
REM        Right-click -> "Run as administrator"

setlocal enabledelayedexpansion

set "SCRIPT_DIR=%~dp0"
set "PROJECT_ROOT=%SCRIPT_DIR%..\..\"
set "STATE_FILE=%SCRIPT_DIR%.permissions_backup.txt"

REM Check if running as administrator
net session >nul 2>&1
if %errorLevel% neq 0 (
    echo Error: This script must be run as Administrator
    echo Right-click the script and select "Run as administrator"
    pause
    exit /b 1
)

REM Check if already applied
if exist "%STATE_FILE%" (
    echo Restrictions already applied. Run revert_restrictions.bat first.
    pause
    exit /b 1
)

cd /d "%PROJECT_ROOT%"

echo === Simple Project Directory Protection (Windows) ===
echo Project root: %CD%
echo.
echo Applying restrictions to prevent file creation/deletion in:
echo   - Project root (.)
echo   - doc\
echo   - examples\
echo   - scripts\
echo.

REM Save current permissions
echo Saving current permissions...
(
    echo # Original permissions backup
    echo # Generated: %DATE% %TIME%
    echo # Windows NTFS ACLs
    echo.
) > "%STATE_FILE%"

REM Save ACLs for each directory
icacls "." /save "%STATE_FILE%.root" /t >nul 2>&1
if exist "doc" icacls "doc" /save "%STATE_FILE%.doc" /t >nul 2>&1
if exist "examples" icacls "examples" /save "%STATE_FILE%.examples" /t >nul 2>&1
if exist "scripts" icacls "scripts" /save "%STATE_FILE%.scripts" /t >nul 2>&1

echo Backup saved to: %STATE_FILE%
echo.

REM Apply restrictions
echo Applying restrictions...
echo.

REM Get current user
for /f "tokens=*" %%u in ('whoami') do set CURRENT_USER=%%u

REM Project root: Deny create files/folders (but allow modifications)
echo Applying to project root...
icacls "." /deny "%CURRENT_USER%:(CI)(WD,AD,WEA,WA)" >nul 2>&1
if %errorLevel% equ 0 (
    echo   * Project root: removed write permission
) else (
    echo   ! Warning: Failed to apply restrictions to project root
)

REM doc/ - if exists
if exist "doc\" (
    echo Applying to doc\...
    icacls "doc" /deny "%CURRENT_USER%:(CI)(WD,AD,WEA,WA)" >nul 2>&1
    if !errorLevel! equ 0 (
        echo   * doc\: removed write permission
    ) else (
        echo   ! Warning: Failed to apply restrictions to doc\
    )
)

REM examples/ - if exists
if exist "examples\" (
    echo Applying to examples\...
    icacls "examples" /deny "%CURRENT_USER%:(CI)(WD,AD,WEA,WA)" >nul 2>&1
    if !errorLevel! equ 0 (
        echo   * examples\: removed write permission
    ) else (
        echo   ! Warning: Failed to apply restrictions to examples\
    )
)

REM scripts/ - if exists
if exist "scripts\" (
    echo Applying to scripts\...
    icacls "scripts" /deny "%CURRENT_USER%:(CI)(WD,AD,WEA,WA)" >nul 2>&1
    if !errorLevel! equ 0 (
        echo   * scripts\: removed write permission
    ) else (
        echo   ! Warning: Failed to apply restrictions to scripts\
    )
)

echo.
echo === Restrictions Applied Successfully ===
echo.
echo Effects:
echo   * Cannot create new files/directories in restricted directories
echo   * Cannot delete files/directories in restricted directories
echo   * CAN modify existing files (file permissions unchanged)
echo   * CAN create/delete in subdirectories (subdirectory permissions unchanged)
echo.
echo Permissions denied:
echo   - WD  = Write Data (create files)
echo   - AD  = Append Data (create folders)
echo   - WEA = Write Extended Attributes
echo   - WA  = Write Attributes
echo.
echo To revert: Run revert_restrictions.bat as Administrator
echo.
pause
