@echo off
REM Revert directory write restrictions (Windows)
REM Restores original permissions saved by apply_restrictions.bat
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

REM Check if backup exists
if not exist "%STATE_FILE%" (
    echo Error: No backup file found at %STATE_FILE%
    echo Restrictions may not have been applied, or backup was deleted.
    pause
    exit /b 1
)

cd /d "%PROJECT_ROOT%"

echo === Simple Project Directory Protection - Revert (Windows) ===
echo Project root: %CD%
echo.
echo Restoring original permissions from: %STATE_FILE%
echo.

REM Get current user
for /f "tokens=*" %%u in ('whoami') do set CURRENT_USER=%%u

echo Removing deny rules...
echo.

REM Remove deny rules from project root
echo Removing restrictions from project root...
icacls "." /remove:d "%CURRENT_USER%" >nul 2>&1
if %errorLevel% equ 0 (
    echo   * Project root: removed deny rule
) else (
    echo   ! Warning: No deny rule found on project root
)

REM Remove deny rules from doc/
if exist "doc\" (
    echo Removing restrictions from doc\...
    icacls "doc" /remove:d "%CURRENT_USER%" >nul 2>&1
    if !errorLevel! equ 0 (
        echo   * doc\: removed deny rule
    ) else (
        echo   ! Warning: No deny rule found on doc\
    )
)

REM Remove deny rules from examples/
if exist "examples\" (
    echo Removing restrictions from examples\...
    icacls "examples" /remove:d "%CURRENT_USER%" >nul 2>&1
    if !errorLevel! equ 0 (
        echo   * examples\: removed deny rule
    ) else (
        echo   ! Warning: No deny rule found on examples\
    )
)

REM Remove deny rules from scripts/
if exist "scripts\" (
    echo Removing restrictions from scripts\...
    icacls "scripts" /remove:d "%CURRENT_USER%" >nul 2>&1
    if !errorLevel! equ 0 (
        echo   * scripts\: removed deny rule
    ) else (
        echo   ! Warning: No deny rule found on scripts\
    )
)

echo.
echo Restoring original ACLs...
echo.

REM Restore original ACLs
if exist "%STATE_FILE%.root" (
    echo Restoring project root ACLs...
    icacls "." /restore "%STATE_FILE%.root" >nul 2>&1
    if !errorLevel! equ 0 (
        echo   * Project root restored
    ) else (
        echo   ! Warning: Failed to restore project root ACLs
    )
    del "%STATE_FILE%.root" >nul 2>&1
)

if exist "%STATE_FILE%.doc" (
    echo Restoring doc\ ACLs...
    icacls "doc" /restore "%STATE_FILE%.doc" >nul 2>&1
    if !errorLevel! equ 0 (
        echo   * doc\ restored
    ) else (
        echo   ! Warning: Failed to restore doc\ ACLs
    )
    del "%STATE_FILE%.doc" >nul 2>&1
)

if exist "%STATE_FILE%.examples" (
    echo Restoring examples\ ACLs...
    icacls "examples" /restore "%STATE_FILE%.examples" >nul 2>&1
    if !errorLevel! equ 0 (
        echo   * examples\ restored
    ) else (
        echo   ! Warning: Failed to restore examples\ ACLs
    )
    del "%STATE_FILE%.examples" >nul 2>&1
)

if exist "%STATE_FILE%.scripts" (
    echo Restoring scripts\ ACLs...
    icacls "scripts" /restore "%STATE_FILE%.scripts" >nul 2>&1
    if !errorLevel! equ 0 (
        echo   * scripts\ restored
    ) else (
        echo   ! Warning: Failed to restore scripts\ ACLs
    )
    del "%STATE_FILE%.scripts" >nul 2>&1
)

echo.
echo Removing backup file...
del "%STATE_FILE%" >nul 2>&1

echo.
echo === Restrictions Reverted Successfully ===
echo.
echo All directories restored to original permissions.
echo You can now create/delete files in all directories.
echo.
echo To re-apply restrictions: Run apply_restrictions.bat as Administrator
echo.
pause
