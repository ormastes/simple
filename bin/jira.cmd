@echo off
setlocal

set "SCRIPT_DIR=%~dp0"
set "TOOL_SCRIPT=%SCRIPT_DIR%..\tools\jira-cli\bin\jira"

rem Try bash (Git Bash / WSL / MSYS2)
where bash >nul 2>nul
if %errorlevel% equ 0 (
    bash "%TOOL_SCRIPT%" %*
    exit /b %errorlevel%
)

echo error: jira requires bash (Git Bash, WSL, or MSYS2). >&2
exit /b 1
