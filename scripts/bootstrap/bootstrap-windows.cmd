@echo off
setlocal
where bash.exe >nul 2>nul
if errorlevel 1 (
  echo error: bootstrap-windows.cmd requires Git Bash or MSYS2 bash.exe 1>&2
  exit /b 1
)
bash.exe "%~dp0bootstrap-from-scratch.sh" windows-entry %*
exit /b %ERRORLEVEL%
