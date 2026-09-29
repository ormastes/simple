@echo off
setlocal DisableDelayedExpansion
rem Use Git Bash, never Windows' legacy WSL bash.exe shim.
if defined MAIL_BASH goto configured
if exist "%ProgramFiles%\Git\bin\bash.exe" set "MAIL_BASH=%ProgramFiles%\Git\bin\bash.exe"
if defined MAIL_BASH goto configured
if exist "%LocalAppData%\Programs\Git\bin\bash.exe" set "MAIL_BASH=%LocalAppData%\Programs\Git\bin\bash.exe"
if defined MAIL_BASH goto configured
echo error: Install Git for Windows or set MAIL_BASH to its bash.exe. 1>&2
exit /b 127
:configured
if not exist "%MAIL_BASH%" (
  echo error: MAIL_BASH must name an existing bash.exe. 1>&2
  exit /b 127
)
rem Login initialization supplies Git's Unix utilities; arguments stay arguments.
set "MAIL_SCRIPT=%~dp0mail"
set "MAIL_SCRIPT=%MAIL_SCRIPT:\=/%"
"%MAIL_BASH%" --login "%MAIL_SCRIPT%" %*
exit /b %errorlevel%
