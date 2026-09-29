@echo off
node "%~dp0launch.cjs" %*
exit /b %ERRORLEVEL%
