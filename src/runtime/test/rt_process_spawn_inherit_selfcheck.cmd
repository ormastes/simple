@echo off
"%~dp0selfcheck.exe" --child
exit /b %errorlevel%
