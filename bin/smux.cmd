@echo off
rem smux - Simple terminal multiplexer (Windows).
call "%~dp0simple.cmd" "%~dp0..\src\app\hosted_apps\smux_client.spl" %*
exit /b %ERRORLEVEL%
