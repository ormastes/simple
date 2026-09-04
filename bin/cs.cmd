@echo off
rem cs - caret suite (Windows). Delegates runtime resolution to bin\simple.cmd
rem and launches the same source entry point as the POSIX bin\cs wrapper.
call "%~dp0simple.cmd" "%~dp0..\src\app\llm_caret\cs_main.spl" %*
exit /b %ERRORLEVEL%
