@echo off
rem cs - caret suite (Windows). Delegates to the Simple CLI's `cs` command so
rem binary resolution lives in exactly one place (bin\simple.cmd) instead of
rem being duplicated here. POSIX hosts use the sibling shell script bin\cs.
"%~dp0simple.cmd" cs %*
