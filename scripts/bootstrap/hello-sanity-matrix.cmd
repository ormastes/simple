@echo off
setlocal EnableDelayedExpansion
rem Phases 1-2: hello-sanity-matrix.py. Phase 3: pure-Simple twin on the
rem verified stage binary SIMPLE_VERIFIED_STAGE_BINARY, pinned by
rem SIMPLE_VERIFIED_STAGE_PIN (or --stage-pin); fails closed without it.
set "phase="
set "prev="
for %%A in (%*) do (
  set "arg=%%~A"
  if "!prev!"=="--phase" set "phase=!arg!"
  if "!arg:~0,8!"=="--phase=" set "phase=!arg:~8!"
  set "prev=!arg!"
)
if not "!phase!"=="3" goto py_owner
if not defined SIMPLE_VERIFIED_STAGE_BINARY goto no_stage
if not exist "%SIMPLE_VERIFIED_STAGE_BINARY%" goto no_stage
"%SIMPLE_VERIFIED_STAGE_BINARY%" run "%~dp0hello-sanity-matrix.spl" --stage-binary "%SIMPLE_VERIFIED_STAGE_BINARY%" %*
exit /b %errorlevel%
:no_stage
echo ERROR: phase 3 requires SIMPLE_VERIFIED_STAGE_BINARY (verified stage binary); no Python fallback 1>&2
exit /b 2
:py_owner
where py >nul 2>nul
if errorlevel 1 goto python
py -3 "%~dp0hello-sanity-matrix.py" %*
exit /b %errorlevel%
:python
where python >nul 2>nul
if errorlevel 1 (
  echo ERROR: hello-sanity-matrix requires native Python 3.12 or newer. 1>&2
  exit /b 2
)
python "%~dp0hello-sanity-matrix.py" %*
exit /b %errorlevel%
