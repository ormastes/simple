@echo off
setlocal EnableDelayedExpansion
rem Phases 1-2: hello-sanity-matrix.py. Phase 3: pure-Simple twin on the
rem verified stage binary SIMPLE_VERIFIED_STAGE_BINARY, pinned by
rem SIMPLE_VERIFIED_STAGE_PIN (or --stage-pin); fails closed without it.
rem The wrapper owns --stage-binary: a caller-supplied one is refused.
rem Arguments are scanned with shift, never "for %%A in (%*)": for expands
rem wildcards (* ?) against the current directory and re-tokenises quotes.
rem cmd splits unquoted --phase=3 into "--phase" "3", which the prev check
rem handles; an empty "" argument ends the scan early (the twin parser still
rem keeps the last --stage-binary, the wrapper's).
set "phase="
set "prev="
:scan
if "%~1"=="" goto scan_done
set "arg=%~1"
if /i "!arg!"=="--stage-binary" goto refuse_stage
if /i "!arg:~0,15!"=="--stage-binary=" goto refuse_stage
if "!prev!"=="--phase" set "phase=!arg!"
if "!arg:~0,8!"=="--phase=" set "phase=!arg:~8!"
set "prev=!arg!"
shift
goto scan
:scan_done
if not "!phase!"=="3" goto py_owner
if not defined SIMPLE_VERIFIED_STAGE_BINARY goto no_stage
if not exist "%SIMPLE_VERIFIED_STAGE_BINARY%" goto no_stage
"%SIMPLE_VERIFIED_STAGE_BINARY%" run "%~dp0hello-sanity-matrix.spl" %* --stage-binary "%SIMPLE_VERIFIED_STAGE_BINARY%"
exit /b %errorlevel%
:refuse_stage
echo ERROR: --stage-binary is owned by the wrapper (SIMPLE_VERIFIED_STAGE_BINARY); refusing a caller-supplied value 1>&2
exit /b 2
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
