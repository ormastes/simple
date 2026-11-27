@echo off
setlocal
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
