@echo off
setlocal
REM Windows twin of the rust_worker cargo fixture (cargo, no extension).
REM Dispatches on the argument stream exactly like the POSIX case statement:
REM   metadata / --version / --features timeout / --features malformed /
REM   clippy / check, else exit 64.
set "args= %* "
echo %args% | findstr /C:" --features timeout " >nul
if %errorlevel%==0 goto do_timeout
echo %args% | findstr /C:" --features malformed " >nul
if %errorlevel%==0 goto do_malformed
echo %args% | findstr /C:" metadata " >nul
if %errorlevel%==0 goto do_metadata
echo %args% | findstr /C:" --version " >nul
if %errorlevel%==0 goto do_version
echo %args% | findstr /C:" clippy " >nul
if %errorlevel%==0 goto do_clippy
echo %args% | findstr /C:" check " >nul
if %errorlevel%==0 goto do_check
exit /b 64

:do_metadata
echo {"packages":[],"workspace_root":"fixture","version":1}
exit /b 0

:do_version
echo cargo 1.90.0 (fixture)
exit /b 0

:do_timeout
%SystemRoot%\System32\ping.exe -n 3 127.0.0.1 >nul
exit /b 0

:do_malformed
echo not-json
exit /b 0

:do_clippy
echo {"reason":"compiler-message","message":{"level":"warning","code":{"code":"clippy::needless_return"},"message":"unneeded return","spans":[{"file_name":"src/lib.rs","byte_start":0,"byte_end":1,"line_start":1,"line_end":1,"column_start":1,"column_end":2}],"children":[]}}
exit /b 0

:do_check
echo {"reason":"compiler-message","message":{"level":"error","code":{"code":"E0425"},"message":"cannot find value","spans":[{"file_name":"src/lib.rs","byte_start":0,"byte_end":1,"line_start":1,"line_end":1,"column_start":1,"column_end":2}],"children":[]}}
exit /b 0
