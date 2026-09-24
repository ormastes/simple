@echo off
setlocal
rem Run from a Visual Studio x64 developer environment. This narrow regression
rem links the actual C owner with the Rust twin module without a full seed build.
if not defined LLVM_SYS_230_PREFIX set "LLVM_SYS_230_PREFIX=C:\dev\tool\clang+llvm-23.1.1-x86_64-pc-windows-msvc"
set "DIRECTX_LLVM=%LLVM_SYS_230_PREFIX%\bin"
set "SIMPLE_NO_STUB_FALLBACK=1"
set "CARGO_BUILD_JOBS=24"
pushd "%~dp0..\.."
if errorlevel 1 exit /b 1
set "OUT=build\native_probe\directx-submission-abi"
if not exist "%OUT%" mkdir "%OUT%"
"%DIRECTX_LLVM%\clang-cl.exe" /nologo /std:c11 /W4 /WX /c src\runtime\runtime_directx_core.c /Fo"%OUT%\runtime_directx_core.obj" > "%OUT%\c-build.log" 2>&1
if errorlevel 1 goto failed
rustc --edition=2021 --test --emit=obj,link src\compiler_rust\runtime\src\directx_submission_twins.rs -C link-arg=%OUT%\runtime_directx_core.obj -l d3d11 -l dxgi -o "%OUT%\directx_submission_twins.exe" > "%OUT%\rust-build.log" 2>&1
if errorlevel 1 goto failed
"%DIRECTX_LLVM%\llvm-nm.exe" --defined-only "%OUT%\runtime_directx_core.obj" > "%OUT%\c-symbols.log" 2>&1
if errorlevel 1 goto failed
"%DIRECTX_LLVM%\llvm-nm.exe" --defined-only "%OUT%\directx_submission_twins.o" > "%OUT%\rust-symbols.log" 2>&1
if errorlevel 1 goto failed
rem Exact unmangled definitions must all belong to the C object.
powershell -NoProfile -Command "$c = Get-Content '%OUT%\c-symbols.log'; $r = Get-Content '%OUT%\rust-symbols.log'; foreach ($n in 'poll','complete','retire','abandon','readback_pixel') { $p = '\srt_directx_submission_' + $n + '$'; $cc = @($c -match $p).Count; $rc = @($r -match $p).Count; Write-Output ($n + ': C=' + $cc + ' Rust=' + $rc); if ($cc -ne 1 -or $rc -ne 0) { exit 1 } }" > "%OUT%\symbol-check.log" 2>&1
if errorlevel 1 goto failed
"%OUT%\directx_submission_twins.exe" --nocapture --exact tests::rust_twins_remain_callable_and_fail_closed > "%OUT%\tests.log" 2>&1
if errorlevel 1 goto failed
findstr /c:"test result: ok. 1 passed; 0 failed; 0 ignored;" "%OUT%\tests.log" >nul
if errorlevel 1 goto failed
rem This opt-in test must execute on hardware; unavailable D3D11 is a failure.
"%OUT%\directx_submission_twins.exe" --nocapture --ignored --exact tests::windows_c_abi_keeps_real_submission_lifecycle > "%OUT%\hardware-tests.log" 2>&1
if errorlevel 1 goto failed
findstr /c:"test result: ok. 1 passed; 0 failed; 0 ignored;" "%OUT%\hardware-tests.log" >nul
if errorlevel 1 goto failed
type "%OUT%\tests.log"
type "%OUT%\hardware-tests.log"
popd
exit /b 0
:failed
echo FAIL: inspect %OUT% logs
popd
exit /b 1
