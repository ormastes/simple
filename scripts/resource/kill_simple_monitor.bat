@echo off
REM Monitor CPU and memory usage every 2 seconds (Windows).
REM When free CPU AND free memory BOTH drop below the threshold (default 90%%),
REM kill all processes whose name contains "simple", except this script.
REM
REM NOTE: This file CANNOT be .shs (Simple Shell Script) because the Simple
REM runtime/interpreter must be running to execute .shs files — but this script's
REM purpose is to KILL Simple processes when resources are exhausted. If this were
REM .shs, it would need a Simple process to run, which would then kill itself.
REM It must be a plain .bat to remain independent of the Simple runtime.
REM
REM Compatible with: cmd.exe, MinGW/MSYS2 (via cmd /c), MSVC Developer Command Prompt
REM Uses: wmic (primary), PowerShell (fallback)
REM
REM Usage: kill_simple_monitor.bat [THRESHOLD]   (default: 90)
REM Runs in background automatically via start /b.

setlocal enabledelayedexpansion

set "THRESHOLD=%~1"
if "%THRESHOLD%"=="" set "THRESHOLD=90"
set "INTERVAL=2"
set "SCRIPT_NAME=kill_simple_monitor"

REM Write PID file so ensure_kill_monitor_running can detect us
set "PIDFILE=%TEMP%\kill_simple_monitor.pid"

REM Auto-background: re-launch detached if not already backgrounded
if not defined _MONITOR_BG (
    set "LOG=%TEMP%\%SCRIPT_NAME%_%RANDOM%.log"
    echo [monitor] Running in background ^(log: !LOG!^)
    start "" /b cmd /c "set "_MONITOR_BG=1" && "%~f0" %THRESHOLD%" > "!LOG!" 2>&1
    exit /b 0
)

REM Write PID file (presence = running)
echo running > "%PIDFILE%"

echo [monitor] Starting simple-process monitor (OS: Windows, free threshold: %THRESHOLD%%%, interval: %INTERVAL%s)

:loop

REM ===== Free memory % =====
set "mem_free_pct=100"
set "mem_avail_mb=0"
set "mem_total_mb=0"
set "free_kb="
set "total_kb="

REM Try wmic with /value format — parse "Key=Value" lines
for /f "tokens=2 delims==" %%b in ('wmic OS get FreePhysicalMemory /value 2^>nul ^| find "="') do (
    set "free_kb=%%b"
)
for /f "tokens=2 delims==" %%b in ('wmic OS get TotalVisibleMemorySize /value 2^>nul ^| find "="') do (
    set "total_kb=%%b"
)

REM Strip trailing whitespace/CR from wmic
if defined free_kb set "free_kb=!free_kb: =!"
if defined total_kb set "total_kb=!total_kb: =!"

REM Fallback: PowerShell if wmic failed
if not defined free_kb (
    for /f "usebackq delims=" %%v in (`powershell.exe -NoProfile -Command "(Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory" 2^>nul`) do (
        set "free_kb=%%v"
        set "free_kb=!free_kb: =!"
    )
)
if not defined total_kb (
    for /f "usebackq delims=" %%v in (`powershell.exe -NoProfile -Command "(Get-CimInstance Win32_OperatingSystem).TotalVisibleMemorySize" 2^>nul`) do (
        set "total_kb=%%v"
        set "total_kb=!total_kb: =!"
    )
)

if defined free_kb if defined total_kb (
    set /a "mem_avail_mb=free_kb / 1024" 2>nul
    set /a "mem_total_mb=total_kb / 1024" 2>nul
    if !mem_total_mb! gtr 0 (
        set /a "mem_free_pct=free_kb * 100 / total_kb" 2>nul
    )
)

REM ===== Free CPU % =====
set "cpu_free_pct=100"
set "cpu_load="

for /f "tokens=2 delims==" %%b in ('wmic cpu get LoadPercentage /value 2^>nul ^| find "="') do (
    set "cpu_load=%%b"
)
if defined cpu_load set "cpu_load=!cpu_load: =!"

REM Fallback: PowerShell
if not defined cpu_load (
    for /f "usebackq delims=" %%v in (`powershell.exe -NoProfile -Command "(Get-CimInstance Win32_Processor).LoadPercentage" 2^>nul`) do (
        set "cpu_load=%%v"
        set "cpu_load=!cpu_load: =!"
    )
)

if defined cpu_load (
    set /a "cpu_free_pct=100 - cpu_load" 2>nul
)

echo [monitor] free CPU: !cpu_free_pct!%% ^| free MEM: !mem_free_pct!%% (!mem_avail_mb!/!mem_total_mb! MB)

REM ===== Check thresholds (BOTH must be exceeded) =====
set "do_kill=0"
if !cpu_free_pct! lss %THRESHOLD% (
    if !mem_free_pct! lss %THRESHOLD% (
        set "do_kill=1"
    )
)

if "!do_kill!"=="1" (
    echo [monitor] THRESHOLD EXCEEDED: free CPU !cpu_free_pct!%% ^< %THRESHOLD%%% AND free MEM !mem_free_pct!%% ^< %THRESHOLD%%%
    REM List "simple" processes, filter out this script, kill remaining
    tasklist /fo csv /nh 2>nul | findstr /i "simple" | findstr /v /i "%SCRIPT_NAME%" > "%TEMP%\simple_procs.tmp" 2>nul
    set "found=0"
    for /f "tokens=1,2 delims=," %%p in (%TEMP%\simple_procs.tmp) do (
        set "pname=%%~p"
        set "ppid=%%~q"
        echo [monitor]   taskkill !ppid! ^(!pname!^)
        taskkill /pid !ppid! /f >nul 2>&1
        set "found=1"
    )
    del "%TEMP%\simple_procs.tmp" 2>nul
    if "!found!"=="0" (
        echo [monitor] No 'simple' processes found to kill.
    )
)

timeout /t %INTERVAL% /nobreak >nul 2>&1
goto loop
