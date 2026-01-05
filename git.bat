@echo off
REM Git-to-JJ wrapper - Redirects git commands to jj equivalents
REM This helps LLMs use jj instead of git

set cmd=%1
shift

echo NOTE: This project uses jj (Jujutsu) instead of git.
echo       Please use 'jj' commands directly next time.
echo       Translating 'git %cmd%' -^> jj equivalent...
echo.

if "%cmd%"=="status" (
    jj status %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="diff" (
    jj diff %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="log" (
    jj log %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="add" (
    echo Note: jj auto-tracks files, no need to add
    jj status
    goto :eof
)
if "%cmd%"=="commit" (
    if "%1"=="-m" (
        shift
        jj commit -m %1 %2 %3 %4
    ) else (
        jj commit %1 %2 %3 %4 %5
    )
    goto :eof
)
if "%cmd%"=="push" (
    jj git push %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="pull" (
    jj git fetch %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="fetch" (
    jj git fetch %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="checkout" (
    jj edit %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="branch" (
    jj bookmark %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="stash" (
    echo Note: jj doesn't need stash - changes are always preserved
    jj status
    goto :eof
)
if "%cmd%"=="init" (
    jj git init %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="clone" (
    jj git clone %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="show" (
    jj show %1 %2 %3 %4 %5
    goto :eof
)
if "%cmd%"=="reset" (
    echo Note: use 'jj restore' or 'jj abandon' instead of git reset
    jj status
    goto :eof
)

echo Unknown git command: %cmd%
echo Use jj directly. Common commands:
echo   jj status, jj diff, jj log, jj commit, jj describe
echo   jj git push, jj git fetch, jj edit, jj new
exit /b 1
