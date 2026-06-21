@echo off
REM place_spipe.bat  (script 2, Windows) — see place_spipe.sh for details.
setlocal
set "HERE=%~dp0"
set "MODE=%~1"
set "PRIVATE_URL=%~2"
set "CORE_URL=%~3"
if "%CORE_URL%"=="" set "CORE_URL=https://github.com/ormastes/simple.git"

if "%MODE%"=="" goto usage
if "%PRIVATE_URL%"=="" goto usage
if exist ".spipe" ( echo error: .spipe already exists & exit /b 1 )
git rev-parse --is-inside-work-tree >nul 2>&1 || ( echo error: run inside a git project & exit /b 1 )

if /i "%MODE%"=="embed" (
  git submodule add "%PRIVATE_URL%" .spipe || exit /b 1
) else if /i "%MODE%"=="generate" (
  git clone "%PRIVATE_URL%" .spipe || exit /b 1
  findstr /x /c:"/.spipe/" .gitignore >nul 2>&1 || echo /.spipe/>> .gitignore
) else (
  goto usage
)

REM wire read-only core + doc/wiki skeleton inside .spipe (submodule-of-submodule)
pushd .spipe
call "%HERE%add_spipe_core.bat" "%CORE_URL%" || ( popd & exit /b 1 )
popd

echo done: .spipe (%MODE%) with read-only core at .spipe/core
exit /b 0

:usage
echo usage: place_spipe.bat ^<embed^|generate^> ^<private-spipe-repo-url^> [core-url]
echo   embed     .spipe added as a submodule of this project
echo   generate  .spipe cloned into .spipe and gitignored (no outside link)
exit /b 1
