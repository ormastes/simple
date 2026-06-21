@echo off
REM add_spipe_core.bat  (script 1, Windows) — see add_spipe_core.sh for details.
REM Vendor the public CORE project into .\core as a real COMMITTED copy (a plain
REM clone of the private repo gets everything, no submodule). core/ is a stripped
REM clone (its .git removed) so there is no upstream link and nothing can be
REM pushed back. Re-run to PULL changes. Run from INSIDE the .spipe private repo.
setlocal
set "CORE_URL=%~1"
set "CORE_REF=%~2"
if "%CORE_URL%"=="" set "CORE_URL=https://github.com/ormastes/simple.git"
if "%CORE_REF%"=="" set "CORE_REF=main"

git rev-parse --is-inside-work-tree >nul 2>&1 || ( echo error: run inside the .spipe git repo & exit /b 1 )

REM (re)vendor: replace core/ with the latest upstream snapshot, then strip its .git
if exist "core" rmdir /s /q core
git clone --depth 1 --branch "%CORE_REF%" "%CORE_URL%" core || exit /b 1
if exist "core\.git" rmdir /s /q core\.git
git add -A core
git commit -q -m "vendor: core @ %CORE_REF% (%CORE_URL%)" || echo core already up to date

REM overlay doc/wiki skeleton (read order: 00 -> 10 -> 20)
for %%D in (00_llm_process 10_llm_wiki 20_raw_doc) do if not exist "%%D" mkdir "%%D"
if not exist "00_llm_process\README.md" echo # LLM process>> 00_llm_process\README.md & echo.>> 00_llm_process\README.md & echo LLM pipeline/process definitions. References ../10_llm_wiki for curated knowledge.>> 00_llm_process\README.md
if not exist "10_llm_wiki\README.md" echo # LLM wiki>> 10_llm_wiki\README.md & echo.>> 10_llm_wiki\README.md & echo Curated LLM wiki distilled from ../20_raw_doc. Public-safe only - no secrets.>> 10_llm_wiki\README.md
if not exist "20_raw_doc\README.md" echo # Raw docs>> 20_raw_doc\README.md & echo.>> 20_raw_doc\README.md & echo Raw source documents - inputs the wiki is distilled from.>> 20_raw_doc\README.md
git add 00_llm_process 10_llm_wiki 20_raw_doc
git commit -q -m "chore(spipe): overlay doc/wiki skeleton (00_llm_process 10_llm_wiki 20_raw_doc)"

echo core vendored at .spipe/core (%CORE_URL%@%CORE_REF%) - committed copy, pull-only
echo pull updates later: re-run this script (re-clones latest snapshot, recommits)
echo doc/wiki dirs ready: 00_llm_process/ 10_llm_wiki/ 20_raw_doc/
exit /b 0
