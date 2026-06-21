@echo off
REM add_spipe_core.bat  (script 1, Windows) — see add_spipe_core.sh for details.
REM Wire the public CORE project as a READ-ONLY submodule at .\core and create
REM the overlay doc/wiki skeleton. Run from INSIDE the .spipe private repo.
setlocal
set "CORE_URL=%~1"
set "CORE_REF=%~2"
if "%CORE_URL%"=="" set "CORE_URL=https://github.com/ormastes/simple.git"
if "%CORE_REF%"=="" set "CORE_REF=main"

git rev-parse --is-inside-work-tree >nul 2>&1 || ( echo error: run inside the .spipe git repo & exit /b 1 )
if exist "core" ( echo error: .\core already exists & exit /b 1 )

git submodule add --name core -b "%CORE_REF%" "%CORE_URL%" core || exit /b 1
git config -f .gitmodules submodule.core.update none
git config -f .gitmodules submodule.core.ignore all
git add .gitmodules core

REM overlay doc/wiki skeleton (read order: 00 -> 10 -> 20)
for %%D in (00_llm_process 10_llm_wiki 20_raw_doc) do if not exist "%%D" mkdir "%%D"
if not exist "00_llm_process\README.md" echo # LLM process>> 00_llm_process\README.md & echo.>> 00_llm_process\README.md & echo LLM pipeline/process definitions. References ../10_llm_wiki for curated knowledge.>> 00_llm_process\README.md
if not exist "10_llm_wiki\README.md" echo # LLM wiki>> 10_llm_wiki\README.md & echo.>> 10_llm_wiki\README.md & echo Curated LLM wiki distilled from ../20_raw_doc. Public-safe only - no secrets.>> 10_llm_wiki\README.md
if not exist "20_raw_doc\README.md" echo # Raw docs>> 20_raw_doc\README.md & echo.>> 20_raw_doc\README.md & echo Raw source documents - inputs the wiki is distilled from.>> 20_raw_doc\README.md
git add 00_llm_process 10_llm_wiki 20_raw_doc

echo core wired read-only at .spipe/core (%CORE_URL%@%CORE_REF%)
echo doc/wiki dirs ready: 00_llm_process/ 10_llm_wiki/ 20_raw_doc/
exit /b 0
