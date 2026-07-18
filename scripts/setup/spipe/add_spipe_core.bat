@echo off
REM add_spipe_core.bat  (script 1, Windows) — see add_spipe_core.sh for details.
REM Place the public CORE project at .\core inside the .spipe private repo,
REM pull-only. Run from INSIDE the .spipe private repo. Modes:
REM   --vendor  (default) shallow-clone, strip .git, COMMIT the snapshot; no
REM             upstream link, pull-only for every clone. Update: re-run.
REM   --nested  live clone gitignored (/core/); pull with `git -C core pull`,
REM             push disabled locally (per-machine only).
setlocal
set "MODE=vendor"
if /i "%~1"=="--vendor" ( set "MODE=vendor" & shift )
if /i "%~1"=="--nested" ( set "MODE=nested" & shift )

set "CORE_URL=%~1"
set "CORE_REF=%~2"
if "%CORE_URL%"=="" set "CORE_URL=https://github.com/ormastes/simple.git"
if "%CORE_REF%"=="" set "CORE_REF=main"

git rev-parse --is-inside-work-tree >nul 2>&1 || ( echo error: run inside the .spipe git repo & exit /b 1 )

if /i "%MODE%"=="vendor" (
  if exist "core" rmdir /s /q core
  git clone --depth 1 --branch "%CORE_REF%" "%CORE_URL%" core || exit /b 1
  if exist "core\.git" rmdir /s /q core\.git
  git add -A core
  git commit -q -m "vendor: core @ %CORE_REF% (%CORE_URL%)" || echo core already up to date
) else (
  if exist "core" ( echo error: .\core already exists & exit /b 1 )
  git clone --branch "%CORE_REF%" "%CORE_URL%" core || exit /b 1
  git -C core remote set-url --push origin DISABLED
  findstr /x /c:"/core/" .gitignore >nul 2>&1 || echo /core/>> .gitignore
  git add .gitignore
  git commit -q -m "chore(spipe): gitignore nested core/ live clone"
)

REM overlay doc/wiki skeleton (read order: 00 -> 10 -> 20)
for %%D in (00_llm_process 10_llm_wiki 20_raw_doc) do if not exist "%%D" mkdir "%%D"
if not exist "00_llm_process\README.md" echo # LLM process>> 00_llm_process\README.md & echo.>> 00_llm_process\README.md & echo LLM pipeline/process definitions. References ../10_llm_wiki for curated knowledge.>> 00_llm_process\README.md
if not exist "10_llm_wiki\README.md" echo # LLM wiki>> 10_llm_wiki\README.md & echo.>> 10_llm_wiki\README.md & echo Curated LLM wiki distilled from ../20_raw_doc. Public-safe only - no secrets.>> 10_llm_wiki\README.md
if not exist "20_raw_doc\README.md" echo # Raw docs>> 20_raw_doc\README.md & echo.>> 20_raw_doc\README.md & echo Raw source documents - inputs the wiki is distilled from.>> 20_raw_doc\README.md
git add 00_llm_process 10_llm_wiki 20_raw_doc
git commit -q -m "chore(spipe): overlay doc/wiki skeleton (00_llm_process 10_llm_wiki 20_raw_doc)"

echo core ready at .spipe/core (%MODE%, %CORE_URL%@%CORE_REF%) - pull-only
echo doc/wiki dirs ready: 00_llm_process/ 10_llm_wiki/ 20_raw_doc/
exit /b 0
