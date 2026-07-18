#!/bin/sh
# add_spipe_core.sh  (script 1)
# Place the public CORE project at ./core inside the .spipe private repo,
# pull-only. Run from INSIDE the .spipe private repo. Two modes:
#
#   --vendor  (default) shallow-clone, strip .git, COMMIT the snapshot. core/ is
#             real files that travel inside .spipe clones; the committed tree has
#             no upstream remote, so pushing to the public repo is impossible by
#             construction for EVERY clone. Update: re-run this script.
#   --nested  live clone kept OUT of the repo (gitignored /core/). Pulls with
#             `git -C core pull`; push disabled locally. That push-block is
#             per-machine config and does NOT travel — each consumer reclones.
#
# Needs only core git (no git-subtree).
set -eu

MODE=vendor
case "${1:-}" in
  --vendor) MODE=vendor; shift ;;
  --nested) MODE=nested; shift ;;
  --*) echo "error: unknown flag $1 (use --vendor or --nested)"; exit 1 ;;
esac

CORE_URL="${1:-https://github.com/ormastes/simple.git}"
CORE_REF="${2:-main}"

git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "error: run inside the .spipe git repo"; exit 1; }

if [ "$MODE" = vendor ]; then
  # (re)vendor: replace core/ with the latest upstream snapshot, then strip its .git
  rm -rf core
  git clone --depth 1 --branch "$CORE_REF" "$CORE_URL" core
  rm -rf core/.git
  git add -A core
  git commit -q -m "vendor: core @ $CORE_REF ($CORE_URL)" || echo "core already up to date"
else
  # nested live clone: kept out of the repo, pull-only on this machine
  [ -e core ] && { echo "error: ./core already exists"; exit 1; }
  git clone --branch "$CORE_REF" "$CORE_URL" core
  git -C core remote set-url --push origin DISABLED
  grep -qxF '/core/' .gitignore 2>/dev/null || printf '/core/\n' >> .gitignore
  git add .gitignore
  git commit -q -m "chore(spipe): gitignore nested core/ live clone" || true
fi

# overlay doc/wiki skeleton (read order: 00 -> 10 -> 20). Created if missing.
mkdir -p 00_llm_process 10_llm_wiki 20_raw_doc
[ -e 00_llm_process/README.md ] || printf '# LLM process\n\nLLM pipeline/process definitions. References ../10_llm_wiki for curated knowledge.\n' > 00_llm_process/README.md
[ -e 10_llm_wiki/README.md ]    || printf '# LLM wiki\n\nCurated LLM wiki distilled from ../20_raw_doc. Public-safe only — no secrets.\n' > 10_llm_wiki/README.md
[ -e 20_raw_doc/README.md ]     || printf '# Raw docs\n\nRaw source documents — inputs the wiki is distilled from.\n' > 20_raw_doc/README.md
git add 00_llm_process 10_llm_wiki 20_raw_doc
git commit -q -m "chore(spipe): overlay doc/wiki skeleton (00_llm_process 10_llm_wiki 20_raw_doc)" || true

echo "core ready at .spipe/core ($MODE, $CORE_URL@$CORE_REF) — pull-only"
if [ "$MODE" = vendor ]; then
  echo "pull updates: re-run this script (re-clones latest snapshot, recommits)"
else
  echo "pull updates: git -C core pull"
fi
echo "doc/wiki dirs ready: 00_llm_process/ 10_llm_wiki/ 20_raw_doc/"
