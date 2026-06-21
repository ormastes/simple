#!/bin/sh
# add_spipe_core.sh  (script 1)
# Vendor the public CORE project into ./core as a real, COMMITTED copy.
# Run from INSIDE the .spipe private repo. core/ becomes plain files in THIS
# repo — a normal `git clone` of the private repo gets everything, no submodule.
#
# Pull-only by construction: core/ is a stripped clone (its .git is removed), so
# there is no link back to the public repo and nothing can be pushed upstream.
# To PULL changes later, just re-run this script: it re-clones the latest
# snapshot and recommits. Needs nothing beyond core git (no git-subtree).
set -eu

CORE_URL="${1:-https://github.com/ormastes/simple.git}"
CORE_REF="${2:-main}"

git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "error: run inside the .spipe git repo"; exit 1; }

# (re)vendor: replace core/ with the latest upstream snapshot, then strip its .git
rm -rf core
git clone --depth 1 --branch "$CORE_REF" "$CORE_URL" core
rm -rf core/.git
git add -A core
git commit -q -m "vendor: core @ $CORE_REF ($CORE_URL)" || echo "core already up to date"

# overlay doc/wiki skeleton (read order: 00 -> 10 -> 20). Created if missing.
mkdir -p 00_llm_process 10_llm_wiki 20_raw_doc
[ -e 00_llm_process/README.md ] || printf '# LLM process\n\nLLM pipeline/process definitions. References ../10_llm_wiki for curated knowledge.\n' > 00_llm_process/README.md
[ -e 10_llm_wiki/README.md ]    || printf '# LLM wiki\n\nCurated LLM wiki distilled from ../20_raw_doc. Public-safe only — no secrets.\n' > 10_llm_wiki/README.md
[ -e 20_raw_doc/README.md ]     || printf '# Raw docs\n\nRaw source documents — inputs the wiki is distilled from.\n' > 20_raw_doc/README.md
git add 00_llm_process 10_llm_wiki 20_raw_doc
git commit -q -m "chore(spipe): overlay doc/wiki skeleton (00_llm_process 10_llm_wiki 20_raw_doc)" || true

echo "core vendored at .spipe/core ($CORE_URL@$CORE_REF) — committed copy, pull-only"
echo "pull updates later: re-run this script (re-clones latest snapshot, recommits)"
echo "doc/wiki dirs ready: 00_llm_process/ 10_llm_wiki/ 20_raw_doc/"
