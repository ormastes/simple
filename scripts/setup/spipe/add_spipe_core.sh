#!/bin/sh
# add_spipe_core.sh  (script 1)
# Wire the public CORE project as a READ-ONLY submodule at ./core.
# Run from INSIDE the .spipe private repo. Builds the submodule-of-submodule:
#   USER_PROJECT/.spipe/core  ->  this public project (read-only)
#
# ponytail: git has no "read-only submodule" flag. Read-only == public https url
# (fetch works, push needs creds the user lacks) + update=none + ignore=all
# (never auto-updated, local edits never show as changes to commit). Upgrade path:
# pull a new ref explicitly when you want it.
set -eu

CORE_URL="${1:-https://github.com/ormastes/simple.git}"
CORE_REF="${2:-main}"

git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "error: run inside the .spipe git repo"; exit 1; }
[ -e core ] && { echo "error: ./core already exists"; exit 1; }

git submodule add --name core -b "$CORE_REF" "$CORE_URL" core
git config -f .gitmodules submodule.core.update none
git config -f .gitmodules submodule.core.ignore  all
git add .gitmodules core

# overlay doc/wiki skeleton (read order: 00 -> 10 -> 20). Created if missing.
mkdir -p 00_llm_process 10_llm_wiki 20_raw_doc
[ -e 00_llm_process/README.md ] || printf '# LLM process\n\nLLM pipeline/process definitions. References ../10_llm_wiki for curated knowledge.\n' > 00_llm_process/README.md
[ -e 10_llm_wiki/README.md ]    || printf '# LLM wiki\n\nCurated LLM wiki distilled from ../20_raw_doc. Public-safe only — no secrets.\n' > 10_llm_wiki/README.md
[ -e 20_raw_doc/README.md ]     || printf '# Raw docs\n\nRaw source documents — inputs the wiki is distilled from.\n' > 20_raw_doc/README.md
git add 00_llm_process 10_llm_wiki 20_raw_doc

echo "core wired read-only at .spipe/core ($CORE_URL@$CORE_REF)"
echo "doc/wiki dirs ready: 00_llm_process/ 10_llm_wiki/ 20_raw_doc/"
echo "pull updates explicitly:  git -C core fetch && git -C core checkout <tag-or-sha>"
