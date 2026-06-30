#!/bin/sh
# place_spipe.sh  (script 2)
# Set up the private .spipe overlay in the CURRENT project. Private content
# (wiki, configs, secrets) lives ONLY inside .spipe and is never referenced
# from outside it. This script creates NO secrets.
#
# Modes:
#   embed     .spipe added as a git submodule of this project
#             (parent tracks a gitlink + the private url in .gitmodules)
#   generate  .spipe cloned into ./.spipe and gitignored
#             (parent has NO reference to the private repo at all)
set -eu

CORE_MODE=
case "${1:-}" in
  --vendor|--nested) CORE_MODE="$1"; shift ;;
esac
MODE="${1:-}"
PRIVATE_URL="${2:-}"
CORE_URL="${3:-https://github.com/ormastes/simple.git}"
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

usage() {
  echo "usage: place_spipe.sh [--vendor|--nested] <embed|generate> <private-spipe-repo-url> [core-url]"
  echo "  embed     .spipe added as a submodule of this project"
  echo "  generate  .spipe cloned into ./.spipe and gitignored (no outside link)"
  echo "  --vendor  core/ committed snapshot, pull-only for all clones (default)"
  echo "  --nested  core/ live clone, gitignored, pull with 'git -C core pull'"
  exit 1
}
[ -n "$MODE" ] && [ -n "$PRIVATE_URL" ] || usage
[ -e .spipe ] && { echo "error: .spipe already exists"; exit 1; }
git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "error: run inside a git project"; exit 1; }

case "$MODE" in
  embed)
    git submodule add "$PRIVATE_URL" .spipe
    ;;
  generate)
    git clone "$PRIVATE_URL" .spipe
    # keep the private overlay out of the parent repo entirely
    grep -qxF '/.spipe/' .gitignore 2>/dev/null || printf '/.spipe/\n' >> .gitignore
    ;;
  *) usage ;;
esac

# wire the pull-only core INSIDE .spipe (forward the core mode flag)
( cd .spipe && sh "$HERE/add_spipe_core.sh" $CORE_MODE "$CORE_URL" )

echo "done: .spipe ($MODE) with read-only core at .spipe/core"
