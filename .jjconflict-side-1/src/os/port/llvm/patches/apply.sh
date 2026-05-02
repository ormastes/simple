#!/usr/bin/env bash
# apply.sh — copy SimpleOS ToolChain scaffolding into an ormastes/llvm-project
# checkout. Does NOT apply the manual hunks (see the .patch.md files for
# those); this script only handles the "new file" portion of 0002.
#
# Usage:
#   apply.sh <path-to-llvm-project-checkout>
#
# Requires the checkout to be on the `simpleos` branch of
# git@github.com:ormastes/llvm-project.git. We do not enforce that here —
# the maintainer should double-check before running.

set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <llvm-project-src-dir>" >&2
  exit 64
fi

LLVM_SRC="$1"
PATCH_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FILES_DIR="${PATCH_DIR}/files"

if [[ ! -d "${LLVM_SRC}/clang/lib/Driver/ToolChains" ]]; then
  echo "error: ${LLVM_SRC} does not look like an llvm-project checkout" >&2
  echo "       (missing clang/lib/Driver/ToolChains)" >&2
  exit 66
fi

# Confirm branch (soft check — warn only).
if command -v git >/dev/null 2>&1; then
  BRANCH="$(git -C "${LLVM_SRC}" rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)"
  if [[ "${BRANCH}" != "simpleos" ]]; then
    echo "warning: checkout is on branch '${BRANCH}', expected 'simpleos'" >&2
  fi
fi

DEST_TOOLCHAINS="${LLVM_SRC}/clang/lib/Driver/ToolChains"

echo "[apply.sh] copying SimpleOS.h  -> ${DEST_TOOLCHAINS}/SimpleOS.h"
install -m 0644 "${FILES_DIR}/SimpleOS.h"   "${DEST_TOOLCHAINS}/SimpleOS.h"

echo "[apply.sh] copying SimpleOS.cpp -> ${DEST_TOOLCHAINS}/SimpleOS.cpp"
install -m 0644 "${FILES_DIR}/SimpleOS.cpp" "${DEST_TOOLCHAINS}/SimpleOS.cpp"

cat <<'EOF'

[apply.sh] file copies complete.

Manual follow-ups still required — the maintainer MUST edit these by hand:

  1. llvm/include/llvm/TargetParser/Triple.h
     - Add `SimpleOS` to the `OSType` enum (before `LastOSType`).
     See: 0001-triple-simpleos.patch.md

  2. llvm/lib/TargetParser/Triple.cpp
     - Add case to `getOSTypeName` returning "simpleos".
     - Add `.StartsWith("simpleos", Triple::SimpleOS)` to `parseOS`.
     See: 0001-triple-simpleos.patch.md

  3. clang/lib/Driver/CMakeLists.txt
     - Add `ToolChains/SimpleOS.cpp` to the clangDriver SRCS list.

  4. clang/lib/Driver/Driver.cpp
     - `#include "ToolChains/SimpleOS.h"`
     - Add `case llvm::Triple::SimpleOS:` in `Driver::getToolChain`.
     See: 0002-clang-toolchain-simpleos.patch.md

  5. clang/CMakeLists.txt
     - Add `option(CLANG_SIMPLEOS_EMBED_LLD ... OFF)`.

  6. clang/tools/driver/CMakeLists.txt
     - Conditionally link lldCommon + lldELF and define
       CLANG_SIMPLEOS_EMBED_LLD.

  7. clang/tools/driver/driver.cpp
     - Apply the hunk shown in files/driver_embed_lld_hunk.cpp.
     See: 0003-embed-lld-in-clang-driver.patch.md

After all edits, rebuild with:
  cmake -G Ninja -S llvm -B build -DLLVM_ENABLE_PROJECTS='clang;lld' ...
  ninja -C build clang lld

EOF
