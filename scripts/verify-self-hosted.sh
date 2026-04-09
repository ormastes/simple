#!/bin/sh
# Verify that bin/ links point to self-hosted binaries, NOT Rust bootstrap artifacts.
#
# Usage:
#   scripts/verify-self-hosted.sh           # check and report
#   scripts/verify-self-hosted.sh --fix     # also fix stale Rust symlinks via setup.sh
#
# Exit codes:
#   0 = all links are self-hosted (or no links exist)
#   1 = one or more links point to Rust bootstrap
#   2 = no runtime found at all

set -eu

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

fix_mode=0
if [ "${1:-}" = "--fix" ]; then
  fix_mode=1
fi

# Returns 0 if file is (or transitively resolves to) a Rust build artifact.
is_rust_artifact() {
  local target="$1"
  local resolved="$target"
  while [ -L "$resolved" ]; do
    local link
    link="$(readlink "$resolved")"
    case "$link" in
      /*) resolved="$link" ;;
      *)  resolved="$(dirname "$resolved")/$link" ;;
    esac
  done
  case "$resolved" in
    */src/compiler_rust/target/*) return 0 ;;
    *) return 1 ;;
  esac
}

PASS=0
FAIL=0
WARN=0

check_link() {
  local label="$1" path="$2"

  if [ ! -e "$path" ] && [ ! -L "$path" ]; then
    echo "  SKIP: $label — does not exist"
    return
  fi

  if [ -L "$path" ]; then
    local target
    target="$(readlink "$path")"
    if is_rust_artifact "$path"; then
      FAIL=$((FAIL + 1))
      echo "  FAIL: $label → $target (Rust bootstrap artifact!)"
    else
      PASS=$((PASS + 1))
      echo "  PASS: $label → $target (self-hosted)"
    fi
  elif [ -f "$path" ]; then
    # Real binary file — check it's not inside compiler_rust/target/
    local real
    real="$(realpath "$path" 2>/dev/null || echo "$path")"
    case "$real" in
      */src/compiler_rust/target/*)
        FAIL=$((FAIL + 1))
        echo "  FAIL: $label = $real (Rust bootstrap artifact!)"
        ;;
      *)
        PASS=$((PASS + 1))
        echo "  PASS: $label (self-hosted binary)"
        ;;
    esac
  fi
}

echo "=== Self-Hosted Binary Verification ==="
echo ""
echo "Checking bin/ links:"

check_link "bin/simple" "${REPO_ROOT}/bin/simple"
check_link "bin/simple.exe" "${REPO_ROOT}/bin/simple.exe"
check_link "bin/simple_mcp_server" "${REPO_ROOT}/bin/simple_mcp_server"
check_link "bin/simple_lsp_mcp_server" "${REPO_ROOT}/bin/simple_lsp_mcp_server"
check_link "bin/t32_mcp_server" "${REPO_ROOT}/bin/t32_mcp_server"
check_link "bin/t32_lsp_mcp_server" "${REPO_ROOT}/bin/t32_lsp_mcp_server"
check_link "bin/simple_mcp_server.cmd" "${REPO_ROOT}/bin/simple_mcp_server.cmd"
check_link "bin/simple_lsp_mcp_server.cmd" "${REPO_ROOT}/bin/simple_lsp_mcp_server.cmd"
check_link "bin/t32_mcp_server.cmd" "${REPO_ROOT}/bin/t32_mcp_server.cmd"
check_link "bin/t32_lsp_mcp_server.cmd" "${REPO_ROOT}/bin/t32_lsp_mcp_server.cmd"

echo ""
echo "Checking bin/release/ links:"

# Check platform-specific subdirs
for subdir in "${REPO_ROOT}/bin/release"/*/; do
  if [ -d "$subdir" ]; then
    dirname="$(basename "$subdir")"
    for exe in simple simple.exe simple_mcp_server simple_lsp_mcp_server t32_mcp_server t32_lsp_mcp_server simple_mcp_server.cmd simple_lsp_mcp_server.cmd t32_mcp_server.cmd t32_lsp_mcp_server.cmd; do
      if [ -e "${subdir}${exe}" ] || [ -L "${subdir}${exe}" ]; then
        check_link "bin/release/${dirname}/${exe}" "${subdir}${exe}"
      fi
    done
  fi
done

# Check flat bin/release/simple
if [ -e "${REPO_ROOT}/bin/release/simple" ] || [ -L "${REPO_ROOT}/bin/release/simple" ]; then
  check_link "bin/release/simple" "${REPO_ROOT}/bin/release/simple"
fi

echo ""
echo "=== Results: $PASS self-hosted, $FAIL Rust-linked ==="

if [ "$FAIL" -gt 0 ]; then
  echo ""
  echo "WARNING: $FAIL link(s) point to Rust bootstrap artifacts."
  echo "Run 'scripts/bootstrap/bootstrap-from-scratch.sh' to build self-hosted binary."
  echo "Then run 'scripts/setup.sh' to fix symlinks."

  if [ "$fix_mode" -eq 1 ]; then
    echo ""
    echo "--- Attempting fix via scripts/setup.sh ---"
    sh "${REPO_ROOT}/scripts/setup.sh"
    echo ""
    echo "Re-checking after fix..."
    # Re-run checks
    PASS=0
    FAIL=0
    check_link "bin/simple" "${REPO_ROOT}/bin/simple"
    check_link "bin/simple_mcp_server" "${REPO_ROOT}/bin/simple_mcp_server"
    check_link "bin/simple_lsp_mcp_server" "${REPO_ROOT}/bin/simple_lsp_mcp_server"
    for subdir in "${REPO_ROOT}/bin/release"/*/; do
      if [ -d "$subdir" ]; then
        dirname="$(basename "$subdir")"
        for exe in simple simple.exe simple_mcp_server simple_lsp_mcp_server t32_mcp_server t32_lsp_mcp_server simple_mcp_server.cmd simple_lsp_mcp_server.cmd t32_mcp_server.cmd t32_lsp_mcp_server.cmd; do
          if [ -e "${subdir}${exe}" ] || [ -L "${subdir}${exe}" ]; then
            check_link "bin/release/${dirname}/${exe}" "${subdir}${exe}"
          fi
        done
      fi
    done
    echo ""
    if [ "$FAIL" -gt 0 ]; then
      echo "Still $FAIL Rust-linked after fix. Bootstrap required."
      exit 1
    else
      echo "All links now self-hosted."
      exit 0
    fi
  fi

  exit 1
fi

exit 0
