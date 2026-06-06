#!/bin/sh
set -eu

# Create bin/simple (and MCP server) symlinks pointing at the
# platform-specific release binaries.  Called by bootstrap-from-scratch.sh
# after --deploy, or manually after a fresh clone.

repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
. "${repo_root}/scripts/setup/platform-detect.sh"

# platform-detect emits the 3-part Rust triple (e.g. aarch64-apple-darwin), but
# release binaries live under the 4-part Simple-native triple (…-macho on macOS).
# Resolve PLATFORM_TRIPLE to whichever release dir actually exists.
if [ ! -x "${repo_root}/bin/release/${PLATFORM_TRIPLE}/simple" ]; then
  for cand in "${PLATFORM_TRIPLE}-macho" "${PLATFORM_ARCH}-apple-darwin-macho"; do
    if [ -x "${repo_root}/bin/release/${cand}/simple" ]; then
      PLATFORM_TRIPLE="${cand}"
      break
    fi
  done
fi

release_dir="${repo_root}/bin/release/${PLATFORM_TRIPLE}"

if [ ! -x "${release_dir}/simple" ]; then
  echo "setup: ${release_dir}/simple not found — run bootstrap first" >&2
  exit 0
fi

cd "${repo_root}/bin"

ln -sf "release/${PLATFORM_TRIPLE}/simple" simple

for b in t32_mcp_server t32_lsp_mcp_server; do
  if [ -x "release/${PLATFORM_TRIPLE}/${b}" ]; then
    ln -sf "release/${PLATFORM_TRIPLE}/${b}" "${b}"
  fi
done

rm -f simple_mcp_server
cat > simple_mcp_server <<'EOF'
#!/bin/sh
set -eu

case "${1:-}" in
  --version|-v)
    printf '%s\n' 'simple-mcp-server 4.0.0'
    exit 0
    ;;
  --help|-h)
    printf '%s\n' 'simple-mcp-server 4.0.0'
    printf '%s\n' 'Usage: simple_mcp_server'
    printf '%s\n' '       simple_mcp_server --version'
    exit 0
    ;;
esac

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root="${script_dir}/.."

runtime=""
for candidate in \
  "${script_dir}/release/x86_64-unknown-linux-gnu/simple" \
  "${script_dir}/release/linux-x86_64/simple" \
  "${script_dir}/simple" \
  "${repo_root}/bin/release/simple" \
  "${repo_root}/src/compiler_rust/target/release/simple" \
  "${repo_root}/src/compiler_rust/target/debug/simple"
do
  if [ -x "${candidate}" ]; then
    runtime="${candidate}"
    break
  fi
done

if [ -z "${runtime}" ]; then
  printf '%s\n' "error: simple runtime not found" >&2
  exit 127
fi

entry="${repo_root}/src/app/mcp/main.spl"
if [ ! -f "${entry}" ]; then
  printf '%s\n' "error: MCP entry point not found: ${entry}" >&2
  exit 127
fi

export SIMPLE_LIB="${SIMPLE_LIB:-${repo_root}/src}"
export SIMPLE_LOG="${SIMPLE_LOG:-error}"
export SIMPLE_TIMEOUT_SECONDS="${SIMPLE_TIMEOUT_SECONDS:-86400}"
export SIMPLE_MEMORY_LIMIT_MB="${SIMPLE_MEMORY_LIMIT_MB:-${SIMPLE_TEST_MEMORY_LIMIT_MB:-100}}"
export RUST_LOG="${RUST_LOG:-error}"

exec "${runtime}" "${entry}" "$@" 2>>"${repo_root}/.simple/logs/simple_mcp_stderr.log"
EOF
chmod +x simple_mcp_server

if [ -x "release/${PLATFORM_TRIPLE}/simple_lsp_mcp_server" ] || [ -x "release/linux-x86_64/simple_lsp_mcp_server" ]; then
  rm -f simple_lsp_mcp_server
  cat > simple_lsp_mcp_server <<'EOF'
#!/bin/sh
set -eu

case "${1:-}" in
  --version|-v)
    printf '%s\n' 'simple-lsp-mcp-server 0.9.8'
    exit 0
    ;;
  --help|-h)
    printf '%s\n' 'simple-lsp-mcp-server 0.9.8'
    printf '%s\n' 'Usage: simple_lsp_mcp_server'
    printf '%s\n' '       simple_lsp_mcp_server --version'
    exit 0
    ;;
esac

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
platform_dir="${SIMPLE_PLATFORM_TRIPLE:-x86_64-unknown-linux-gnu}"

if [ "${platform_dir}" = "x86_64-unknown-linux-gnu" ] && [ -x "${script_dir}/release/linux-x86_64/simple_lsp_mcp_server" ]; then
  native="${script_dir}/release/linux-x86_64/simple_lsp_mcp_server"
else
  native="${script_dir}/release/${platform_dir}/simple_lsp_mcp_server"
fi

if [ ! -x "${native}" ]; then
  for candidate in "${script_dir}"/release/*/simple_lsp_mcp_server; do
    if [ -x "${candidate}" ]; then
      native="${candidate}"
      break
    fi
  done
fi

if [ ! -x "${native}" ]; then
  printf '%s\n' "error: native simple_lsp_mcp_server not found under ${script_dir}/release" >&2
  exit 127
fi

exec "${native}" "$@"
EOF
  chmod +x simple_lsp_mcp_server
fi

echo "setup: bin/simple -> release/${PLATFORM_TRIPLE}/simple"
