#!/bin/sh
set -eu

# Create bin/simple (and MCP server) symlinks pointing at the
# platform-specific release binaries.  Called by bootstrap-from-scratch.sh
# after --deploy, or manually after a fresh clone.

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
. "${repo_root}/scripts/platform-detect.sh"

release_dir="${repo_root}/bin/release/${PLATFORM_TRIPLE}"

if [ ! -x "${release_dir}/simple" ]; then
  echo "setup: ${release_dir}/simple not found — run bootstrap first" >&2
  exit 0
fi

cd "${repo_root}/bin"

ln -sf "release/${PLATFORM_TRIPLE}/simple" simple

for b in simple_mcp_server t32_mcp_server t32_lsp_mcp_server; do
  if [ -x "release/${PLATFORM_TRIPLE}/${b}" ]; then
    ln -sf "release/${PLATFORM_TRIPLE}/${b}" "${b}"
  fi
done

if [ -x "release/${PLATFORM_TRIPLE}/simple_lsp_mcp_server" ]; then
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
native="${script_dir}/release/${platform_dir}/simple_lsp_mcp_server"

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
