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

for b in simple_mcp_server simple_lsp_mcp_server t32_mcp_server t32_lsp_mcp_server; do
  if [ -x "release/${PLATFORM_TRIPLE}/${b}" ]; then
    ln -sf "release/${PLATFORM_TRIPLE}/${b}" "${b}"
  fi
done

echo "setup: bin/simple -> release/${PLATFORM_TRIPLE}/simple"
