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

for b in t32_mcp_server t32_lsp_mcp_server; do
  if [ -x "release/${PLATFORM_TRIPLE}/${b}" ]; then
    ln -sf "release/${PLATFORM_TRIPLE}/${b}" "${b}"
  fi
done

if [ -x "release/${PLATFORM_TRIPLE}/simple_mcp_server" ] || [ -x "release/linux-x86_64/simple_mcp_server" ]; then
  rm -f simple_mcp_server
  cat > simple_mcp_server <<'EOF'
#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
platform_dir="${SIMPLE_PLATFORM_TRIPLE:-x86_64-unknown-linux-gnu}"

if [ "${platform_dir}" = "x86_64-unknown-linux-gnu" ] && [ -x "${script_dir}/release/linux-x86_64/simple_mcp_server" ]; then
  native="${script_dir}/release/linux-x86_64/simple_mcp_server"
else
  native="${script_dir}/release/${platform_dir}/simple_mcp_server"
fi

if [ ! -x "${native}" ]; then
  for candidate in "${script_dir}"/release/*/simple_mcp_server; do
    if [ -x "${candidate}" ]; then
      native="${candidate}"
      break
    fi
  done
fi

if [ ! -x "${native}" ]; then
  printf '%s\n' "error: native simple_mcp_server not found under ${script_dir}/release" >&2
  exit 127
fi

tmp_input="${TMPDIR:-/tmp}/simple_mcp_server_input.$$"
cat > "${tmp_input}"

tmp_delegate="${TMPDIR:-/tmp}/simple_mcp_server_delegate.$$"
grep -v '"method":"initialized"' "${tmp_input}" > "${tmp_delegate}" || true
tmp_source_err="${TMPDIR:-/tmp}/simple_mcp_server_source_err.$$"

fallback_runtime=""
for candidate in \
  "${script_dir}/../src/compiler_rust/target/debug/simple" \
  "${script_dir}/../bin/release/simple" \
  "${script_dir}/simple"
do
  if [ -x "${candidate}" ]; then
    fallback_runtime="${candidate}"
    break
  fi
done

run_source_mcp() {
  if [ -z "${fallback_runtime}" ]; then
    return 127
  fi
  SIMPLE_LIB="${SIMPLE_LIB:-src}" "${fallback_runtime}" "${script_dir}/../src/app/mcp/main.spl" "$@" < "${tmp_delegate}" 2> "${tmp_source_err}"
}

needs_wm_text_mcp=false
if grep -q '"play_wm_text_' "${tmp_delegate}"; then
  needs_wm_text_mcp=true
fi

if [ "${needs_wm_text_mcp}" = "true" ]; then
  run_source_mcp "$@"
  status="$?"
  rm -f "${tmp_input}" "${tmp_delegate}" "${tmp_source_err}"
  exit "${status}"
fi

tmp_output="${TMPDIR:-/tmp}/simple_mcp_server_output.$$"
tmp_native_err="${TMPDIR:-/tmp}/simple_mcp_server_native_err.$$"
set +e
if command -v timeout >/dev/null 2>&1; then
  timeout 5 "${native}" "$@" < "${tmp_delegate}" > "${tmp_output}" 2> "${tmp_native_err}"
  status="$?"
  if [ "${status}" = "124" ]; then
    status=0
  fi
else
  "${native}" "$@" < "${tmp_delegate}" > "${tmp_output}" 2> "${tmp_native_err}"
  status="$?"
fi
set -e

if [ "${status}" != "0" ] || { grep -q '"method":"tools/list"' "${tmp_delegate}" && ! grep -q 'play_wm_text_status' "${tmp_output}"; }; then
  run_source_mcp "$@"
  status="$?"
else
  cat "${tmp_output}"
fi

rm -f "${tmp_input}" "${tmp_delegate}" "${tmp_output}" "${tmp_native_err}" "${tmp_source_err}"
exit "${status}"
EOF
  chmod +x simple_mcp_server
fi

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
