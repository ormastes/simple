#!/bin/sh
# Smoke-test the packed MCP npm packages in an isolated install.
# This catches stale bootstrap/runtime bundles that only fail after npm install.

set -eu

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/simple-mcp-smoke.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

info() { printf '[INFO] %s\n' "$1"; }
fail() { printf '[FAIL] %s\n' "$1" >&2; }

build_msg() {
    body="$1"
    len="$(printf '%s' "$body" | wc -c | tr -d ' ')"
    printf 'Content-Length: %s\r\n\r\n%s' "$len" "$body"
}

inspect_failure() {
    pkg_name="$1"
    pkg_root="$2"
    runtime="$(find "$pkg_root/native" -path '*/src/compiler_rust/bin/release/simple' -type f | head -n 1 || true)"
    entry="$(find "$pkg_root/native" \( -path '*/src/app/mcp/main.spl' -o -path '*/src/app/simple_lsp_mcp/main.spl' \) | head -n 1 || true)"

    printf '\n[DEBUG] %s package.json runtimeVersion=%s\n' \
        "$pkg_name" \
        "$(sed -n 's/.*"runtimeVersion": *"\([^"]*\)".*/\1/p' "$pkg_root/package.json" | head -n 1)"

    if [ -n "$runtime" ]; then
        printf '[DEBUG] %s runtime=%s\n' "$pkg_name" "$runtime"
        "$runtime" --version 2>&1 | sed 's/^/[DEBUG] runtime-version /'
    fi

    if [ -n "$entry" ]; then
        printf '[DEBUG] %s entry=%s\n' "$pkg_name" "$entry"
        sed -n '1,3p' "$entry" | sed 's/^/[DEBUG] entry-head /'
    fi
}

probe_command() {
    label="$1"
    cmd="$2"
    body="$3"
    expect="$4"

    out_file="$TMP_DIR/${label}.out"
    err_file="$TMP_DIR/${label}.err"

    build_msg "$body" | timeout 12s "$cmd" >"$out_file" 2>"$err_file" || true

    if ! grep -F "$expect" "$out_file" >/dev/null 2>&1; then
        fail "$label did not return expected response fragment: $expect"
        printf '[DEBUG] stdout preview: %s\n' "$(head -c 240 "$out_file" | tr '\n' ' ')"
        printf '[DEBUG] stderr preview: %s\n' "$(head -c 240 "$err_file" | tr '\n' ' ')"
        return 1
    fi

    if [ -s "$err_file" ]; then
        fail "$label wrote to stderr"
        printf '[DEBUG] stderr preview: %s\n' "$(head -c 240 "$err_file" | tr '\n' ' ')"
        return 1
    fi

    info "$label ok"
}

pack_package() {
    pkg_dir="$1"
    out_name="$2"
    (
        cd "$PROJECT_ROOT/$pkg_dir"
        npm pack --silent >"$TMP_DIR/$out_name"
    )
}

main() {
    INIT_BODY='{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"smoke","version":"1.0"}}}'
    TOOLS_BODY='{"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}'

    info "Packing npm tarballs"
    pack_package "tools/mcp-registry" "mcp.tgz.name"
    pack_package "tools/lsp-mcp-registry" "lsp.tgz.name"
    MCP_TGZ="$(cat "$TMP_DIR/mcp.tgz.name")"
    LSP_TGZ="$(cat "$TMP_DIR/lsp.tgz.name")"

    mkdir -p "$TMP_DIR/install"
    cd "$TMP_DIR/install"
    npm init -y >/dev/null 2>&1
    info "Installing packed tarballs into isolated temp project"
    npm install --silent \
        "$PROJECT_ROOT/tools/mcp-registry/$MCP_TGZ" \
        "$PROJECT_ROOT/tools/lsp-mcp-registry/$LSP_TGZ"

    MCP_PKG_ROOT="$TMP_DIR/install/node_modules/@simple-lang/mcp-server"
    LSP_PKG_ROOT="$TMP_DIR/install/node_modules/@simple-lang/lsp-mcp-server"

    probe_command "simple-mcp-server initialize" "./node_modules/.bin/simple-mcp-server" "$INIT_BODY" '"protocolVersion":"2025-06-18"' || {
        inspect_failure "simple-mcp-server" "$MCP_PKG_ROOT"
        exit 1
    }
    probe_command "simple-mcp-server tools/list" "./node_modules/.bin/simple-mcp-server" "$TOOLS_BODY" '"result":{"tools":[' || {
        inspect_failure "simple-mcp-server" "$MCP_PKG_ROOT"
        exit 1
    }
    probe_command "simple-lsp-mcp-server initialize" "./node_modules/.bin/simple-lsp-mcp-server" "$INIT_BODY" '"protocolVersion":"2025-06-18"' || {
        inspect_failure "simple-lsp-mcp-server" "$LSP_PKG_ROOT"
        exit 1
    }
    probe_command "simple-lsp-mcp-server tools/list" "./node_modules/.bin/simple-lsp-mcp-server" "$TOOLS_BODY" '"result":{"tools":[' || {
        inspect_failure "simple-lsp-mcp-server" "$LSP_PKG_ROOT"
        exit 1
    }

    info "MCP package smoke test passed"
}

main "$@"
