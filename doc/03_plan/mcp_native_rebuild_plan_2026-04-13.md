# MCP Native Rebuild Plan (2026-04-13)

## Goal

Rebuild `build/native/simple_mcp_native` and `build/native/simple_lsp_mcp_native` so the resulting Mach-O binaries contain the `install_parent_death_watchdog` / `SIMPLE_PARENT_DEATH_EXIT` runtime symbols from `libsimple_runtime.a`, then deploy to `bin/release/aarch64-apple-darwin-macho/simple_mcp_server` and `simple_lsp_mcp_server`.

## Status at plan time

- Watchdog commit `tkmvrmoq 4743092e feat(runtime): add SIMPLE_PARENT_DEATH_EXIT parent-death watchdog` is on `main` and `main@origin`.
- `libsimple_runtime.a` + `libsimple_native_all.a` contain the watchdog symbols (verified via `strings`).
- Production `bin/release/aarch64-apple-darwin-macho/simple_mcp_server` is `md5`-identical to `build/native/simple_mcp_native` from 11:43 — pre-watchdog. Zero matches for `SIMPLE_PARENT_DEATH_EXIT` in either.
- Bootstrap re-ran setup.sh at 13:42 which copied the pre-watchdog build/native/ files over the production locations without rebuilding them.

## Blockers

1. **Self-hosted compiler segfault.** `bin/simple native-build --source src/lib --source src/app --entry src/app/mcp/main.spl -o /tmp/x` → exit 139. Fresh post-bootstrap `bin/simple` hits it too. Out of scope: fixing this is its own task.
2. **Rust seed chokes on vscode_extension examples.** `src/compiler_rust/target/bootstrap/simple native-build ...` → exit 1 with 8 parse errors in `src/app/vscode_extension/examples/*.spl` and `src/app/vscode_extension_old/**/*.spl`. These files belong to a concurrent session doing migration work and must not be edited.

## Recommended approach — B1: Rust seed + `--entry-closure`

`src/compiler_rust/compiler/src/pipeline/native_project/discovery.rs` and `src/compiler_rust/driver/src/cli/native_build.rs` expose a `--entry-closure` flag that restricts discovery to modules transitively reachable from `--entry` via `use` statements. Since the 8 broken `vscode_extension*` files are never `use`d from `src/app/mcp/main.spl` or `src/app/simple_lsp_mcp/main.spl`, they never enter the compile set and the parse errors never fire.

## Probes (READ-ONLY, all must pass before any WRITE)

| # | Probe | Abort if |
|---|---|---|
| P1 | `nm src/compiler_rust/target/release/libsimple_runtime.a \| grep install_parent_death_watchdog` | 0 matches |
| P2 | `src/compiler_rust/target/bootstrap/simple native-build --help \| grep entry-closure` | Flag absent |
| P3 | `grep -rhE '^\s*use\s+' src/app/mcp src/app/simple_lsp_mcp \| grep vscode_extension` | Any hit |
| P4 | Dry-run build to `/tmp/probe_mcp` with `--entry-closure` | Still emits the 8 vscode parse errors, or any other compile error |
| P5 | `strings /tmp/probe_mcp \| grep -c SIMPLE_PARENT_DEATH_EXIT` | 0 matches |
| P6 | `jj status` + check no concurrent session holds pending changes under `build/native/` or `bin/release/aarch64-apple-darwin-macho/` | Any pending change |

## Phase 1 — Build (WRITES: /tmp only)

```sh
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=$(pwd)/src \
  src/compiler_rust/target/bootstrap/simple native-build \
  --source src/lib --source src/app \
  --entry src/app/mcp/main.spl \
  --entry-closure \
  --runtime-bundle auto \
  --runtime-path src/compiler_rust/target/release/deps \
  -o /tmp/simple_mcp_native.new --strip
```

Then verify:
```sh
strings /tmp/simple_mcp_native.new | grep -c SIMPLE_PARENT_DEATH_EXIT   # ≥1
nm /tmp/simple_mcp_native.new 2>/dev/null | grep install_parent_death_watchdog
file /tmp/simple_mcp_native.new    # Mach-O 64-bit executable arm64
/tmp/simple_mcp_native.new --help 2>&1 | head -5
```

Repeat for the LSP binary with `--entry src/app/simple_lsp_mcp/main.spl` and `-o /tmp/simple_lsp_mcp_native.new`.

## Phase 2 — Stage into build/native/ (WRITES: repo)

```sh
cp build/native/simple_mcp_native     build/native/simple_mcp_native.bak_pre_watchdog
cp build/native/simple_lsp_mcp_native build/native/simple_lsp_mcp_native.bak_pre_watchdog
mv /tmp/simple_mcp_native.new        build/native/simple_mcp_native
mv /tmp/simple_lsp_mcp_native.new    build/native/simple_lsp_mcp_native
chmod +x build/native/simple_mcp_native build/native/simple_lsp_mcp_native
```

Rollback: `mv *.bak_pre_watchdog` back.

## Phase 3 — Deploy (WRITES: repo)

```sh
cp bin/release/aarch64-apple-darwin-macho/simple_mcp_server     bin/release/aarch64-apple-darwin-macho/simple_mcp_server.bak_pre_watchdog
cp bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server.bak_pre_watchdog
cp build/native/simple_mcp_native     bin/release/aarch64-apple-darwin-macho/simple_mcp_server
cp build/native/simple_lsp_mcp_native bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server
chmod +x bin/release/aarch64-apple-darwin-macho/simple_mcp_server bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server
```

## Verification

```sh
strings bin/release/aarch64-apple-darwin-macho/simple_mcp_server     | grep -c SIMPLE_PARENT_DEATH_EXIT   # ≥1
strings bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server | grep -c SIMPLE_PARENT_DEATH_EXIT   # ≥1
nm  bin/release/aarch64-apple-darwin-macho/simple_mcp_server     2>/dev/null | grep install_parent_death_watchdog
nm  bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server 2>/dev/null | grep install_parent_death_watchdog
md5 bin/release/aarch64-apple-darwin-macho/simple_mcp_server     build/native/simple_mcp_native
md5 bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server build/native/simple_lsp_mcp_native
bin/release/aarch64-apple-darwin-macho/simple_mcp_server --help 2>&1 | head
```

### End-to-end parent-death test

Launch the rebuilt server as a child of a test parent, SIGKILL the parent, confirm the child exits within ≤2 seconds of the kill with `SIMPLE_PARENT_DEATH_EXIT=1` set.

## Fallbacks (in order)

1. **B1** — `--entry-closure` (recommended).
2. **B2** — narrower explicit `--source` enumerating only MCP dependencies if `--entry-closure` doesn't filter as expected.
3. **B3** — repo-root `.jjignore` temporarily excluding `src/app/vscode_extension*`. Only if `collect_spl_files_recursive` actually honors `.jjignore` — requires reading `native_project/mod.rs` first.
4. **E** — wait for the concurrent session to land its vscode_extension fix.
5. **Status quo** — leave production pre-watchdog. The Node wrappers (`bin/codex_*_mcp.js`) already handle the observed leak path via ppid polling.

Do NOT fall back to fixing the `bin/simple` segfault (Option A) or designing an SFFI watchdog cdylib (Option C) without explicit user approval.

## Abort conditions (STOP + advisor)

1. Runtime archives lose the watchdog symbols.
2. Any MCP module transitively imports from `app.vscode_extension*`.
3. `--entry-closure` still emits the 8 parse errors.
4. Built binary lacks `SIMPLE_PARENT_DEATH_EXIT`.
5. Concurrent session has pending changes under `build/native/` or `bin/release/aarch64-apple-darwin-macho/`.
6. Smoke test hangs or exits nonzero.
7. Parent-death E2E test doesn't reap within 5 seconds.
8. `jj status` shows unexpected modifications beyond the 6 target files + their `.bak_pre_watchdog` siblings.

## Non-goals

- Fixing the self-hosted `bin/simple` native-build segfault.
- Designing or building an SFFI watchdog cdylib.
- Modifying any file under `src/app/vscode_extension*/`.
- Rebuilding the Rust seed or runtime archives.
- Rebuilding `bin/release/.../simple` (the main compiler).
- Any `jj` commit/push (build outputs live in gitignored dirs).

## Critical files

- `src/compiler_rust/driver/src/cli/native_build.rs`
- `src/compiler_rust/compiler/src/pipeline/native_project/discovery.rs`
- `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs` (for `collect_spl_files_recursive`)
- `src/compiler_rust/runtime/src/value/args.rs`
- `src/app/mcp/main.spl`
- `src/app/simple_lsp_mcp/main.spl`
