# Plan: MCP redeploy via pure-Simple `simple_core` runtime migration (2026-06-02)

**Status:** Active
**Owner:** TBD
**Bugs:** `core_c_string_len_registry_2026-06-02.md`,
`core_c_stdin_fgetc_hang_2026-06-02.md`
**Feature:** `simple_core_runtime_completeness_2026-06-02.md` (#FR-SIMPLECORE-001)
**Prior context:** `mcp_redeploy_smoke_failures_2026-06-01.md`

## Problem

The deployed `bin/simple_mcp_server` is stale (built before the Jun 1–2
serializer commits) and emits malformed `tools/list` JSON. The current Simple
serializer is already correct, so the task is a clean rebuild + redeploy — but
every native rebuild lane was broken. Per project policy the fix must be pure
Simple (C runtime edits are reverted); the seed (Rust) may be fixed after.

## Done in this change set

- **Pure Simple — compile failures (root of every lane's failure):**
  `src/lib/editor/render/md_renderer.spl` and
  `src/lib/editor/view/preview_pane.spl` were missing type imports
  (`RenderBlock`/`BlockModel`/`SdnGraph*`) → HIR `struct 'ANY'` errors. Added
  the imports → native build goes from `2 failed` to `0 failed`.
- **Pure Simple — MCP stdin hang:** `src/app/mcp/main_lazy_protocol.spl` now
  reads stdin with a `read()`-syscall `mcp_read_char()` (mirrors `simple_core`),
  bypassing the broken C `fgetc` `stdin_read_char`. Hang fixed (EOF terminates).
- **Seed (Rust), allowed after pure Simple:**
  - `native_project/stubs.rs`: macOS `.weak` → platform `.weak_definition`
    (macOS `as` rejected GNU `.weak`).
  - `native_all/src/lib.rs`: removed 15 stub symbols duplicating
    `simple-runtime` (duplicate-symbol link failures).
  - Found: `--strip` breaks macOS `__simple_call_module_inits` generation —
    omit `--strip` for these binaries.
- **Regression test:** `test/unit/app/mcp/mcp_tools_list_json_spec.spl` guards
  the `tools/list` serializer (boundary `}},{"name"`, balanced braces, tool set
  incl. `play_wm_text_*`). (Note: `bin/simple test` runner currently segfaults
  on any spec — pre-existing; logic verified via `bin/simple run`.)

With the above, the **core-c lane now builds clean (0 failed) and links**.

## Remaining blocker

The core-c binary still cannot respond: `.len()` returns garbage on the C
runtime (registry check in `rt_core_as_string`). Fix = use `simple_core`'s
runtime, which has a registry-free `rt_string_len` and `read()` stdin.

## Migration steps

1. **Audit (done):** 58 of 173 MCP-needed runtime symbols missing from
   `simple_core` (see feature doc). Regenerate the gap with:
   ```
   nm <mcp-core-c-binary> | grep ' T ' | awk '{print $NF}' | sed 's/^_//' | sort -u > bin.txt
   nm <rust libsimple_runtime.a> | grep ' T ' | awk '{print $NF}' | sed 's/^_//' \
     | grep -E '^(rt_|spl_|stdin|stdout|stderr)' | sort -u > contract.txt
   grep -rh '^pub fn ' src/runtime/simple_core/*.spl | sed -E 's/^pub fn ([a-zA-Z0-9_]+).*/\1/' | sort -u > sc.txt
   comm -12 bin.txt contract.txt | comm -23 - sc.txt    # = the gap
   ```
2. **Implement easy tier (~15):** print/println/getpid/tuple_len/trim_start/
   char_code_at/text_count_codepoints, dict + bytes ops, in `simple_core`.
3. **Implement moderate tier (~17):** file/dir I/O + process via `extern`
   syscalls + Simple logic (pattern: existing `read`/`write`/`malloc`).
4. **TCP/channels (~26):** implement, OR trim the linked tool code so the MCP
   stdio path doesn't pull TCP, deferring this tier.
5. **Wire into the lane:** change `build_core_c_runtime_library`
   (`compiler/src/pipeline/native_project/tools.rs`) to compile `simple_core`
   `.spl` as the lane runtime (or have its symbols win over the C archive so the
   buggy C `rt_string_len`/`stdin_read_char` are not linked). Resolve symbol
   overlap so there are no duplicate definitions.
6. **Build + verify + deploy:**
   ```
   <driver> native-build --runtime-bundle core-c \
     --source src/compiler --source src/app --source src/lib \
     --entry-closure --entry src/app/mcp/main.spl \
     --output bin/release/<triple>/simple_mcp_server      # NOTE: no --strip
   scripts/check-mcp-native-smoke.shs   # expect json_valid=true, wm_text_present=true
   ```
   Deploy ONLY `simple_mcp_server` to `bin/release/<triple>/`; do NOT overwrite
   the self-hosted `bin/release/<triple>/simple`.

## Verification signals

- `"abc".len() == 3` true on core-c; stdin EOF terminates.
- `scripts/check-mcp-native-smoke.shs`: `mcp_tools_json_valid=true`,
  `mcp_tools_schema_valid=true`, `mcp_wm_text_tools_present=true`.

## Notes / risks

- The rebuilt driver + `native_all` used for these builds live in
  `src/compiler_rust/target/release` only; the seed fixes must be carried into
  a proper bootstrap before the deployed `bin/release/.../simple` driver can
  reproduce these builds.
- Shared `src/app/simple_lsp_mcp/json_helpers.spl` still uses C
  `stdin_read_char` (fine for interpreter/rust-hosted; needs the same `read()`
  treatment for a core-c LSP deploy).
