# Seed JIT: calling a function whose body holds a function-local `use` segfaults

- **Date:** 2026-09-13
- **Component:** Rust seed JIT (`bin/simple.exe run`, default execution mode)
- **Host:** Windows 11, x86_64-pc-windows-msvc, seed binary `C:/tool-fix/bin/simple.exe`
- **Severity:** crash (rc 139 / SIGSEGV), nothing printed to stderr
- **Status:** open (seed defect). The supported MCP path is unaffected; partial
  source-side avoidance is landed (see below).

## Symptom

Bare `simple run src/app/mcp/main.spl` (JIT) answers `initialize` and
`tools/list`, then dies with rc 139 on a real `tools/call` such as
`simple_read`. The same sequence with `SIMPLE_EXECUTION_MODE=interpreter`
answers all three. That is the mode `bin/simple_mcp_server.cmd` and
`config/mcp/win/.mcp.json` already default to.

## Minimal repro

```simple
fn _lazy_char() -> text:
    use std.common.string_core.{char_from_code}
    return char_from_code(65)

fn main() -> i64:
    print "p6 before"
    val r = _lazy_char()
    print "p6 after " + r
    0
```

```
SIMPLE_RUST_SEED_WARNING=0 bin/simple.exe run p6.spl
p6 before
Segmentation fault      (rc=139, stderr empty)

SIMPLE_EXECUTION_MODE=interpreter ... run p6.spl
p6 before
p6 after A              (rc=0)
```

## Bisection (same tree, same binary, JIT unless noted)

| probe | shape | result |
|---|---|---|
| p11 | module-level `use std.common.string_core.{char_from_code}`, then call | rc 0 (control) |
| p12 | no `use`, entry fn calls a local helper | rc 0 (control) |
| p6 | entry fn, braced function-local `use std...{char_from_code}` | **rc 139** (interpreter: rc 0) |
| p13 | entry fn, whole-module function-local `use std.common.string_core` | **rc 139** |
| p7 | entry fn, braced function-local `use app.mcp.mcp_log_options.{...}` | **rc 139** |
| p5 / p8 | entry fn, braced function-local `use app.mcp.main_dispatch.{dispatch_tool}` | **rc 139** |
| p14 | entry fn, whole-module function-local `use app.mcp.main_dispatch` | **rc 139** |
| p15 | module-level import of `main_lazy_diag_tools.run_structured_diagnostics`, whose body has a braced function-local `use` (non-entry module) | **rc 139** |
| p16 / p17 / p18 | `mcp_record_last_read`; tuple destructuring `(a, b) = f()`; `format_new_diagnostics_block` | rc 0 |
| p10 | module-level `handle_simple_read`, after hoisting that module's function-local imports | rc 0 (was rc 139) |
| p9 | module-level `dispatch_tool("simple_read")`, which reaches `_dispatch_ip_diag` with its function-local `use app.mcp.main_lazy_diag_tools` | **rc 139** |

The crash follows the function-local `use` itself. It happens with braced and
whole-module forms, with std and app targets, and in entry and non-entry
modules. The same calls through module-level imports run cleanly.

## Why it surfaced now

`src/app/mcp/main.spl` used to fail HIR lowering (`cannot infer field type
while lowering handle_resources_read: struct 'ANY' field 'complete'`), so the
whole program ran in the interpreter. Once `src/compiler` was present in the
tree, that type resolved, the fallback disappeared, and the modules were
JIT-compiled.

## Source-side avoidance: landed and rejected

Landed (cheap, no measurable startup cost):
- `src/app/mcp/main.spl`: `use app.mcp.main_dispatch.{dispatch_tool}` is now
  module-level. `main_dispatch` imports only `main_lazy_json` at top level.
  This fixes JIT `tools/call` for tools that do not reach a handler family (an
  unknown tool now answers rc 0).
- `src/app/mcp/main_lazy_diag_tools.spl`: its three
  `use app.mcp.main_lazy_query_tools.{_mcp_find_simple_binary}` imports are now
  one module-level import. That module is itself loaded lazily. This fixes p15
  and p10.

Measured and rejected: hoisting all 21 function-local `use`s in
`src/app/mcp/main_dispatch.spl` to module level. JIT `tools/call` then works,
but interpreter `initialize` goes from 12.8 s to 23.9 s and stderr from 320 B to
4440 B. That regression would land on the launcher path every client uses, to
fix a mode no launcher selects.

Remaining: in JIT, any handler family reached through
`main_dispatch._dispatch_ip_*` still crashes (p9). Bare JIT `simple run` of
`main.spl` is unsupported for real `tools/call` until the seed is fixed.

## Unblock condition

Fix the seed JIT so p6, p13 and p9 exit 0. Then the function-local `use`s in
`main_dispatch` can stay as they are, and the two hoists above may return to
function-local if lazy loading is worth it.

## Root cause — FIXED 2026-09-14

Same root as `seed_jit_app_module_function_call_segfaults_windows_2026-09-13.md`
(confirmed, not just suspected): a function reached only through a
function-local `use` still lowers to a direct call on a cross-module Simple
function symbol. `src/compiler_rust/compiler/src/codegen/jit.rs`'s
`dlsym_resolves` — the Windows half of the JIT's unresolved-import guard
(`first_unresolved_import_called` -> `jit_import_resolves` ->
`dlsym_resolves`) — unconditionally answered `true` on Windows, so the guard
could never detect that `char_from_code` (p6), or any symbol reached the same
way, resolves to neither a registered runtime symbol nor a real process/CRT
export. `compile_module` finalized it anyway, cranelift-jit bound the import's
GOT slot to NULL, and the first call SIGSEGVs with nothing on stderr.

Fix: `dlsym_resolves` on Windows now genuinely probes via `GetProcAddress`
(mirroring `cranelift-jit-0.116.1/src/backend.rs::lookup_with_dlsym`'s own
Windows fallback: the running executable image, then `ucrtbase.dll`), instead
of assuming every name resolves. Regression coverage: two new tests in
`jit_tests.rs`, `dlsym_resolves_rejects_a_nonexistent_symbol_on_windows` and
`test_jit_unresolved_extern_call_refuses_to_finalize_instead_of_null_jumping`.

Re-ran this doc's p6 repro on the rebuilt binary
(`C:/tool-jit/target/release/simple.exe`, sha256
`e28df9022d3e97c13b6a55e7571195d8422e3df0733b03274fdbbb4a6792d263`):

```
SIMPLE_RUST_SEED_WARNING=0 simple.exe run repro_b_p6.spl
[jit-fallback] unresolved external symbol 'char_from_code': whole module
dropped to the interpreter (expect ~100-1000x slowdown). Set
SIMPLE_JIT_STRICT=1 to turn this into a hard error.
p6 before
p6 after A              (rc=0)
```

Now loudly de-JITs instead of silently SIGSEGVing. The de-JIT is still
correct-but-slow (interpreter fallback for the whole module), so the source-side
avoidances in this doc (hoisting hot-path `use`s to module level) remain worth
keeping where the measured interpreter-startup cost allows it — this fix
removes the crash, not the fallback's performance cost. `bin/simple run
src/app/mcp/main.spl` still needs an end-to-end `tools/call` re-check on this
binary to confirm the crash class named in "Symptom" above is gone; not yet
independently re-verified in this pass beyond the p6/p9-shape unit repro.

**Status: FIXED** (crash), pending PR landing. Performance of the JIT
fallback path for `main_dispatch` is a separate, pre-existing concern.
