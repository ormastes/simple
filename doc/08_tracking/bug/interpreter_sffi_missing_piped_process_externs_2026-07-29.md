# Bug: `rt_process_spawn_piped` family not registered in the interpreter's extern dispatch table

- **Date:** 2026-07-29
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** medium (blocks real execution of a real, already-used stdlib facade under `bin/simple test`/`bin/simple run` on the current Rust seed; does not affect correctness of any landed logic)
- **Found by:** lane DS6 `gdb-transport` (mission-critical robustness campaign), while writing a system spec that spawns real `gdb --interpreter=mi3` through `std.nogc_sync_mut.io.process_spawn_piped`
- **Related:** `src/app/debug/remote/protocol/gdb_mi.spl`, `src/lib/nogc_sync_mut/io/process_ops.spl`, `src/runtime/runtime_process.c`, `src/lib/editor/services/debug_session_dap.spl`, `src/app/editor/debug_process_runtime.spl`, `test/03_system/gui/editor_debug_session_spec.spl`

## Symptom

Any `.spl` program that calls `process_spawn_piped()` (or the sibling
`process_write_stdin`/`process_read_stdout`/`process_close_piped`/
`process_write_stdin_some`) fails at the extern-call boundary:

```
ERROR simple_compiler::interpreter_sffi: rt_interp_call error: SemanticWithContext(
  ContextualError { message: "unknown extern function: rt_process_spawn_piped", ... })
```

- Under `bin/simple run`, this is logged and the call soft-fails (returns
  `pid=0`); execution continues.
- Under `bin/simple test`, the same failure surfaces as a hard per-`it`
  failure (`✗ ...` / `semantic: unknown extern function: rt_process_spawn_piped`),
  not a catchable `Result` — Simple has no try/catch by design
  (`.claude/rules/language.md`), so a spec cannot recover from this in-language.

Reproduced with a two-line probe:

```simple
use std.nogc_sync_mut.io.{process_spawn_piped}
fn main():
    print "pid={process_spawn_piped(\"true\", [])}"
```

`bin/simple run` → `pid=0` (with the ERROR line above on stderr).
`bin/simple test` (wrapped in an `it` block) → the example fails with the
semantic error text instead of a normal assertion failure.

## Root cause

`rt_process_spawn_piped`, `rt_process_write_stdin`,
`rt_process_write_stdin_some`, `rt_process_read_stdout`,
`rt_process_close_piped`, and `rt_browser_renderer_spawn_sandboxed` /
`rt_browser_renderer_sandbox_enter` are all implemented natively in
`src/runtime/runtime_process.c` (confirmed: non-blocking pipe read,
real fork/exec, SIGTERM+reap on close) and are declared correctly as
`extern fn` in `src/lib/nogc_sync_mut/io/process_ops.spl`. The
self-hosted compiler's own backend even carries them in its known-extern
registry (`src/compiler/70.backend/backend/stage4_symbol_closure.spl:584`).

But `grep -rn "rt_process_spawn_piped" src/compiler_rust/src` returns **zero
matches** — the Rust bootstrap seed's `interpreter_sffi` bridge (the
tree-walk interpreter's foreign-function dispatcher, which both `bin/simple
test` and — on this seed — `bin/simple run` end up routing through) never
had this whole extern family added to its dispatch table. It is a gap in
the seed binary's Rust source, not a `.spl`-side bug and not something a
rebuild-from-current-source would fix on its own (the source genuinely
lacks the registration).

This is why the *only* existing spec in the tree that touches this facade,
`test/03_system/gui/editor_debug_session_spec.spl:276`, does not actually
call it — it only asserts the extern is textually declared
(`expect(src.contains("extern fn rt_process_spawn_piped(...)"))`). That is
independent confirmation this gap predates lane DS6 and was already being
worked around the same way elsewhere.

## Impact on lane DS6

`GdbMiClient` (owned by this lane) was rewritten to use
`process_spawn_piped`/`process_write_stdin`/`process_read_stdout`/
`process_close_piped` instead of the old `mkfifo` + `sh -c` + `timeout grep`
transport — this is still believed correct (it matches the primitives
already used, unmodified, by `debug_session_dap.spl` and
`debug_process_runtime.spl`, and the self-hosted compiler's own extern
registry knows about them). The new system spec,
`test/03_system/app/debug/remote/protocol/gdb_mi_transport_spec.spl`,
detects this specific capability gap via a **safe out-of-process probe**
(spawns a throwaway `bin/simple run <probe>.spl` child and reads its
stdout, since the failure mode is non-fatal under `run`) and skips cleanly
with a message pointing at this file, rather than either faking a pass or
leaving a permanently-red spec. Once this gap is closed the same spec will
exercise the real transport automatically — no spec changes needed.

## Suggested fix

Add `rt_process_spawn_piped`, `rt_process_write_stdin`,
`rt_process_write_stdin_some`, `rt_process_read_stdout`,
`rt_process_close_piped` (and the two `rt_browser_renderer_*` variants) to
the Rust seed's `interpreter_sffi` extern dispatch table, wired to the
existing native implementations in `runtime_process.c`. Out of scope for
this lane (Rust seed change + rebuild; project rule is "fix .spl not Rust"
and "no bootstrap unless essential").

## 2026-08-17 re-verification (lane m1_rust_interp) — ALREADY FIXED IN SOURCE

Classified by CONTENT, not by commit ancestry (per session CORRECTIONS #1).

The whole piped-process family IS registered in the interpreter extern dispatch
table. `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` carries an
explicit back-reference to THIS doc at line 1624, immediately above the
registrations:

```
1624:    // doc/08_tracking/bug/interpreter_sffi_missing_piped_process_externs_2026-07-29.md
1625:    insert_simple!("rt_process_spawn_piped", system::rt_process_spawn_piped);
...
1629:    insert_simple!("rt_process_close_piped", system::rt_process_close_piped);
```

The implementations live in `interpreter_extern/system.rs:1094-1190`
(`rt_process_spawn_piped` at :1131, with a `PipedChildren` registry at :1115).

The triage row's evidence ("git grep rt_process_spawn_piped under
interpreter_extern/ returns zero hits") is **wrong** — it returns 12 hits across
`system.rs` and `mod.rs`.

**Status: RESOLVED (stale doc).** Note the deployed `bin/simple` seed predates
this and may still exhibit the symptom until redeployed; that is a deployment
lag, not a source defect.
