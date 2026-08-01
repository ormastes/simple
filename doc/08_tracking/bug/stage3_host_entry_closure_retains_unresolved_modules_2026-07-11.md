# Stage3 Host Entry Closure Retains Unresolved Modules

The pure-Simple stage3 compiler builds the production hosted WM with
`--source src/os/hosted/hosted_entry.spl --entry-closure`, compiles all source
files successfully, then generates 23 unresolved-symbol stubs. The evidence
wrapper deletes this linked candidate and reports
`production-native-build-incomplete`.

The unresolved object owners include Engine2D Metal/SFFI modules, OS userlib
window/log/fs modules, common binary I/O, and failsafe logging. Removing the
production compositor's only `os.userlib.ipc_protocol` dependency and moving
its method numbers to `common.window_protocol.compositor_methods` did not
change the set. A clean measurement compiled 271 modules with zero failures
and retained the same 23 names, including `_file_metadata`, `_glob_find`,
`_spl_dlopen`, `_unsafe_addr_of`, and `_wm_input_event`.

The compiler must limit emitted objects and unresolved-symbol synthesis to the
reachable function/data closure, or provide a strict mode that rejects and
reports the exact reachability path for every retained unresolved symbol. A
linked artifact containing generated return stubs is not valid host WM
evidence.

## 2026-07-17 update: current symptom is a NEW upstream regression, not this one

Re-running the exact repro (`bin/simple native-build --source
src/os/hosted/hosted_entry.spl --entry src/os/hosted/hosted_entry.spl
--entry-closure -o <out> --clean`, Rust-seed `bin/simple` at
`5aee6bc6a25`) no longer reaches the link stage described above at all, so
the 23-stub symptom could not be re-checked. Two distinct findings:

**1. Not a hang — just slow, and the reported 300s window was too short.**
Sampling `/proc/<pid>` every 60s showed a single `simple-main` thread
pinned at ~99% CPU the whole time (never blocked on I/O/a lock: wchan only
ever `futex_wait_queue` on idle helper threads), with RSS flat at
~1.3–1.4 GB (no unbounded growth). The build log looked "frozen" at ~1510
lines only because `log_debug`/`log_phase` are no-ops or eprint-gated
behind `SIMPLE_COMPILER_PHASE_PROFILE=1` / `SIMPLE_COMPILER_TRACE=1` (see
`src/compiler/80.driver/driver_log_helpers.spl`), which are off by
default. With those env vars enabled on a smaller-timeout probe, phase2
(per-file parse of the ~128-source entry closure) shows each file costs
roughly a 1.3s fixed overhead + ~2.2 ms per source character under the
interpreted seed — e.g. `src/os/hosted/hosted_entry.spl` (23,457 chars)
alone took 54.1s, and `src/os/compositor/host_compositor_core.spl`
(75,754 chars) took over 180s and didn't even finish before a 240s probe
timeout. Given a full 2400s budget, the real (untraced) run actually
finished — with an ERROR, not a hang — at ~420s wall time. So: a 300s
timeout is simply not enough for this target's entry closure via the
seed; it is not stuck.

**2. Genuine new blocker: `phase 2 FAILED` — a parser regression for
declare-without-initializer `var` locals.** The run that completes at
~420s fails parsing with:

```
[parser_error] path src/std/gc_async_mut/gpu/engine2d/draw_ir_adv.spl line 586:28: expected =, got Newline ''
[parser_error] line 586:28: unexpected token in expression: Newline ''
[ERROR] phase 2 FAILED
error: native-build failed without diagnostics
```

Line 586 is `var offscreen: Engine2D` — a local variable declared with a
type annotation but no initializer, assigned later inside conditional
branches (`if`/`elif` + `match` arms). Root cause: `parse_var_decl_stmt()`
in `src/compiler/10.frontend/core/parser_stmts.spl` (around line 645–682)
unconditionally calls `parser_expect(100)` (the `=` token) after the
optional type-tag, with no branch for "type annotation present, no
initializer, next token is a statement terminator." This is a **general**
parser limitation, not specific to `draw_ir_adv.spl` or to `Engine2D`:
the exact same source shape (`var name: SomeType` with no `=`, assigned
later via `match`/`if` arms) is used as ordinary style in several other
files already in the tree, e.g.:
- `src/lib/nogc_async_mut/http_server/worker.spl:184,191`
  (`var chain: TlsCertificateChain`, `var key: TlsPrivateKey`)
- `src/lib/nogc_async_mut/http_server/static_file.spl:397,505`
- `src/lib/nogc_async_mut/http_server/range.spl:64-65`
- `src/app/simple_process_manager/spm_service.spl:24-26`
- `src/app/test_daemon/daemon.spl:438`

A minimal standalone repro (independent of the OS/GUI closure) confirms
this is general, not file-specific:

```simple
struct Thing:
    tag: i64

fn pick(flag: bool) -> Thing:
    var result: Thing
    if flag:
        result = Thing(tag: 1)
    else:
        result = Thing(tag: 0)
    result
```

`bin/simple native-build --entry <this file> -o <out> --clean` fails with
the identical `expected =, got Newline` at the `var result: Thing` line.
These other files apparently never hit this because their closures are
not exercised by the currently-passing native-build coverage (TLS/HTTP
server paths, etc.); `draw_ir_adv.spl` is the first case pulled into a
tested entry closure (the hosted WM's Engine2D/GPU closure) since this
construct was written into it.

**Net effect:** the hosted-WM entry-closure native-build currently cannot
reach the MIR-lowering/codegen/link stage at all (blocked in phase 2), so
the original 23-unresolved-stub symptom in this doc is currently
unreachable/unverifiable until the parser gap above is fixed. Both bugs
are real and distinct; this doc's original title symptom should be
re-verified once `parse_var_decl_stmt` supports declare-without-init
`var` locals (or `draw_ir_adv.spl`'s construct is rewritten, though that
would only paper over the general parser gap, which 8+ other files also
rely on).

No fix was applied in this pass: `parse_var_decl_stmt` is a hot, universally
exercised path (every `var` statement in the ~600K-line codebase is parsed
through it by the interpreted seed), and a correct fix needs a matching
"no initializer" representation through HIR/MIR lowering (and the
interpreter's own decl-eval path) — verifying that safely requires the
self-hosted bootstrap rebuild loop, which is out of scope for a
worktree-only diagnosis pass.
