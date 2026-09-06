# `src/lib` defines `fn eprint`, shadowing the prelude builtin program-wide; native-build then cannot resolve `eprint` at all

- **Filed:** 2026-08-17 (c_splmisc lane)
- **Severity:** P1
- **Class:** wrong-function dispatch (silently, in the interpreter) escalating to
  a hard native-build failure
- **Status:** OPEN — root cause RE-DIAGNOSED 2026-08-17 (the shadow is NOT the
  cause; see "Re-diagnosis" at the bottom). A one-line pure-Simple fix has been
  applied but is **NOT yet verified by a completed native-build**.
- **Root cause (original, superseded):** `src/lib/nogc_sync_mut/io/process_ops.spl:558`
  — `fn eprint(msg: text):`
- **Root cause (actual):** `src/compiler/20.hir/hir_lowering/expressions.spl:51`
  — `is_interp_builtin_fn` omitted `eprint`.

## Summary

`eprint` is a prelude builtin. `src/lib/nogc_sync_mut/io/process_ops.spl:558`
also declares a *user function* named `eprint`. The compiler itself detects the
collision and states the blast radius precisely:

```
WARNING: `fn eprint` at line 558 shadows the prelude builtin `eprint` and is
being called INSTEAD of it. This applies to the whole program, including modules
that only imported this one transitively. Rename the local function if that was
not intended.
```

Read that carefully: **"is being called INSTEAD of it"**, and **"the whole
program, including modules that only imported this one transitively."** Any
program that transitively imports `std.nogc_sync_mut.io.process_ops` — which is
most of them, since it arrives through ordinary I/O imports — has every
`eprint(...)` call in *its own* source rebound to the stdlib function. This is a
warning, not an error, so it is easy to scroll past in a build log that already
emits ~1900 warning lines.

## Reproduction (executed, verbatim)

Fixture `r4.spl` (this fixture was originally written for
`stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10.md`;
the `eprint` behaviour is incidental to that row but is the whole of this one):

```
struct Ctx:
    errors: [text]

class Drv:
    ctx: Ctx

impl Drv:
    me phase(c: Ctx) -> Ctx:
        Ctx(errors: c.errors.push("boom"))

    me drive():
        self.ctx = self.phase(self.ctx)
        eprint("count=")
        eprint(self.ctx.errors.len())
        if self.ctx.errors.len() > 0:
            eprint(self.ctx.errors[0])

fn main():
    val d = Drv(ctx: Ctx(errors: []))
    d.drive()
```

### Interpreter / JIT lane — works

```
$ nice -n 19 bin/simple run .../r4.spl --timeout 300
rc=0
count=1boom
```

### Native lane — FAILS

```
$ cd .../w && timeout 600 nice -n 19 bin/simple native-build r4.spl -o r4.bin > nb.out 2>&1
$ rc=$?
rc=1

error: HIR lowering error in r4.spl: unresolved name: eprint at r4.spl:9:35
error: HIR lowering error in r4.spl: unresolved name: eprint at r4.spl:9:35
!!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!
error: native-build worker exited with code 1.
  interpreter: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple (exit code 1)
```

`rc` was assigned on the line **after** the command, never read through a pipe.

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
59536728 bytes, mtime 2026-08-16 22:59 (Rust seed). The `native-build` worker
runs the pure-Simple driver — `nb.out` contains the driver's own
`[bootstrap-error-count] source_idx=0 point=entry count=0` trace — so this is a
pure-Simple-lane resolution result, not a seed-only artifact.

The same shadow warning is emitted three times in one build from two distinct
sites (`nb.out:13` reports line 464 of another module, `nb.out:1580` and `:1816`
report `process_ops.spl:558`), so this is not a single stray declaration.

## Why this is worse than an ordinary shadow

1. **Silent in the common lane.** On the interpreter the program runs and prints;
   the user simply gets the stdlib function instead of the builtin. If the two
   ever differ in buffering, flushing, stream, or return type, the difference is
   invisible at the call site.
2. **Hard failure in the native lane, at a call the user wrote.** The
   diagnostic blames `r4.spl:9:35` — the *user's* file — for a name the user
   never shadowed. Nothing in that message points at
   `src/lib/nogc_sync_mut/io/process_ops.spl`. A user hitting this has no path
   from the error to the cause except by noticing the warning 1500 lines earlier.
3. **Transitive and invisible.** The user need not import `process_ops`
   directly.

## Suspected connection to an existing row

`stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10.md`
records that `eprint` referencing a `text` parameter "silently did not persist"
natively, and its own Not-done list asks whether the symptom is
`eprint`-specific or affects `print`/`file_write` equally. **This shadow is a
strong candidate answer**: if `eprint` resolves to a stdlib function rather than
the builtin, an `eprint`-specific native anomaly is expected and a
`print`-specific one is not. Anyone working that row should first re-run its
repro with `print` substituted for `eprint` and compare. A `print`-substituted
build was started here but had not completed when this lane stopped.

## Fix direction (not applied)

`src/lib/**` is outside this lane's exclusive file scope, so nothing was
changed. The compiler's own warning states the remedy: rename the local
function. `process_ops.spl:558`'s `eprint` should become an explicitly-named,
non-colliding helper, with its call sites updated. Before renaming, check
whether it is deliberately re-exported as part of the module's public surface —
if it is, this is an API change and needs the owner's sign-off.

A second, independent hardening worth considering: **shadowing a prelude builtin
program-wide should be an ERROR, not a warning.** The current warning correctly
describes an outcome nobody would choose on purpose, and it is emitted into logs
where it cannot realistically be seen.

## What was NOT proven

- Whether the stdlib `eprint` and the prelude builtin actually behave
  differently (stream, buffering, flush, return type). If they are equivalent,
  the interpreter-lane impact is cosmetic and only the native failure matters.
  This was not diffed.
- Whether `print` and `file_write` are affected by sibling shadows. The
  `print`-substituted native build was still running at stop-work.
- The other shadow site reported at `nb.out:13` ("line 464") was not identified
  to a file.
- No spec was written: this lane filed rather than fixed, and the project's
  two-spec rule attaches to fixes. A reproducing spec must shell out to a
  subprocess running `native-build` — a spec body runs interpreted and can never
  observe this.

## Re-diagnosis 2026-08-17 — the stdlib shadow is NOT the cause

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
**59537240 bytes, mtime 2026-08-17 12:58:51** (Rust seed).

### The shadow is deliberate and load-bearing

`src/lib/nogc_sync_mut/io/process_ops.spl:550-559` carries an explicit comment
block saying so, added by the fix for
`eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`: the shadowing
`fn eprint` exists precisely so the self-hosted compiler's diagnostics reach the
real fd 2 instead of fd 1, and it ends with "Do NOT reintroduce a `print`
fallback here." The sibling site the original filing could not identify
("nb.out:13, line 464") is `src/app/io/process_ops.spl:464` — the same function
in the app-tier mirror of the same module. **Renaming either one, the remedy the
original "Fix direction" section proposed, would re-open a fixed P1.** That
remedy should not be applied.

### The native failure is an independent, unrelated gate

`unresolved name: eprint` is emitted by the pure-Simple HIR lowerer at
`src/compiler/20.hir/hir_lowering/expressions.spl:400-402`. That error is
reached only when the name matches none of the escape predicates at `:385`:

```
if is_interp_builtin_fn(name) or is_bootstrap_builtin or is_result_variant or ...
```

- `is_interp_builtin_fn` (`:51`) listed `print`, `println`, `to_string`,
  `type_of`, `clone`, `file_exists`, `file_read`, `file_write`, `file_delete`,
  `env_get`, `env_set`, `int`, `float`, `bool`, `panic`, `str`, `text`
  — **and not `eprint`**.
- `is_bootstrap_builtin` (`:351`) DOES accept `eprint`
  (`is_bootstrap_builtin_fn`, `:93-105`) but only when
  `SIMPLE_BOOTSTRAP == "1"`.

So `eprint` was resolvable **only inside a bootstrap build**. An ordinary
`native-build` of a user file that calls `eprint(...)` had no path to it and
died pointing at the user's own line — exactly the "blames `r4.spl:9:35` for a
name the user never shadowed" symptom in §2 above. Nothing about the stdlib
declaration participates: the diagnostic fires before any module symbol is
consulted, which is also why the interpreter lane (which resolves the stdlib
function by name and runs fine) never showed it.

Everything downstream of HIR already handled `eprint` unconditionally, which is
what makes this a one-line gap rather than a missing feature:
- MIR: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1291`
  (`if name == "eprint": return MirType.unit()`).
- LLVM backend: `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:1603`
  maps `eprint` -> `@rt_eprintln`, and `:1677` types its return `void`.

### Fix applied (pure-Simple, one line)

`src/compiler/20.hir/hir_lowering/expressions.spl:51` — `eprint` added to
`is_interp_builtin_fn`, with a docstring paragraph recording why. No stdlib file
was touched, so the deliberate fd-2 shadow is preserved intact.

`eprintln` was deliberately NOT added: unlike `eprint` it has no MIR or LLVM
lowering (`grep -rn '"eprintln"' src/compiler` finds it only in the builtin
registry, the effect table, a checker list and a lint list), so admitting it at
HIR would move the failure downstream rather than fix it. That is a separate
row, not silently in scope here.

### VERIFICATION STATUS — NOT PROVEN, DO NOT CLOSE

The fixture `r4.spl` from §"Reproduction" was rebuilt verbatim and
`native-build` was run before and after the change:

```
$ cd <scratch>/w && timeout 5400 nice -n 19 bin/simple native-build r4.spl -o r4.bin > nb2.out 2>&1
$ rc=$?     # assigned on the line AFTER the command, never through a pipe
rc=255
$ grep -c 'unresolved name' nb.out nb2.out
nb.out:0
nb2.out:0
```

**Neither run reproduced the documented failure and neither produced a binary.**
Both hit the wall-clock limit (host under concurrent bootstrap load) with
`error: native-build worker timed out ... before producing a binary` and never
reached the point where the original `rc=1` / `unresolved name: eprint` was
emitted — the pre-change control log is byte-comparable to the post-change one
(1185 vs 1189 lines, both 0 unresolved-name lines). Per this repo's convention an
absent verdict is UNVERIFIED, never a pass and never a fail, so **these two runs
carry zero evidence in either direction** and the fix above rests on source
analysis alone.

To close this row someone must, on a quiet host, run `native-build` on `r4.spl`
to completion and observe (a) a produced `r4.bin` and (b) `./r4.bin` printing
`count=1boom` on **fd 2** (`./r4.bin 2>err.log 1>/dev/null` must leave `err.log`
non-empty — that is the assertion the 2026-08-10 row cares about). Until then
this record stays OPEN.

### Verification attempt 2026-08-17 (20:12-20:4x) on the NEWLY REDEPLOYED seed — STILL UNVERIFIED

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
md5 `669150b61f2f20401a6a895ae54e9fee`, size 59550432, mtime
2026-08-17 20:10:45 UTC.

The same `r4.spl` fixture was rebuilt verbatim and `native-build` was run
**twice**, the second time with the CPU guard explicitly disabled. Both runs
were **killed by the host's RSS guard before producing a binary**:

```
$ cd <scratch>/w && timeout 5400 nice -n 19 bin/simple native-build r4.spl -o r4.bin > nb.out 2>&1
NBEXIT=143
$ cd <scratch>/w && SIMPLE_TIMEOUT_SECONDS=0 timeout 5400 nice -n 19 \
    bin/simple native-build r4.spl -o r4.bin > nb3.out 2>&1
NB3EXIT=143
$ tail -1 nb3.out (kill line)
error: TIMEOUT: killed by kill_simple_monitor (rss=24159MB>=24000MB:
  .../simple run src/app/cli/native_build_worker.spl r4.spl -o r4.bin).
  Raise the limit with SIMPLE_TIMEOUT_SECONDS=<secs> (0 disables the CPU guard)
$ grep -c 'unresolved name' nb.out nb3.out   ->  0 and 0
$ ls r4.bin  ->  No such file or directory
```

`SIMPLE_TIMEOUT_SECONDS=0` disables only the **CPU** guard; the kill here is the
**RSS** ceiling (24 GB), so that knob does not help and neither run reached the
point where the original `rc=1` / `unresolved name: eprint` was emitted. Both
logs stop while the worker is still loading the compiler's own `20.hir` source
(`nb3.out:1042-1094` are `export use` warnings from `src/compiler/20.hir/**`).

Per this repo's convention an absent verdict is UNVERIFIED, **never a pass**:
these two runs carry zero evidence in either direction, exactly like the earlier
pair. **The one-line fix at `expressions.spl:51` therefore remains unverified by
execution and this record stays OPEN.**

Only the interpreter lane is confirmed green (it always was, and it does not
exercise the failing path):

```
$ bin/simple run <scratch>/w/r4.spl
1
boom
rc=0
```

**New, concrete blocker to record:** this row cannot be closed on this host at
all — the pure-Simple `native_build_worker` needs >24 GB RSS for a 20-line
fixture, which is itself worth a separate row. Closing this one requires either
a host with a higher RSS ceiling / a raised `kill_simple_monitor` limit, or a
cheaper way to drive `is_interp_builtin_fn` (a HIR-only entry point) that does
not load the whole compiler into one process.

### Also still not proven (unchanged from the original filing)

Whether the stdlib `eprint` and the prelude builtin differ in stream/buffering,
and whether `print`/`file_write` have sibling shadows.
