# `file_read` infinitely recurses and aborts the process — seed-dependent, any file

- Date: 2026-08-23
- Status: **FIXED 2026-08-23** (see the section at the bottom of this file). The
  original triage below is kept verbatim for its bisect evidence; the header
  line that used to say OPEN, and the "Suggested follow-up" section, are
  superseded by that section. It was previously only WORKED AROUND at the one
  call site that hit it, while remaining a live landmine for every other caller.

> ## READ THIS BEFORE RE-MEASURING ANYTHING IN THIS FILE
>
> **The same source reports the failure two completely different ways depending
> on which engine happens to run it, and nothing in the output says which engine
> ran.** A reproducer that imports nothing gets JIT-compiled, has no recursion
> accounting at all, and smashes the native stack — which reads as "the
> recursion-depth limiter is dead code". Add *any* `std.io_runtime` import and
> the module is demoted to the interpreter (unresolved `runtime_file_rename`),
> where the identical program reports cleanly as
> `recursion depth N exceeded limit N in function 'f'`.
>
> Both were observed in ONE session, and a sibling lane concluded the limiter
> was dead while this lane measured it working — same source, different engine.
> **State the engine with every recursion measurement.** A peer landed
> `SIMPLE_ENGINE_RECEIPT=1` (`47c7ee79b09`, bug record
> `no_engine_receipt_silent_jit_demotion_2026-08-23.md`) for exactly this
> ambiguity: it prints
> `[engine-receipt] engine=<E> requested=<R> demoted=<yes|no> reason=<R|->`
> from inside each engine's own execution entry. **Use it.** Whether the engine
> should also be named in the `StackOverflow` diagnostic text itself is an open
> question worth taking up — see the follow-up list at the end of this file.
- Severity: high — it aborts the process (`SIGABRT`, core dumped), it is not a
  wrong answer you can check for, and `file_read` is one of the most-used
  functions in the tree.

## Symptom

```
fatal runtime error: stack overflow, aborting
```

`rc=134`, core dumped, in under 9 s, with no other output.

## Minimal reproduce

```simple
use std.io_runtime.{file_read}
fn main():
    val s = file_read("/etc/hostname") ?? ""
    print "len={s.len()}"
```

| seed | result |
|---|---|
| `/mnt/fast/cargo-target-run20/release/simple` (2026-08-23 02:01) | **rc=134, stack overflow** |
| `bin/release/x86_64-unknown-linux-gnu/simple` (deployed) | rc=0, `len=3` |

**It is not procfs-specific.** The first reproduce used `/proc/meminfo`, whose
`st_size` is 0, which made a size-based read loop the obvious suspect — but a
plain regular file on a normal filesystem fails identically. Anyone triaging
this should not go looking for a pseudo-file special case.

## Where it comes from

`src/lib/nogc_sync_mut/io/file_ops.spl:76`

```simple
fn file_read(path: text) -> text:
    read_file_text(path)
```

`file_read` is a one-line forwarder to `read_file_text`. If `read_file_text`
resolves back to `file_read` in a given build, that is unbounded mutual
recursion with no base case, which is exactly the observed signature (stack
overflow rather than a hang or a wrong value). The same build emits

```
warning: public function `env_get` has 3 co-compiled definitions with 2 differing
signatures ((text)->Optional(text) vs (text)->text); JIT call sites resolve by
exact arg-type match ... falling back to the last definition when types are
ambiguous — a fallback hit may still dispatch to the wrong one.
[compiler_cross_module_private_symbol_collision]
```

so cross-module symbol collision with last-definition-wins fallback is already
known to be live in this build. `file_read` forwarding to a name that can
collide is the same class. **This has not been confirmed by reading the
resolved symbol table** — it is the leading hypothesis consistent with every
measurement, and whoever fixes it should confirm before changing dispatch.

## How it was found

It took down `main`. Commit `ff095d31591` added a `MemAvailable` clamp for shard
concurrency whose only new I/O was `file_read("/proc/meminfo")`, on the
`native-build` orchestrator path. Every `native-build` then aborted with
`rc=134` before step 0/6 — including a 3-line hello world with `--threads 2`, so
not load-dependent. Reverted in `765f9d2aad4`.

Bisect, by running (each step a real `native-build`, ~9 s to crash):

| variant | result |
|---|---|
| clamp as landed | rc=134 |
| module present, `shard_threads_mem_cap` body → `requested` | rc=124 (no crash) |
| full body, `/proc` read replaced by a constant | rc=124 (no crash) |
| **`file_read` called but its result discarded, never parsed** | **rc=134** |

The last row is the isolation: neither the clamp arithmetic nor the parser is
involved, only the `file_read` call. `SIMPLE_SHARD_MEM_CLAMP=0` also cleared it,
which is what first pointed at the clamp path rather than the 19 other commits
in the window.

## Workaround used

The clamp now reads MemAvailable via `process_run_timeout("awk", ...)` — the same
mechanism `native_build_main.spl` already uses for `readlink` on that exact path,
so it is proven live there. That is a workaround at one call site, **not a fix**.

## Why this matters beyond the clamp

`file_read` is called all over `src/` and `test/`. On any build where this
resolution goes wrong, every one of those call sites aborts the process. The
deployed binary is fine today, so the tree looks healthy; the defect surfaces
only when a particular seed is used, which is precisely how it consumed a
build-blocking incident before being identified.

## Suggested follow-up

1. Confirm the resolution hypothesis by dumping the symbol table for
   `read_file_text` / `file_read` in a build that reproduces.
2. Give the forwarder a unique callee name so it cannot collide, per the
   compiler's own advice in the collision warning.
3. Consider making `compiler_cross_module_private_symbol_collision` fatal for
   the case where a function's resolved callee is itself — self-recursion via
   fallback dispatch is never intended and is statically detectable.

---

## FIXED 2026-08-23 (second lane) — cycle confirmed by construction, not inference

Status above is superseded: **FIXED**. The resolution hypothesis was right and is
now confirmed the only way that matters — by breaking the cycle and watching the
abort disappear on the configuration that actually fails.

### The cycle, exactly

| site | body (before) |
|---|---|
| `src/lib/nogc_sync_mut/io_runtime.spl:163` `read_file_text` | `file_read(path)` |
| `src/lib/nogc_sync_mut/io/file_ops.spl:76` `file_read` | `read_file_text(path)` |

`file_read` has **two** co-compiled definitions (`io_runtime.spl:143`, which is
safe and calls `file_read_result`, and the `file_ops.spl:76` forwarder above).
When last-definition-wins fallback binds `read_file_text`'s call to the
`file_ops` copy, the two forwarders are unbounded mutual recursion with no base
case. Neither name is unique, so nothing in either body is a base case.

### Fix (minimal, semantics-preserving)

Route both forwarders through **uniquely-named** callees, so no dispatch outcome
can re-close the cycle:

- `io_runtime.spl` `read_file_text` and `read_file` now match on
  `file_read_result` (one definition in the tree) instead of calling `file_read`.
- `io/file_ops.spl` `file_read` now matches on `file_read_result` too.

No behaviour changes on any path: all three previously returned
`file_read_result`'s Ok payload or `""`.

### Verified on the configuration that fails

Seed `/mnt/fast/cargo-target-run20/release/simple` (2026-08-23 02:01), engine
**JIT (Cranelift)** — the reproducer emits no `[jit-fallback]` line, so it is
natively compiled, which is also why the failure is a raw `rc=134` smash and not
a diagnostic (see the engine matrix below).

```
# pre-fix
$ simple run tmpso/fr.spl          # file_read("/etc/hostname")
thread 'simple-main' (1883560) has overflowed its stack
fatal runtime error: stack overflow, aborting
timeout: the monitored command dumped core
RC=134

# post-fix, same seed, same file
$ simple run tmpso/fr.spl
len=3
RC=0
```

All five public forwarders green post-fix on that seed:
`file_read=3 read_file=3 read_file_text=3 file_size=3 file_size_raw=3`, rc=0.

### Second, latent instance of the same class — also fixed

`io_runtime.spl:247 file_size_raw -> file_size` and
`io/file_ops.spl:140 file_size -> file_size_raw` is the identical shape;
`file_size` has **10** co-compiled definitions under `src/lib`. It had not fired
on any measured build (`file_size_raw("/etc/hostname")` returns 3 on the run20
seed), so this is a latent landmine hardened pre-emptively, **not** a reproduced
crash. Both halves now call `rt_file_size` / inline the clamp directly.

### Neighbour sweep

Mechanical scan of all 34,418 top-level `fn` names under `src/lib` for
single-expression forwarders whose callee forwards back, restricted to pairs
where at least one name is duplicated (5,234 names are). Seven pairs, all
recorded here so the next lane does not re-derive them:

| pair | status |
|---|---|
| `file_read` (io/file_ops) ↔ `read_file_text` (io_runtime) | **FIXED — this bug** |
| `file_size` (io/file_ops) ↔ `file_size_raw` (io_runtime) | **FIXED — latent** |
| `sha1_init` (common/crypto/sha1) ↔ `create_sha1_context` (crypto/sha1) | open, unverified |
| `is_dir` (gc_async_mut/io/mod_stub) ↔ `dir_exists` (nogc_async_mut/mcp/resources) | open, unverified |
| `is_dir` (nogc_async_mut/io/mod_stub) ↔ `dir_exists` (same) | open, unverified |
| `is_absolute_path` (gc_async_mut/path, nogc_sync_mut/path) ↔ `is_absolute` (nogc_sync_mut/platform) | open, unverified |
| `extract_json_string` ↔ `extract_json_string_v2` (nogc_async_mut/mcp) | open, unverified |

The five open pairs are cross-family (gc/nogc, mcp, crypto) and were **not
reproduced**; they are the same shape and should be hardened the same way, but
that is a separate change against modules this lane did not touch. Changing them
blind would have been unverifiable churn.

**What the next lane needs to do for each — you do NOT need to redo the census.**
The census that produced this list is: every top-level `fn` under `src/lib`
(34,418 names), keep those whose body is a single expression that is a bare call,
build the forwarder edge `name -> callee`, and report any pair where the callee
also forwards back, restricted to pairs where at least one of the two names has
more than one definition (5,234 names do). The seven pairs above are its complete
output; the five below are what is left.

Per pair, the verification is three cheap steps:

1. **Confirm the cycle is real in source** — read both bodies and check that
   neither is a base case. A forwarder pair is only dangerous when *both* halves
   forward; if one half calls an extern or has a real body, that half terminates
   the cycle and the pair is benign.
2. **Confirm the names actually collide** — `grep -rn "^\(pub \)\?fn <name>(" src/lib`
   and count definitions. Two same-named definitions with the SAME arity/signature
   are what makes last-definition-wins reachable; differing signatures are
   resolved by exact arg-type match first and are much less likely to misfire.
3. **Try to reproduce on a seed that exhibits the class** — a 4-line `simple run`
   program calling the public entry point, run on a run20-class seed. `rc=134`
   with no output is the signature. **A green result here does not clear the
   pair** — `file_size_raw` came back green and was still fixed, because
   whether dispatch picks the fatal copy is a property of the build, not of the
   source. Green means "latent", not "safe".

Then apply the same fix shape: route each forwarder through a **uniquely-named**
callee (or inline the body / call the extern directly), so no dispatch outcome
can close the cycle.

| pair | what to check specifically |
|---|---|
| `sha1_init` ↔ `create_sha1_context` | two different sha1 implementations (`common/crypto/sha1.spl` vs `crypto/sha1.spl`). Check whether these are genuinely the same API or an intentional facade over two hash backends — if the two modules are never co-compiled the pair cannot close, and that is worth establishing first |
| `is_dir` ↔ `dir_exists` (two pairs: `gc_async_mut/io/mod_stub.spl` and `nogc_async_mut/io/mod_stub.spl`, both against `nogc_async_mut/mcp/resources.spl`) | `mod_stub` files are stubs; confirm whether either is live in any build or is dead scaffolding. If dead, deletion is the better fix than rerouting. Note both stubs point at the SAME `resources.spl` definition, so one fix on the `resources.spl` side may close both |
| `is_absolute_path` ↔ `is_absolute` | two `is_absolute_path` definitions (`gc_async_mut/path.spl`, `nogc_sync_mut/path.spl`) against one `is_absolute` in `nogc_sync_mut/platform.spl`. This is the pair most likely to be genuinely reachable, since path handling is used by everything including the driver — check it first |
| `extract_json_string` ↔ `extract_json_string_v2` | a `_v2` suffix suggests a deliberate migration shim. Establish which direction is intended to be authoritative; if `_v2` is the real implementation, the plain name should forward to it and `_v2` must not forward back |

### Regression test

`test/01_unit/lib/io_runtime/file_read_forwarder_no_self_recursion_spec.spl`,
9 examples. **Honest limitation, stated rather than papered over:** the seven
behavioural examples pass on BOTH sides of the fix under `simple test` — that
harness resolves the duplicates correctly and never reproduced the abort, which
is exactly why the defect survived. The two added **source-invariant** examples
are the ones that discriminate, because the cycle is a static property of the
two bodies rather than of one dispatch outcome:

```
# pre-fix (libs reverted, spec present), deployed binary
✗ std.io_runtime.read_file_text does not forward to the ambiguous name file_read
  expected true to equal false
✗ io.file_ops.file_read does not forward to the ambiguous name read_file_text
  expected true to equal false
Results: 9 total, 7 passed, 2 failed

# post-fix
Results: 9 total, 9 passed, 0 failed
```

## Why it aborted instead of reporting: the recursion limiter is engine-dependent

The sibling question — is `rc=134` or `recursion depth 1000 exceeded` the
expected failure? — has a measured answer, and it is **per engine**. Same seed,
same source shape, forced limit `SIMPLE_MAX_RECURSION_DEPTH=10`:

| engine | runaway recursion | verified |
|---|---|---|
| Rust seed, **interpreter** | `error: stack overflow: recursion depth 10 exceeded limit 10 in function 'f'`, rc=1 — clean, env-tunable | yes, this lane |
| Rust seed, **JIT (Cranelift)** | `fatal runtime error: stack overflow, aborting`, rc=134, core dumped. 5,000 frames deep with the limit set to 10 and detection explicitly on | yes, this lane |
| pure-Simple self-hosted | `recursion depth 1000 exceeded limit 1000 in function 'file_rename'`, clean | peer lane |
| native AOT | not measured | no |

So the limiter is **not** dead, as an earlier reading of this suggested — the
single `push_call_depth` site
(`compiler/src/interpreter_call/core/function_exec.rs:634` →
`interpreter_state.rs:789`) is on the interpreter's function-body path only.
JIT-compiled code uses real machine frames and is never accounted, so it smashes
the stack. The trap for anyone re-measuring: a reproducer that imports nothing
gets JIT-compiled and shows "the guard is dead"; adding any `std.io_runtime`
import drops the module to the interpreter (unresolved `runtime_file_rename`)
and the same program then reports cleanly. Both were observed in one session.

**Not fixed here, filed instead** (each is larger than a semantics-preserving
edit and touches the seed's codegen or its global state):

1. **JIT/native lanes have no recursion accounting at all.** Making `rc=134` a
   readable diagnostic there means emitting a depth check per call in codegen —
   a real cost/design decision, not a minimal fix. Until then, any runaway
   recursion reached through JIT-compiled code aborts without naming a function,
   which is precisely why this bug cost a build-blocking incident to identify.
2. **`RECURSION_DEPTH` is process-global, not thread-local**
   (`src/compiler_rust/common/src/fault_detection.rs:13`, documented as "not
   per-thread for simplicity"). Under sharded work the limit is wrong in both
   directions: unrelated threads' frames sum into one counter (spurious fires),
   and a genuinely deep single thread can be masked. The 64 MB stack the default
   limit of 1000 is calibrated against belongs to the `simple-main` thread
   (`driver/src/main.rs:1100`); threads spawned without an explicit
   `.stack_size` get the 2 MB default, so 1000 interpreter frames is not
   necessarily survivable there.
3. **Name the engine in the diagnostic itself.** `CompileError::StackOverflow`
   (`compiler/src/error.rs:514`) prints depth, limit and function but not which
   engine produced it — and the engine is precisely the axis that decides
   whether you get that message at all. Folding the `engine_receipt` value into
   the text (or emitting the receipt alongside every stack-overflow abort) would
   have removed a whole session's worth of contradictory measurements. Raised
   with the `47c7ee79b09` lane rather than done here, since it is their
   mechanism.
4. `driver/src/cli/init.rs:248 init_stack_overflow_detection` is wired
   (`init_runtime`, `main.rs:1189`) and its env knobs
   `SIMPLE_STACK_OVERFLOW_DETECTION` / `SIMPLE_MAX_RECURSION_DEPTH` do work —
   on the interpreter. They are silently inert on the JIT path, per (1).

## This is one defect FAMILY, not four unrelated bugs (2026-08-23)

Four separate incidents landed on the same day, all of them "a name resolved to
the wrong definition":

1. **`file_read` mutual recursion** — this bug. Two co-compiled `file_read`
   definitions; last-definition-wins closed a forwarder pair into infinite
   recursion and aborted the process.
2. **`file_rename` facade** — a peer lane's alias resolution made the
   interpreter resolve an alias back into its own caller, reported as
   `recursion depth 1000 exceeded limit 1000 in function 'file_rename'`. Fixed
   at origin as `fix(interp): resolve aliased imports of multiply-defined
   names` — note the commit title names the *general* condition, multiply-defined
   names, which is exactly this family.
3. **`rt_mem_snapshot_*` cross-crate** — same shape across crate boundaries.
4. **token-kind space mismatch** — the same failure at the type level rather
   than the symbol level.

Treating these as four unrelated bugs under-counts the risk. The common cause is
that **a duplicated name plus a fallback dispatch rule is a silent
mis-resolution machine**, and the failure mode it produces is arbitrary: infinite
recursion here, a wrong-but-plausible value elsewhere, a crash somewhere else.
The compiler already knows when this happens -- it emits
`compiler_cross_module_private_symbol_collision` -- but the warning is advisory
and the fallback proceeds anyway. The durable fix for the family is upstream of
any individual call site: make a resolved-callee-equals-self edge a hard error
(it is statically detectable and never intended), and consider making the
collision warning fatal where the candidates have identical signatures, since
that is precisely the case where "exact arg-type match" cannot discriminate and
the fallback is a coin flip.

## Process hazard found while verifying this fix (worth more than the fix)

Three pre-push guards were run against **the wrong repository** and returned
meaningless PASSes. The shell cause is specific and will recur:

```sh
cd X && setsid nohup sh -c '...' &   disown; sleep 2; for g in ...; do ... done
```

The `&` binds the **entire** `cd X && setsid ...` chain into the background job,
so the foreground `for` loop runs in the *session* cwd, not `X`. The guards were
read-only so nothing was disturbed, but their verdicts described a different
tree than the one being pushed.

It was caught only because `check-no-conflict-tree-push` prints the repo and the
commit count it examined -- `repo /mnt/data/worktrees/simple-main, 5 commit(s)`
instead of `repo /mnt/fast/wt/stackoverflow-1, 1 commit(s)`. Two rules follow:

1. **Run guards with an explicit absolute path / `-C`**, never relying on an
   inherited cwd, and never with a `cd` that a `&` can capture.
2. **Trust only verdicts that name the subject they examined.** A guard that
   prints `PASS` without stating which repo, which range, and how many commits
   or files it checked cannot be audited, and a wrong-scope run is
   indistinguishable from a real one. This is a concrete argument for making
   *every* guard print its scope, not just the three that already do.
