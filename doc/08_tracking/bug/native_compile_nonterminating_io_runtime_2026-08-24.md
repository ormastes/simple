# `native-build` of an `io_runtime` importer does not terminate in `native_compile`

**Status:** RESOLVED 2026-08-24 — FIFTH blocker in the `io_runtime` native-build chain
**Successor:** blocker #6, `native_compile_explicit_panic_diverging_process_ops_2026-08-24.md`
**Observed:** 2026-08-24
**Area:** 70.backend `_MirToLlvm` (native_compile stage), seed tree-walk interpreter
**Predecessor:** `hir_block_value_type_decayed_object_to_int_2026-08-24.md`
(blocker #4, RESOLVED `be3e6fe4a21`)

## Position in the chain

Blockers 1-4 are fixed. With `9e3eb1adccd`, `838f5e2e08c` and `be3e6fe4a21`
landed, the `io_runtime` control program no longer fails — it **hangs**.

## Reproduction

Seed rebuilt from the fixed tree (`cargo build --release --bin simple`,
`BRC=0`). Exit codes read DIRECTLY into a variable on the line after the
command, never through a pipe.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ timeout 3600 "$SEED" native-build lanework/control.spl -o lanework/control.bin > fix2.log 2>&1
$ NB_RC=$?
NB_RC=124            # 124 == timed out at 3600s
$ grep -c "E-HIR-BLOCK-VALUE-TYPE-DECAYED" fix2.log
0
$ grep -c "cannot convert object to int" fix2.log
0
```

Last progress line, then ~59 minutes of silence:

```text
[build] native_cache 7/7 step 5/6 +11510ms dt=1ms complete
[build] native_compile 2/7 step 5/6 +11510ms dt=0ms lanework.control
```

## Evidence that it is a spin, not slow progress

Measured on the live worker (`src/app/cli/native_build_worker.spl`):

- CPU time tracked elapsed time 1:1 for the whole run (`00:52:45` CPU at
  `52:46` elapsed) — pegged at 100% of one core.
- `VmRSS` flat at ~2,191,100 kB for the last 30+ minutes.
- `/proc/<pid>/io` **completely unchanged** across a 30s sample:
  `rchar: 196686577`, `wchar: 509946`, `syscr: 29406`, `syscw: 2122` before and
  after. Zero I/O progress.
- Worker stderr stopped growing at 36,920 bytes.

Pure compute with no allocation growth and no I/O is the signature of a loop
that is not converging, not of a large module graph still being lowered.

## This is NOT a regression from the blocker-#4 fix

The blocker-#4 fix replaced a raw `MirInstKind.LoadGlobal` payload decode with
typed `MirInst` accessors in
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`. That change is
independently verified not to break `native_compile`:

```text
$ timeout 540 "$SEED" native-build lanework/hello.spl -o lanework/hello.bin
$ HRC=$?
HELLO_NB_RC=0
$ ./lanework/hello.bin
hello
$ RUN_RC=0
```

A plain hello-world native-builds to a working, running binary on the same
binary that hangs on the `io_runtime` importer. Before the fix the
`io_runtime` case could not reach this stage at all — it died at
`native_compile 1/7` in ~21s with `cannot convert object to int` — so there is
no earlier terminating behaviour that was lost.

## Not yet measured

Where in `_MirToLlvm` the loop sits. Attach-based profiling is blocked on this
host (`ptrace_scope=1`, `perf_event_paranoid=4`), so the next step is a
level-gated iteration/progress counter in the `native_compile` instruction walk
rather than a profiler.

## Gate

Fenced by `scripts/check/check-hir-block-tail-and-loadglobal-decode.shs`.
Following the honest-gate precedent, the DEFAULT assertion is
signature-absence, not exit 0 — a gate that is red at birth pins nothing, since
a real blocker-#4 regression and this hang would both exit 1 and be
indistinguishable without reading prose. The residual exit status is therefore
NAMED IN THE VERDICT LINE instead of being asserted away, and `--require-success`
turns exit 0 into a hard assertion; flip that on as the default once this bug
lands.

Both modes measured end to end (`BUILD_TIMEOUT=300`), verbatim:

```text
$ BUILD_TIMEOUT=300 sh scripts/check/check-hir-block-tail-and-loadglobal-decode.shs
$ GATE_RC=$?
GATE_RC=0
selftest: 8 fixture(s) passed
PASS - 2 case(s) checked, 0 E-HIR-BLOCK-VALUE-TYPE-DECAYED and 0 object-to-int; native-build exited 124, NOT success -- blocker #5 is open (doc/08_tracking/bug/native_compile_nonterminating_io_runtime_2026-08-24.md); pass --require-success to assert exit 0

$ BUILD_TIMEOUT=300 sh scripts/check/check-hir-block-tail-and-loadglobal-decode.shs --require-success
selftest: 8 fixture(s) passed
FAIL - 2 case(s) checked, both fenced signatures are absent but native-build exited 124 and --require-success was given
GATE_STRICT_RC=1
```

Selftest fixture F4c pins that a DECAYED regression still outranks a non-zero
exit, so the residual-exit allowance can never mask a real regression.

## Operational note

`timeout` kills the `native-build` parent but the `native_build_worker.spl`
child SURVIVES as a ~2.1 GB, 100%-CPU orphan. Three were reaped by hand after
this investigation. Anyone reproducing this should check
`pgrep -af native_build_worker.spl` afterwards.

## Also still open (independent, measured on the same pass)

- `std.common.text` — `MIR lowering error: unresolved method call: index_of`
- `std.nogc_sync_mut.fs` — `MIR lowering error: undefined variable Dir`


---

# RESOLUTION (2026-08-24)

## Root cause — an EXPONENTIAL DFS, not an infinite loop

`ssa_block_can_reach` in `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`
was a recursive depth-first search that threaded its `visited` set **DOWN each
branch**:

```simple
val seen = visited.push(start_id)
for succ_id in ssa_terminator_successors(start_block.terminator):
    if ssa_block_can_reach(blocks, succ_id, target_id, seen):
        reached = true
```

Because `seen` is a fresh per-branch copy, sibling successors never observe each
other's marks. Nothing is memoized across the search, so **every distinct path
through the CFG is re-explored**: O(2^branches). The loop over successors also
never short-circuits once `reached` is true, which compounds it.

This is why the defect presented as a HANG rather than a crash: the search does
terminate in principle, so there is no error, no allocation growth and no I/O —
it simply does not finish. Every measured characteristic in the original report
follows directly:

| measured | explained by |
|---|---|
| CPU 1:1 with elapsed, 100% of one core | pure recursive compute |
| `VmRSS` flat at ~2,191,100 kB | each branch's `seen` copy is freed on return; depth is bounded by the block count |
| `/proc/<pid>/io` byte-identical | no I/O is performed |
| hello-world unaffected | callers gate on `blocks.len() < 4` |

## Where it loops — localized by ungated progress probes

Attach-based profiling is blocked on this host, so the loop was found by
bisecting with temporary probes (all removed before commit). The chain:

```text
[probe] compile_begin std.nogc_sync_mut.io.process_ops
[probe] ssa:start process_run_timeout_live
[probe] ssa:enter blocks=94 locals=504
[probe] ssa:alloca-done applied=false reason=unsupported instruction
[probe] B1 phi_required_locals-begin blocks=94      <-- never returned
```

`llvm_bootstrap_ssa_function` -> (alloca transform REJECTS with "unsupported
instruction") -> `ssa_var_transform_blocks` ->
`ssa_phi_required_locals_for_blocks` -> `ssa_safe_join_predecessors` ->
`ssa_forward_join_predecessors` -> `ssa_block_can_reach`.

The hanging input is `process_run_timeout_live`
(`src/lib/nogc_sync_mut/io/process_ops.spl:359`) — **94 blocks, 504 locals**.

A heisenbug worth recording: `SIMPLE_BOOTSTRAP_DEBUG=1` made the hang vanish.
That is not luck — the debug branch in
`70.backend/backend/_MirToLlvm/core_codegen.spl` takes an entirely different
`if bootstrap_debug: ... else: ...` arm that never calls
`llvm_bootstrap_ssa_function`. Do not read a green run under that env var as
evidence about this path.

## Fix

`ssa_block_can_reach` is now an **iterative worklist** over a single shared
`seen` set, with an early return the moment `target_id` is seen. Semantics are
unchanged: for a reachability predicate, a block already expanded without
reaching the target cannot reach it by a different path either, so sharing the
visited set across siblings is exactly equivalent. Complexity goes from
O(2^branches) to O(V+E) (with a linear `local_list_contains`, O(V*E) — trivial
at these sizes).

## Proof — exit codes read DIRECTLY into a variable on the line after the command

```text
$ timeout 600 "$SEED" native-build lanework/control.spl -o lanework/control.bin
$ NB_RC=$?
NB_RC=1     elapsed=181s      # was 124 (timed out) at 3600s
```

The hang is gone: the compile now **terminates in 181 s**, and
`process_run_timeout_live` passes the previously non-returning stage instantly
(`B1` -> `B2 phi_locals=2`).

No regression on the path that already worked:

```text
$ timeout 600 "$SEED" native-build lanework/hello.spl -o lanework/hello.bin
$ HELLO_NB_RC=$?
HELLO_NB_RC=0
$ ./lanework/hello.bin
hello
$ RUN_RC=$?
RUN_RC=0
```

`cargo check --release --bin simple` — green.

## HONEST STATUS: a SIXTH blocker is exposed underneath

`NB_RC=1`, **not 0**. Removing the hang revealed the next defect in the chain:

```text
error: explicit panic() -- diverging, must not fall through
error: semantic: panic: compile error: explicit panic() -- diverging, must not fall through
```

Filed as `native_compile_explicit_panic_diverging_process_ops_2026-08-24.md`.
Blocker #5 (this record) is genuinely fixed and is fenced on its own mechanism;
it is not being closed by treating blocker #6's exit 1 as success.

**Therefore `--require-success` in
`scripts/check/check-hir-block-tail-and-loadglobal-decode.shs` is deliberately
NOT flipped on** — that flag asserts exit 0, which is still false. Flip it when
blocker #6 lands, not now. Flipping it here would make a red gate the default
and pin nothing.

## Gate

`scripts/check/check-ssa-block-reach-not-exponential.shs` — fail-closed, verdict
last, `--selftest` first and fatal (7 fixtures). Two checks:

1. **Mechanism** (always, milliseconds): `ssa_block_can_reach` must not call
   itself. The exponential form is recursive by construction, so this catches a
   reintroduction without waiting on a 3-minute build. A self-mention inside a
   comment does not count (fixture F5), and the function going missing is
   ERROR, never a silent pass (F3/F4).
2. **Behaviour** (`--with-build`, minutes): native-build an `io_runtime`
   importer **under `timeout`** and classify `rc=124` as a distinct HANG FAIL.
   The timeout is the point — a non-terminating compile has no exit code until
   something kills it, so a gate without one would hang forever instead of
   failing. Following the honest-gate precedent, this asserts NON-HANG and
   NAMES the residual exit status rather than asserting exit 0;
   `--require-success` adds that assertion once blocker #6 lands.

Mutation-tested, verbatim:

```text
$ sh scripts/check/check-ssa-block-reach-not-exponential.shs
selftest: 7 fixture(s) passed
PASS - 1 check(s) run, `ssa_block_can_reach` is iterative (single shared `seen`, no per-branch copy); behavioural check not requested (pass --with-build)
RC1=0

# mutation: restore the recursive form
FAIL - 1 check(s) run; ssa_block_can_reach is recursive again (per-branch `visited` copy => O(2^branches)) -- see doc/08_tracking/bug/native_compile_nonterminating_io_runtime_2026-08-24.md
RC2=1

# mutation: rename the function away
ERROR - nothing was checked (could not read `fn ssa_block_can_reach` in src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl)
RC3=2

$ SEED=... BUILD_TIMEOUT=600 sh scripts/check/check-ssa-block-reach-not-exponential.shs --with-build
selftest: 7 fixture(s) passed
PASS - 2 check(s) run, `ssa_block_can_reach` is iterative (single shared `seen`, no per-branch copy); native-build terminated with exit 1 within 600s (NOT a hang)
GATE_RC=0
```
