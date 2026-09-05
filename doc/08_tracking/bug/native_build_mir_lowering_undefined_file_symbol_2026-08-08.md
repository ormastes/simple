# `native-build` MIR lowering fails to resolve `File`/`FileHandle` symbols for the `rt_io_file_roundtrip` fixture — reached, decisive, reproducible

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Summary

The AOT (`native-build`, true LLVM codegen) leg of
`scripts/check/check-rt-io-file-native-jit-stub.shs` was previously
UNDETERMINED because every attempt stalled during parsing before reaching
codegen (see
`doc/08_tracking/bug/entry_closure_runs_global_stdlib_pass_regardless_of_imports_2026-08-08.md`,
"Update 2026-08-08c"). This session gave the direct-worker recipe a full
1800s budget instead of ≤590s. **Parsing DOES finish — confirmed
slow-but-finite, not a stall — but the build then fails with a genuine MIR
lowering error before reaching codegen.** So the original question ("is
`rt_io_file_*` stubbed under AOT?") is still not directly answerable, but for
a sharper, now-fully-characterized reason: the fixture never compiles at all
under `native-build` today, independent of the `rt_io_file_*` question.

## Repro

```
env SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1 \
    SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING=1 SIMPLE_COMPILER_TRACE=1 \
    SIMPLE_EXECUTION_MODE=interpret \
    stdbuf -oL -eL timeout 1800 bin/release/x86_64-unknown-linux-gnu/simple \
    run src/app/cli/native_build_worker.spl \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure --entry test/fixtures/rt_io_file_roundtrip/main.spl \
    --cache-dir <scratch>/cache -o <scratch>/out.o --emit-object
```

Same recipe as Update 2026-08-08b/c in the entry-closure doc, just given a
much larger (1800s) budget via `nohup ... &` + background polling instead of
a single foreground tool call (the agent Bash tool caps a single call's
`timeout` param at 600000ms/10min, which is why nobody had run this past
~590s before).

## What happened (full timeline, elapsed ms from process start)

| elapsed | event |
|---|---|
| — | closure BFS: 6 files (main.spl + 5 stdlib deps), ~5s, matches prior findings |
| +88,806ms | `phase2:parse:file:done` for `main.spl` (2155 chars) |
| +509,936ms | `phase2:parse:file:done` for `src/std/nogc_sync_mut/io/file.spl` (16723 chars) — **421.1s just for this one file's parse**, confirming Update 2026-08-08c's localisation |
| +583,632ms | `phase2:parse:file:done` for `src/std/common/io/types.spl` (10315 chars) — only 73.7s (**139.9 chars/s**, ~4-5x faster per-char than file.spl) |
| +609,614ms | `phase2:parse:file:done` for `src/lib/common/io/traits.spl` (4959 chars) — 26.0s (190.8 chars/s) |
| +927,789ms | `phase2:parse:file:done` for `src/std/common/string_core.spl` (11698 chars) — **318.2s (36.8 chars/s)**, comparably slow to file.spl despite being smaller |
| +988,282ms | `aot:lower_to_mir:module:done` idx=0 `test.fixtures.rt_io_file_roundtrip.main` (functions=1) |
| +1,022,344ms | `aot:lower_to_mir:module:done` idx=1 `std.nogc_sync_mut.io.file` (functions=31) |
| +1,026,606ms | `aot:lower_to_mir:module:done` idx=2 `std.common.io.types` (functions=8) |
| +1,026,671ms | `aot:lower_to_mir:module:done` idx=3 `lib.common.io.traits` (functions=0) |
| +1,047,749ms | `aot:lower_to_mir:module:done` idx=4 `std.common.string_core` (functions=40) |
| (immediately after) | a burst of `[ERROR] MIR error: MIR lowering error: ...` lines, then final `error: MIR lowering error: undefined variable: File` and the process exits |

Total: **~1080s (18 minutes) to a definitive, reproducible failure** — not a
timeout (rc came from the process exiting on its own inside the 1800s
budget, not from the `timeout` wrapper).

**Key finding #1 — parsing is slow-but-finite, and the per-char cost is NOT
uniform across files of similar size.** `file.spl` (16723 chars, 421s,
39.7 chars/s) and `string_core.spl` (11698 chars, 318s, 36.8 chars/s) parse
at a similar (slow) rate to each other, while `types.spl` (10315 chars, 74s,
139.9 chars/s) and `traits.spl` (4959 chars, 26s, 190.8 chars/s) parse
3.5-5x faster per char. `file.spl` and `string_core.spl` are both
class/function-dense (31 and 40 lowered functions respectively vs. 8 and 0
for the faster two), so the cost tracks declaration/expression density, not
raw character count — this is consistent with, and sharpens, the
"interpreter dispatch tax" explanation already on record in
`entry_closure_runs_global_stdlib_pass_regardless_of_imports_2026-08-08.md`,
and argues against a naive quadratic-in-file-length theory (no truncation
experiment was needed once real cross-file rate data was in hand — the
non-uniform per-char rate across files of comparable size is itself
sufficient to rule out "it's just O(n^2) on character count").

**Key finding #2 — the real, previously-unreached blocker: MIR lowering
fails to resolve `File`.** The error lines' variable names (`h`, `c`, `n`)
line up exactly with `main.spl`'s own `case Ok(h)`, `case Ok(c)`,
`case Ok(n)` bindings (see `test/fixtures/rt_io_file_roundtrip/main.spl`
lines 18, 43, 48). The `write_text`/`close`/`read_text`/`size`/`read_all`/
`write_all`/`merge` unresolved-method-call errors correspond to methods
`main.spl` calls directly (`write_text`, `close`, `read_text`, `size`) AND
methods that do NOT appear in `main.spl` at all (`read_all`, `write_all`,
`merge`) — those must come from `file.spl`'s own 31 lowered functions
referencing sibling `FileHandle`/`File` methods internally. The final fatal
line is `error: MIR lowering error: undefined variable: File` — `File` is
the class `main.spl` uses for `File.delete(path)` / `File.exists(path)`
(lines 15, 33) and is exported at `src/lib/nogc_sync_mut/io/file.spl:561`
(`export FileHandle, File`), so the class genuinely exists and is exported;
this is a symbol-resolution ordering/registration bug in `native-build`'s
MIR lowering, not a missing declaration. Module lowering order was
idx=0 (`main`) **before** idx=1 (`file`) finished — i.e. the entry module is
MIR-lowered before its dependency's declarations are fully registered for
cross-module lookup, which is consistent with `main.spl`'s own references to
`File` failing to resolve.

## Why this matters for the `rt_io_file_*` AOT stub question

**The build never reaches codegen for this fixture.** So whether
`rt_io_file_*` is stubbed or wired correctly under true AOT/LLVM codegen
remains genuinely UNDETERMINED — but the reason has changed from "nobody
gave it enough wall-clock" (false, per Update 2026-08-08c and now fully
confirmed here: parsing alone takes ~1048s to complete, not more) to "the
fixture doesn't compile under `native-build` today, for a reason unrelated
to `rt_io_file_*`, and unresolved so far." Fixing the MIR-lowering
symbol-resolution ordering bug is a prerequisite for ever answering the
original stub question for this fixture via `native-build`.

## Scope note

Per task instructions, no attempt was made to fix the MIR-lowering ordering
bug or the parser performance characteristics in this session — both are
characterized and filed here for someone else to pick up. Do not attempt a
parser fix as a side effect of picking up the stub question again; the two
are separable (the MIR-lowering bug blocks reaching codegen regardless of
parse speed, and would need fixing even if parsing were instant).

## Next steps

1. Fix (or at least explain) the MIR-lowering module-ordering issue: why is
   the entry module (`main`) lowered to MIR before its dependency
   (`std.nogc_sync_mut.io.file`) finishes, and why does that cause
   `File`/`FileHandle` symbol lookups from `main`'s body to fail instead of
   being deferred/resolved via a second pass. Compare against the minimal
   `FileMode`/`SeekFrom`-only fixture from Update 2026-08-08b, which DID
   reach codegen successfully with 2 closure modules — the difference there
   is `main` didn't reference any *class* from the dependency, only enum
   variants, which may take a different (working) resolution path.
2. Separately, the per-char parse-rate variance above (27-40 chars/s for
   declaration-dense files vs. 140-190 chars/s for lighter ones) is worth a
   real profile (flamegraph/perf) of the forced-interpret parse path if
   `native-build`'s reliance on the tree-walk interpreter for its own
   compiler passes is to remain the default — out of scope here, not fixed.
3. Once (1) is fixed, re-run the exact repro above (or the fence script's
   AOT leg) to get the actual stub/no-stub verdict for `rt_io_file_*`.

## Evidence

Full trace log (24,369 lines,
`SIMPLE_COMPILER_TRACE=1` + closure timing) captured this session; timings
above are direct quotes of its `[BOOTSTRAP-PHASE]` markers. Not attached to
this doc (too large) — reproducible via the exact command above in ~18
minutes.

## RESOLVED 2026-08-09 — root cause was a Dict-method-name collision, not a
## cross-module lowering-order bug

The "module lowering order idx=0 (`main`) before idx=1 (`file`)" framing
above is **falsified**. Discriminating evidence: `File.exists(path)` (same
call chain, same module-lowering order, a genuinely non-resolved-ahead-of-
time static method) resolved fine; only `File.delete(path)` failed. If this
were an ordering bug, both calls would fail identically.

Actual root cause: `lower_method_call`
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, dict-probe
block around line 1230) treats any Unresolved-resolution method call named
`delete`/`get`/`has`/`keys`/`values`/`contains`/`contains_key`/`remove` as a
candidate Dict method and unconditionally calls `self.lower_expr(receiver)`
to probe whether the receiver is a runtime `Dict` — **before** the
static/class-receiver dispatch logic further down gets a chance to run.
`File` is a bare class-name reference (`NamedVar`), never a runtime value;
`Var`/`NamedVar` lowering (`expr_dispatch.spl`) has no "this names a
class" case (only locals, module globals, and two hardcoded named
constants), so probing it as an ordinary expression fell straight through
to the generic "undefined variable" error. `File.exists` didn't collide
with any Dict method name, so it skipped this probe entirely and reached
the correct static-dispatch path further down (`Unresolved` arm,
`static_receiver_name`-keyed lookup) — which is exactly why one call in the
same chain succeeded and the other failed identically-ordered.

Fix: gate the dict-probe block on `static_receiver_name == ""` (computed
earlier in the same function from the receiver's HIR symbol kind —
non-empty iff the receiver is a bare Class/Struct/Enum/Import name). A
class-name receiver can never be a Dict instance, so the probe is safely
skipped and control reaches the existing static-method dispatch logic,
which already resolves the call correctly via `struct_method_syms` or the
`self.symbols.lookup_method_in_type` fallback — neither of which is
ordering-sensitive.

Verified:
- Minimal 2-module fixture (`FileThing` class with static `delete`/`exists`,
  entry module importing and calling both) — before the fix: `undefined
  variable: FileThing`; after: `rc=0`, object file emitted.
- Real Dict operations (`d["a"]=1`, `d.delete("a")`, `d.has("b")`) combined
  with a colliding-named static method (`Thing.delete(...)`) in the same
  module — `rc=0`, both dispatch correctly (no regression to genuine Dict
  method resolution).
- Full original repro (`rt_io_file_roundtrip/main.spl` through the real
  `src/compiler`+`src/app`+`src/lib` closure, ~18 minutes to a definitive
  result twice, same recipe as above): `undefined variable: File` is GONE.
  The build now progresses past the `File`-class calls (`File.delete`,
  `File.exists`) and reaches a **different, later** failure: `undefined
  variable: h` (the `FileHandle` local bound via `case Ok(h): h`) plus a
  cluster of `unresolved method call:` errors for `FileHandle` INSTANCE
  methods (`write_text`, `close`, `read_text`, `size`, `read_all`,
  `write_all`, `merge`). That is the pre-existing "native-build can't
  resolve a struct instance method without HIR type inference" gap
  documented inline at `method_calls_literals.spl`'s `Unresolved` arm
  (bug #138/#156) — a distinct, separable defect from this one. The
  original `rt_io_file_*` AOT-stub question (whether `rt_io_file_*` is
  stubbed under true LLVM codegen) is therefore **still undetermined**, now
  blocked on the FileHandle instance-method-resolution gap instead of this
  one. Not fixed here — out of scope for this fix, filed as a distinct
  follow-up.

Fix landed in `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
(one-line gate + doc comment on the existing dict-probe condition).
