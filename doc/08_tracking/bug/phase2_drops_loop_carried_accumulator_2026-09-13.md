# P0: phase 2 silently drops a loop-carried accumulator update

**Filed:** 2026-09-13
**Lane:** phase 2 only (the pure-Simple Stage 2 compiler). Phase 1 (Rust seed) is correct on **both** its backends.
**Severity:** P0 — wrong answers, exit 0, no diagnostic. This is the worst failure shape a compiler has.

## Symptom

```simple
fn main() -> i64:
    var s = 0
    var i = 1
    while i <= 10:
        s = s + i
        i = i + 1
    print "sum={s} i={i}"
    0
```

| compiler | output |
|---|---|
| phase 1 seed (`run`) | `sum=55 i=11` |
| phase 1 seed, `--backend=cranelift` | `sum=55` |
| **phase 2** | **`sum=0 i=11`** |

The loop executes the right number of times — `i` is 11, so the condition, the
counter update and the back-edge are all fine. Only the accumulator assignment
is dropped. There is no error, no warning, and the process exits 0.

## Trigger

A loop-carried mutation whose right-hand side reads **both** the mutated
variable **and** the loop-condition variable.

| probe | shape | phase 2 |
|---|---|---|
| `a = a + 1` | reads only itself | **correct** |
| `last = i` | reads only the counter | **correct** |
| `s = s + i` | reads **both** | **dropped** |
| `s = s + add(i, i*2)` | both, via a call | **dropped** |
| `xs.push(i)` in a loop | both | **dropped** (`n=0`) |

So neither operand alone is enough; it is the combination.

## Not a backend bug, and not the link shim

- Phase 1 is correct on LLVM **and** on `--backend=cranelift`, so the shape
  itself is not miscompiled by either backend.
- Phase 2 is wrong on both of its own lanes — cranelift-direct and its
  `--backend=llvm` cache object — which places the fault in phase 2's own
  lowering, above the backend.
- The probes are runtime-call-free integer loops, so the hand-link shim used to
  produce a runnable binary cannot account for it.


## Self-contained reproduction

An earlier revision of this record pointed at `build/p2run/**`. That path is
covered by `.gitignore`, so those files reach nobody else and the instructions
were unfollowable even though the measurements behind them were real. The probe
source is inlined here instead, and the harness is described rather than
referenced.

Save the probe below, then, with the MSVC toolchain sourced
(`. ./scripts/setup/windows-msvc-bootstrap-env.shs`):

1. `<phase2-simple.exe> compile --format=smf <probe>.spl` — phase 2 cannot
   finish a `native-build` while the capsule-receipt defect stands, so stop at
   the object.
2. Link the emitted `.o` with the runtime archives
   (`simple_runtime.lib` from the stage2 runtime authority and the
   `core_c_runtime` one) plus the usual Win32 system libraries, using
   `link.exe -SUBSYSTEM:CONSOLE -FORCE:MULTIPLE`.
3. Run it, and run the same source through the Rust seed
   (`<seed> run <probe>.spl`) as the phase 1 control.

```simple
# probe: loop-carried accumulator, proved WITHOUT printing the number
fn main() -> i64:
    var s = 0
    var i = 1
    while i <= 10:
        s = s + i
        i = i + 1
    if s == 55:
        print "SUM_IS_55"
    else:
        print "SUM_NOT_55"
    if s == 0:
        print "SUM_IS_ZERO"
    if i == 11:
        print "COUNTER_OK"
    0
```

Branching rather than printing matters: `str()` is separately broken in this
lane (see `phase2_str_returns_raw_pointer_2026-09-13.md`), so a printed number
would not have settled anything. phase 1 answers `SUM_IS_55 | COUNTER_OK`;
phase 2 answers `SUM_NOT_55 | SUM_IS_ZERO | COUNTER_OK`.

## Reproduction (original harness, local only)

Phase 2 cannot finish a `native-build` (see the capsule-receipt defect,
`phase2_file_size_garbage_breaks_capsule_receipt_2026-09-13.md`), so the object
is emitted with `compile --format=smf` and linked by hand:

```sh
. ./scripts/setup/windows-msvc-bootstrap-env.shs
sh build/p2run/build_and_run.sh <path-to-phase2-simple.exe> p2
```

`build/p2run/prog/*.spl` holds the probe set; `zz_mysum.spl` is the case above.
Verified twice, independently, against the same phase 2 artifact.

## Why this matters beyond the one probe

Phase 2 currently produces zero finished binaries on its own, so this defect has
been invisible: every failure so far looked like a *build* failure. It is not.
When the receipt gate is fixed, phase 2 will start emitting binaries that link,
run, and compute wrong values — and a bootstrap that admits such a compiler
would propagate the fault into everything it then builds.

**Admission should stay closed until this is fixed**, independently of the
receipt defect that is currently closing it.

## Related, same lane

- `phase2_file_size_garbage_breaks_capsule_receipt_2026-09-13.md` — `rt_file_size`
  arrives as a pointer-shaped integer, so no `native-build` completes.
- Sampled compile matrices: 19 of 75 `src/lib` files SEGV under phase 2 where
  phase 1 never crashes; 0 of 90 specs compile (the spec DSL does not resolve).

## ROOT CAUSE FOUND (2026-09-13, FULLTEST lane, aarch64 Linux)

Reproduced on aarch64 Linux (this record was Windows-only until now) with
BOTH the pinned Stage-2 binary
(`.../boot13/pin/cand.boot13b.stage2`, sha256 `d19daa8c090c2a30ec6f...`) via
`native-build`, and — much faster, no bootstrap needed — the seed's own
in-process HIR->MIR->LLVM pipeline (same technique as
`llvm_emitter_ssa_violation_guard_spec.spl`): `parse_full_frontend ->
HirLowering -> MirLowering -> MirToLlvm.translate_module`. **Not
loop-specific**: a single non-looping `var a = 1; var b = 2; a = a + b` (no
loop at all) reproduces it identically. The exact trigger, isolated by
probing four variants:

| source shape | result |
|---|---|
| `a = a + 1` (self, literal addend) | correct |
| `x = a + b` (new var, not reassigning either operand) | correct |
| `a = a + b` (reassign to one operand, other operand a DIFFERENT variable) | **BROKEN** |

The emitted LLVM IR for the broken case:

```
%l7 = add i64 -1, 0                          ; const -1
%l16 = load i64, ptr %l12, align 8           ; load `a`  (the accumulator)
%l17 = load i64, ptr %l11, align 8           ; load `b`  (the addend)
%t0 = inttoptr i64 %l16 to ptr
%t1 = inttoptr i64 %l17 to ptr
%l8 = call i8 @rt_array_extend_i64(ptr %t0, ptr %t1, i64 %l7)
```

`a`'s addresses are reinterpreted as ARRAY HANDLES and passed to
`rt_array_extend_i64` -- and the call's `i8` result is never stored back into
`a`, so `a` is never updated. Root cause:
`src/compiler/10.frontend/desugar/collection_desugar.spl` rewrites the bare
STATEMENT form `x = x + y` into `x.merge(y)`, intended to turn `arr = arr +
other_arr` into an in-place extend. Its `is_definite_scalar_addend` gate only
recognises a LITERAL addend, so `a = a + b` (addend `b` is an identifier, not
a literal) is rewritten to `.merge()` even though NEITHER operand is an
array. `lower_unresolved_array_merge`
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:962`) is
"the first layer that knows the receiver's real type" (its own docstring) and
already special-cases a TEXT receiver (routes to `rt_strcat_tagged` + copy-
back — the fix for `mir_unresolved_method_call_merge_2026-08-22.md`) but
falls through to `rt_array_extend_i64` unconditionally for every OTHER type,
including plain i64/f64 scalars.

### Fix LANDED 2026-09-13 (`dea98eba7f9`, FULLTEST lane)

TDD: RED spec at
`test/01_unit/compiler/mir/scalar_compound_reassign_not_array_merge_spec.spl`
(3 examples: rejects the array-merge builtin for a scalar reassign, confirms
the correct arithmetic value, confirms a REAL array `arr = arr + other` still
uses the array-merge builtin). RED without the fix (2/3 fail), GREEN with it
(3/3 pass), verified both under the seed's `test` runner and independently
via the in-process HIR->MIR->LLVM pipeline (scalar case: no
`rt_array_extend_i64` call, no `inttoptr`, real `add nsw i64`; array case:
still routes through `rt_array_extend_i64`; text case: still routes through
`rt_strcat_tagged`).

This fix initially could not be committed: the file it touches,
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, was listed
in this fan-out's fence (another active `codex/*` branch had it in its
diff). Live re-verification (`git diff --name-only $(git merge-base
origin/main <ref>) <ref> -- <file>` over all 195 `refs/remotes/origin/codex/*`
refs) found 95 branches genuinely still touch the file, but none of their
hunks overlap this fix's insertion point (`lower_unresolved_array_merge`,
lines ~962-1030) — the 95 collapse to ~9 distinct patch shapes, all
elsewhere in the file. On that disjointness evidence the lead extended the
unfence to this one hunk; landed as `dea98eba7f9`, touching only the single
intended hunk (one contiguous insertion at line 1018). See
`RECEIPT_FULLTEST.md`'s "Fence re-verification" section for the full
per-branch breakdown. The patch that landed (verbatim, for reference):

```diff
--- a/src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl
+++ b/src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl
@@ lower_unresolved_array_merge, immediately after the TEXT-receiver branch's
@@ closing `return mg_recv` and before `val mg_op = MirOperand(...)`:
+        # PLAIN SCALAR RECEIVER (i64/f64/bool/...) -> ordinary arithmetic add,
+        # not array extend. Same root cause as the TEXT case above:
+        # `collection_desugar.spl`'s `is_definite_scalar_addend` gate only
+        # recognises a LITERAL addend, so `s = s + i` (an identifier addend)
+        # is rewritten to `.merge()` even though neither `s` nor `i` is an
+        # array. Falling through to `rt_array_extend_i64` here reinterprets
+        # both operands' raw i64 bit patterns as array handles via `inttoptr`
+        # and NEVER stores its result back into the receiver -- the call's
+        # i8 result is simply discarded -- so the receiver is silently never
+        # updated. Reproduced without any loop: a bare `a = a + b` with two
+        # plain i64 locals is enough. This is
+        # doc/08_tracking/bug/phase2_drops_loop_carried_accumulator_2026-09-13.md
+        # (P0): phase 1 (seed run/JIT) computes `s = s + i` correctly; only
+        # this native/self-hosted MIR lowering path does not. Only an actual
+        # Array/Slice receiver may still take the extend path below.
+        var mg_recv_is_array = false
+        if val mg_recv_type = self.builder.local_type(mg_recv):
+            match mg_recv_type.kind:
+                case MirTypeKind.Array(_, _) | MirTypeKind.Slice(_): mg_recv_is_array = true
+                case _: ()
+        if not mg_recv_is_array:
+            val mg_add_type = if val t = self.builder.local_type(mg_recv): t else: MirType.i64()
+            var b_mg_add = self.builder
+            val mg_add_res = b_mg_add.emit_binop(MirBinOp.Add, mir_operand_copy(mg_recv), mir_operand_copy(mg_other), mg_add_type)
+            self.builder = b_mg_add
+            self.builder.emit_copy(mg_recv, mg_add_res)
+            self.emit_method_writeback(wb_kind, wb_base, wb_index, wb_field_idx, mg_recv)
+            return mg_recv
         val mg_op = MirOperand(kind: MirOperandKind.Const(
             MirConstValue.Str("rt_array_extend_i64"),
```

Landed and GREEN; `@tag:in-development` and the placeholder spec header have
been dropped.

## Second P0 in this lane: `str()` / string-concat bug is a DIFFERENT, deeper defect

Investigated `phase2_str_returns_raw_pointer_2026-09-13.md` with the same
in-process technique. `"A_str=" + str(t)` and even `str(t) + str(u)` (no
literal operand at all) both lower to:

```
%l5 = call i64 @rt_raw_i64_to_string(i64 %l2)
%t0 = inttoptr i64 %l5 to ptr
...
%l7 = call ptr @rt_strcat_tagged(ptr %t0, ptr %t1)
%t2 = ptrtoint ptr %l7 to i64
%l8 = call ptr @rt_interp_cstr(i64 %t2)
```

This is STRUCTURALLY IDENTICAL to `"A=" + "B"` (two plain literals), which
the surrounding code comments claim is "verified working" — so the MIR/LLVM
shape here is not obviously wrong by inspection, unlike the accumulator bug
above. The defect is therefore most likely NOT in this MIR lowering layer but
either in the native runtime implementations of `rt_strcat_tagged` /
`rt_raw_i64_to_string` / `rt_interp_cstr` (their tagged-vs-raw autodetection,
referenced in comments as "bug #136"), or in how native-build links/selects
among possibly-duplicate runtime symbol definitions. Not fixed in this
session — needs a native-runtime-level investigation (likely
`src/runtime/*.c` or `src/compiler_rust`, a different scope/owner than the
accumulator bug above), out of this lane's remaining budget. Left OPEN with
this narrowing as the next step.
