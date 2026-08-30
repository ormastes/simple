# `RuntimeValue::from_int` still truncates to 61 bits at HEAD — the fix landed, was reverted, and only its readers and specs came back

- **Filed:** 2026-08-17
- **Status:** PARTIALLY FIXED 2026-08-17 — runtime choke point + JIT green
  (`boxed_int_wide_roundtrip` 3/3, rc 0); LLVM backend and MIR interpreter still
  TRUNCATING. See the note at the end. Do not close.
- **Severity:** High, and mis-recorded as fixed. This defect has been declared
  resolved at least four times.
- **Component:** `src/compiler_rust/runtime/src/value/core.rs`,
  `codegen/llvm/**`, `codegen/mir_interpreter.rs`
- **Supersedes the resolution claims in:**
  `doc/08_tracking/bug/seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`
- **Related:** `doc/08_tracking/bug/seed_build_guard_checks_only_bin_target_no_link_2026-08-17.md`
  (why nothing caught the test that asserts this fix failing to compile)

## The contradiction this row exists to resolve

Two claims were live at the same time and cannot both be simply true:

- **Claim A:** the int61 truncation defect **IS** fixed at HEAD — a lane's `2^60`
  engine control stopped diverging on a fresh build, which is what exposed that
  control as unsound.
- **Claim B:** `RuntimeValue::from_int` is still the bare shift, so
  `from_int(i64::MAX).as_int() == -1`.

**Resolution: Claim B is correct, and Claim A was not evidence of a fix.** The
fix was never partially applied per-path. It landed once, in full, and was then
reverted; what survived the revert was the *readers* (`HeapInt`,
`HeapObjectType::Int`, `as_heap_i64`) and the *specs*. A tree with readers and no
producer looks half-fixed to a source reader and fully broken to a test.

## Measurement (execution, on the commit that makes the test compile)

`cargo test --release -p simple-runtime --test boxed_int_wide_roundtrip`, rc read
from a variable on the line after the unpiped invocation:

```
test every_i64_survives_the_inline_boundary ... FAILED
test fits_inline_int_matches_the_actual_inline_capacity ... ok
test wide_ints_from_the_bug_report_roundtrip ... FAILED
test result: FAILED. 1 passed; 2 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
```

`BOXED_TEST_RC=101`. Failure detail:

```
from_int(0xefffffffffffffff) lost bits: got 0xfffffffffffffff
from_int(0x8010000000000000).as_int() must round-trip, not truncate to 61 bits
```

The one PASS is load-bearing: `fits_inline_int_matches_the_actual_inline_capacity`
checks the newly implemented predicate against an **independently computed**
oracle (`((v as u64).wrapping_shl(3) as i64) >> 3 == v`), so the predicate's
asymmetric range `-2^60 ..= 2^60 - 1` is confirmed correct rather than merely
self-consistent. The other two failures are therefore genuine truncation, not a
wrong predicate.

Before this, the test **could not compile at all** (`E0599`: `fits_inline_int`
defined nowhere). That is why this had no test coverage despite being filed four
times, and it is exactly the guard gap filed in the companion row.

## Path-by-path status

The encoding is `from_int(i) = (i as u64) << 3`, recovered by
`as_int() = (bits as i64) >> 3` — a 61-bit two's-complement payload.

| Path | Encoding site | State | Evidence |
|---|---|---|---|
| **Runtime tagging** (the choke point) | `runtime/src/value/core.rs:240-244` | **TRUNCATING** | `Self((i as u64) << 3)`; no range check, no heap box. Measured above. |
| Cranelift JIT — emitter | `compiler/src/codegen/cranelift_emitter.rs:739`, `call_runtime_1(..., "rt_value_int", val)` | **TRUNCATING** (delegates) | the in-source comment at :730-738 *claims* `rt_value_int` heap-boxes wide values. It does not: `runtime/src/value/sffi/value_ops.rs:7-9` shows `rt_value_int` is `from_int` verbatim. |
| Cranelift JIT — `BoxInt` instr | `compiler/src/codegen/instr/mod.rs:1448`, same `rt_value_int` call | **TRUNCATING** | the old inline `ishl` site is gone; it was replaced by a delegating call that is equally lossy. |
| **LLVM backend** | `codegen/llvm/functions.rs:~1946` (`BoxInt`), `codegen/llvm/emitter.rs:2096` (`build_left_shift(int_v, three, "box_shl")`), `codegen/llvm/backend_core.rs:731-736` | **TRUNCATING**, and *independently* so | raw `shl 3`; never calls `rt_value_int` at all, so fixing the runtime alone would **not** fix this path. `functions.rs:1928` documents `from_int(i) = i << 3` as the contract. |
| MIR interpreter (Rust) | `codegen/mir_interpreter.rs:766`, `self.set(dest, self.get(value) << 3)` (unbox :776) | **TRUNCATING** | unchanged from the original filing. |
| MIR lowering | comments only: `lowering_expr_ops.rs:571,579`, `lowering_expr_builtin.rs:434,581,667`, `lowering_core.rs:1471`, `lowering_expr_method.rs:1801` | no encoding site; **routes around** the limit | these are u64-packing avoidance heuristics — the per-case whack-a-mole the original row explicitly rejected as a strategy. |
| Simple-side interpreter (`src/app/interpreter/**`) | none — no `<< 3` tagging | **unaffected** | stores native `i64` losslessly. |
| Native scalar `i64` in registers | n/a | **unaffected** | never enters the tagged `RuntimeValue` representation. |

**Producer audit — this is the crux.** `HeapInt` (`runtime/src/value/heap.rs:87-90`)
and `HeapObjectType::Int` have **no producer anywhere in the tree**. Only readers
exist: `core.rs` (`as_heap_i64`, plus the `"int"` name and `ValueKind::Int`
mappings), `sffi/equality.rs:257`, `sffi/io_print.rs:485,572`, `heap.rs:517`,
`collections.rs:1842`. `from_wide_int` — the function the original row says
`from_int` was changed to call — exists **only** as a call in
`runtime/tests/boxed_int_wide_roundtrip.rs`; there is no definition. That is the
signature of a revert, not of an incomplete implementation.

## Why the `2^60` control stopped diverging (Claim A explained)

Not a fix. Two candidate mechanisms, both consistent with the table above and
neither requiring `from_int` to have changed:

1. A **packed** `[i64]`/`[u64]` array path. Packed arrays (`U64_PACKED`,
   `BYTE_PACKED` in `heap.rs` gc_flags) store raw words and bypass tagging
   entirely, so a value that never enters the tagged representation never
   truncates. A control that happens to route through packing measures the
   packing, not the tag.
2. A **stale-vs-fresh `bin/simple` mismatch** — the exact trap the original row
   documents, and independently live today (a deployed binary of 59536728 bytes,
   mtime 2026-08-16 22:59:37, behind origin).

Either way, a control that stops diverging without the encoding site changing is
an unsound control. That is the real finding behind Claim A and it should be
recorded as such rather than as a resolution.

## What `seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md` currently claims

That document contradicts itself and must not be read as authoritative on status:

1. Line 3: "VERIFIED FIXED 2026-08-17 — and now actually covered by tests",
   asserting `from_int` range-checks and routes to `from_wide_int`. **False at HEAD.**
2. Line 36: a second "VERIFIED FIXED 2026-08-17 (batch_02)", crediting
   `2a240d9b0b2`, marked "Closeable", blaming reproductions on a stale seed.
3. Line 62 metadata: **Status: OPEN**, awaiting go-ahead on a representation change.
4. Line 182: "not shippable"; a 2026-07-22 Option-B attempt "did NOT fix the JIT
   truncation".
5. Final section (~line 240): "Option A DID land, then was silently REVERTED by a
   stale snapshot" — `e14a2ffb4df` reverted all 10 source files of `2a240d9b0b2`.
   Status there: LIVE at HEAD, cause = revert. It claims the 10 files were restored
   uncommitted; **they were not** — `core.rs:240` is again `Self((i as u64) << 3)`.

Item 5 is the accurate one. Items 1 and 2 are the mis-recorded closures, and they
are why this is the fifth filing: **a partial fix recorded as complete is how this
defect got closed four times.** The stale-seed explanation offered in items 2 and 5
is plausible in general and is exactly why it was believed — but it is refuted here
by a `cargo test` against freshly compiled runtime source, which involves no
deployed binary at all.

## Not attempted here, deliberately

The `from_int` fix itself is a value-representation change touching every path in
the table, and the LLVM backend needs its **own** fix because it never calls
`rt_value_int`. It is not a small ablatable change and is out of scope for this
row. What this row delivers is: the test now **compiles and is honestly RED**, the
predicate that specifies the inline capacity now exists and is verified correct
against an independent oracle, and the per-path status is recorded so the next
attempt cannot be declared complete after fixing only the runtime choke point.

## Reproducer

```sh
cd <isolated worktree>/src/compiler_rust
CARGO_TARGET_DIR=/mnt/data/cargo-int61 cargo test --release -p simple-runtime --test boxed_int_wide_roundtrip
RC=$?          # read on the line AFTER, never through a pipe
echo "BOXED_TEST_RC=$RC"   # expect 101 until from_int boxes wide values
```

Live Simple-side reproducer specs that survived the revert:
`test/01_unit/compiler/codegen/probe_wide_int_boundary_jit.spl`,
`wide_int_boundary_class_spec.spl`.

## Exit criteria

Not "`from_int` was changed" — all of:

1. `boxed_int_wide_roundtrip` is GREEN (3/3), stated with rc and the
   `test result:` line quoted.
2. A `HeapObjectType::Int` **producer** exists and is reachable from `from_int`.
3. The **LLVM** path (`emitter.rs:2096`, `functions.rs:~1946`) is fixed
   independently, or demonstrably routed through the fixed runtime call.
4. The MIR interpreter path (`mir_interpreter.rs:766`) is fixed or documented as
   unreachable, with evidence.
5. A revert-detection note: this fix has been reverted by a stale snapshot once
   (`e14a2ffb4df`), so re-landing it must be re-verified at origin **after** the
   push, not only locally.

## 2026-08-17 — CHOKE POINT FIXED; two paths still open (honest partial)

`src/compiler_rust/runtime/src/value/core.rs`:

- `from_int` now consults `fits_inline_int` and routes wide values to a new
  `from_wide_int`, which allocates a `HeapInt` leaf with
  `HeapHeader::new(HeapObjectType::Int, …)` and returns a tagged heap pointer —
  modelled directly on the existing `from_u64`/`from_float` boxing. This is the
  **missing producer** exit criterion 2 asks for. OOM/layout failure falls back to the
  legacy inline shift rather than returning a wrong kind.
- `as_int` reads the box back via `as_heap_i64()` when the value is not an inline int.
- `is_int()` is deliberately unchanged (tag-only), which is what the test's
  `fits_inline_int(v) == boxed.is_int()` assertion pins.

Exit criterion 1, quoted verbatim, rc read on the line AFTER the unpiped invocation:

```
$ cd src/compiler_rust && CARGO_TARGET_DIR=/mnt/data/cargo-bugfix-0dc8 \
    cargo test --release -p simple-runtime --test boxed_int_wide_roundtrip
BOXED_TEST_RC=0
running 3 tests
test every_i64_survives_the_inline_boundary ... ok
test fits_inline_int_matches_the_actual_inline_capacity ... ok
test wide_ints_from_the_bug_report_roundtrip ... ok
test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
```

Per-path status after this change:

| Path | State |
|---|---|
| Runtime tagging (`core.rs from_int`/`as_int`) | **FIXED**, test-covered (above) |
| Cranelift JIT (`cranelift_emitter.rs`, `instr/mod.rs` `BoxInt`) | **FIXED by delegation** — both call `rt_value_int`, which is `from_int` verbatim, so the in-source comment claiming heap-boxing is now true |
| **LLVM backend** (`codegen/llvm/emitter.rs:2096` `build_left_shift`, `functions.rs:~1946`) | **STILL TRUNCATING** — emits a raw `shl 3` and never calls `rt_value_int`, exactly as criterion 3 warns. Not changed here: it needs the emitter to call the runtime instead of open-coding the tag, which is a codegen change this row's evidence does not cover. |
| MIR interpreter (`mir_interpreter.rs:764-780`) | **STILL TRUNCATING** — `emit_box_int`/`emit_unbox_int` are a symmetric in-model shift with no access to the runtime allocator; boxing there means giving that interpreter a heap. Documented, not fixed. |

Criteria 1 and 2 are met and verified by execution. **Criteria 3 and 4 are NOT met** —
do not read this note as a closure, and do not close the row until the LLVM emitter is
fixed independently. Criterion 5 (re-verify at origin after push) is untouched: nothing
was pushed from this lane.

Binary: /mnt/data/cargo-bugfix-0dc8/release/simple (built 2026-08-17 13:48, 59554384 bytes, from this worktree's source; NOT deployed to bin/simple). `bin/simple` is still the pre-fix seed.

**Status:** PARTIALLY FIXED — runtime choke point + JIT green; LLVM backend and MIR
interpreter still open.

## 2026-08-17 20:1x — re-run on the DEPLOYED seed: still PARTIAL, as designed

Binary: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple (bin/simple), md5 669150b61f2f20401a6a895ae54e9fee, 59550432 bytes, mtime 2026-08-17 20:10:45 — the REDEPLOYED seed carrying this session's fixes.

The runtime choke point + Cranelift JIT half is now verified on the deployed binary
(probe `c3b.spl`, interpreter vs jit, five wide-int shapes — identical and correct):

```
var=1152921504606846976  arr=1152921504606846976  lit=1152921504606846976
lit62=4611686018427387904  push=1152921504606846976      (both engines)
```

But the row is NOT closed: the live Simple-side reproducer spec is still partly red.

```
$ bin/simple test test/01_unit/compiler/codegen/wide_int_boundary_class_spec.spl --no-session-daemon --timeout 900
Results: 3 total, 2 passed, 1 failed
```

That residual is the LLVM-emitter / MIR-interpreter half the per-path table above
already records as STILL TRUNCATING. No regression relative to the isolated build.

**Status: still PARTIALLY FIXED — runtime + JIT green on the DEPLOYED seed; LLVM
backend and MIR interpreter still open.**
