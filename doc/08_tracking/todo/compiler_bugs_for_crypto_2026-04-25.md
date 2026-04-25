# Compiler / Interpreter Bug-Fix Plan (Unblocking SSH+TLS Crypto Rollout)

Date: 2026-04-25
Owner: unassigned
Companion to: `ssh_tls_modern_algorithms_2026-04-25.md`

This plan addresses the bugs that would otherwise force ugly workarounds in
the SSH/TLS modern-algorithm port. Each entry has a minimal repro, suspected
root cause, fix location, and acceptance test. Order is **blocking-first**:
B1–B3 unblock crypto KAT testing; B4–B6 are quality-of-life that pay back
across all crypto code; B7+ are speculative — opened only on a real repro
during §1–§6 of the crypto plan.

Out of scope (already fixed): Cranelift `>>` signed/unsigned (closed by
FR-DRIVER-0002b on 2026-04-18; do not re-open without a fresh repro).

---

## B1 · Release binary swallows error detail (BLOCKING)

**Memory:** `feedback_simple_run_wrapper_broken.md` (confirmed 2026-04-18).

**Repro**

```bash
./bin/simple /tmp/syntax_error.spl
# → "[STDERR] Error running /tmp/syntax_error.spl"   (no actual error shown)
./src/compiler_rust/target/bootstrap/simple /tmp/syntax_error.spl
# → "error: parse error: Unexpected token: expected Colon, found RBrace"
```

Two related defects:
1. Real parse / runtime error message is dropped; only a generic wrapper line
   survives.
2. The wrapper line is printed on **stdout** with a `[STDERR]` prefix, not on
   stderr — so exit-code-aware shell pipelines see clean stdout while exit
   code is 1.

**Suspected root cause:** Regression in self-hosted error-reporting path
introduced between the last working release build and the 2026-04-18 ~03:03
rebuild. Likely in `src/app/cli/` (script entrypoint) or
`src/compiler/90.tools/` where errors are formatted before being emitted.

**Fix**
- Locate the wrapper that emits `"[STDERR] Error running …"` (likely a `print`
  on a Result error branch in `src/app/cli/`). Restore the underlying
  `Err(text)` payload in the message, and route via the stderr handle, not
  stdout.
- Add a regression test: a `.spl` file with a known parse error must produce
  a non-empty stderr containing the original message, and an empty stdout.

**Acceptance**
- `bin/simple test/regression/wrapper_error_detail.spl` shows the real error.
- Test harness asserts stderr length > 50 bytes and stdout length == 0.

---

## B2 · Interpreter `[u8]` quadratic on multi-MiB buffers (BLOCKING for crypto KAT)

**Memory:** `feedback_interpreter_bulk_buffer.md` (confirmed 2026-04-15).

**Repro**

```spl
fn main():
    var buf: [u8] = []
    var i: u64 = 0
    while i < 1048576:    # 1 MiB
        buf.push(0u8)
        i = i + 1
    print buf.len()
```

Wall time per buffer size in interpreter mode (`bin/simple <file>.spl`):

| size | wall  |
|------|-------|
| 64 KiB | <0.5s |
| 256 KiB | ~5s |
| 1 MiB | >30s |
| 32 MiB | never completes |

Doubling pattern (`pad = pad + pad`) is no faster — it's also quadratic.

**Suspected root cause:** Interpreter list ops (probably `push` and/or
slice/concat) reallocate without amortized growth, OR copy the whole vector on
every operation due to a refcount-on-mutate path. Native compile is fine
(memory note IF-13).

**Fix path** (do the cheap one first; only do the deep one if it becomes a
recurring complaint after crypto lands)

- **Quick (1–2 days):** add a runtime extern `rt_bytes_alloc(len: u64) -> [u8]`
  that returns a zero-filled buffer in O(len) using the existing C runtime
  (`src/runtime/runtime_native.c`), plus `rt_bytes_copy_into(dst, dst_off,
  src) -> bool`. Crypto KAT loaders call this instead of push-loops.
- **Proper:** find the `push` / concat lowering in
  `src/compiler_rust/compiler/src/interpreter*/` (and the self-hosted
  equivalent under `src/compiler/40.eval/` or wherever interpreter lives) and
  switch to amortized-doubling Vec semantics with COW only on observed
  aliasing. Add a perf test that asserts 32 MiB push-loop completes in <2 s.

**Acceptance**
- `bin/simple test/perf/bytes_push_1mib.spl` completes in <1 s, 32 MiB in <30 s.
- `rt_bytes_alloc` extern available and wired through `std.bytes`.

---

## B3 · SSpec `--mode=smf` wrapper class hoisting — VERIFIED FIXED 2026-04-25

**Status:** Already landed 2026-04-17 in `preprocess_sspec_for_smf`
(`src/compiler_rust/driver/src/cli/test_runner/execution.rs`). Module-scope
`class`/`impl`/`enum`/`trait`/`type`/`val`/`let`/`mod` are now hoisted; `use std.spec`
is auto-injected. Verified by running `test/smoke/compile_smoke_spec.spl` and a
module-scope `class Foo` spec under `--mode=smf` — both PASS. Crypto KAT loaders
(module-scope class definitions) are unblocked.

**Residual issues (separate items, NOT B3 — won't block crypto KATs):**
- R1: `class` INSIDE `it` blocks fails HIR lowering — needs HIR change.
- ~~R2: `skip("reason")` unresolved in compiled mode — `skip` is a Simple language
  keyword.~~ **Superseded by R2-broader (see below).** The bug is bigger than
  the `skip` keyword conflict — the SMF/native compile path links *no*
  `std.spec` library symbols.

### R2-broader · SMF/native cannot link any `std.spec` library symbol — investigated 2026-04-25

**Repro (each fails identically with `Undefined symbol: <name>` at SMF reloc):**

```spl
# /tmp/r2_pending.spl
use std.spec
describe "x":
    it "y":
        pending("reason")        # → Undefined symbol: pending
```

```bash
bin/simple test --mode=smf --force-rebuild --clean /tmp/r2_pending.spl
# 2026-04-25T10:14:28Z ERROR ... Undefined symbol: pending (required by relocation 8)
# Failed (5ms)
```

Same failure with `skip("...")` (symbol `skip`), `skip_it "..."` (symbol
`skip_it`), and `check(true)` (symbol `check`) — all are exported by
`src/lib/nogc_sync_mut/spec.spl` and re-exported by
`src/lib/nogc_sync_mut/spec/__init__.spl`, but none reach the SMF.

`describe`/`it`/`expect` "PASS" only because:
- `--mode=native` runs `pipeline/native_project/stubs.rs` which prints
  `Generating 234 stub functions for unresolved symbols` and replaces every
  `std.spec` call with a no-op stub. The "PASSED" is meaningless — the body
  never executed.
- `--mode=smf` swallows a runtime `Function not found (invalid UTF-8 name)`
  inside the bdd shim and the test runner reports PASSED anyway.

**This means R2 cannot be solved by:**
- (a) renaming `skip` → `pending` in the DSL — `pending` is also unresolved.
- (b) parser context-sensitivity for `skip(...)` — would parse fine but still
  fail to link.
- (c) HIR lowering for `Node::Skip` with trailing expr — same.

The actual fix path is to make the SMF/native pipeline link the `std.spec`
library functions reached via `use std.spec`, OR to teach the test wrapper
to inline the small spec-DSL helpers (similar to how
`test/unit/lib/common/pending_on_spec.spl` already inlines `pending_on` and
`pending_skip` because — quoting that file — *"the runtime doesn't expose
custom spec functions from std.spec imports"*). The latter is local to
`preprocess_sspec_for_smf` in
`src/compiler_rust/driver/src/cli/test_runner/execution.rs`.

**Latent companion bug (also surfaced during this investigation):**

Two paths report PASSED for tests that actually failed to run:

1. `--mode=native` stub-generation makes calls to undefined library symbols
   into no-op stubs. The `it` body "executes" but does nothing; matchers
   never assert. Crypto specs running `--compile` are very likely getting
   false greens today — anything assertion-driven that touches a stubbed
   symbol silently passes.
2. `--mode=smf` describe/it path swallows a "Function not found (invalid
   UTF-8 name)" runtime error and reports PASSED. Same false-green risk.

These need their own bug entries (separate from R2-broader). For the crypto
rollout, treat compiled-mode `bin/simple test --compile` results as
**non-authoritative until R2-broader and the false-green bugs are resolved**;
run crypto specs in interpreter mode only.

**Acceptance gate #2 of the original R2 ticket** ("skip/pending still work
in interpreter mode") is locked in by
`test/unit/compiler/r2_pending_helper_spec.spl`, which uses
`pending("reason")` and verifies the interpreter BDD path
(`interpreter_call/bdd.rs:656`).

**Original (stale) description retained for history:**

**Memory:** `feedback_sspec_compile_pipeline.md`.

**Repro**

```bash
bin/simple test --mode=smf test/unit/crypto/sha256_kat.spec.spl
# → compile error: class definition not allowed in expression context;
#                 unresolved symbol `skip`
```

This blocks compiled-mode regression tests for any spec that defines helper
classes — which is *every* crypto KAT loader.

**Suspected root cause** (per memory)
- Spec wrapper template in the test runner emits the spec body inside
  `fn main():` rather than at module scope, so any `class Foo:` inside
  becomes invalid.
- `skip(...)` is parsed but no module-level binding is generated in compiled
  mode (interpreter has it built in).

**Fix**
- Update the spec wrapper generator to emit class defs at module scope and
  only the `it`/`describe` driver inside `fn main()`. Files are likely under
  `src/app/test_runner_new/` or `src/compiler/90.tools/spec_*` — confirm with
  `grep -rn "fn main" $(grep -rln "wrap_spec_for_compile" src/)`.
- Provide a `skip(reason: text)` shim in `lib/common/test/` that compiled-mode
  test runners link in.

**Acceptance**
- `test/unit/crypto/sha256_kat.spec.spl --mode=smf` compiles and passes.
- `bin/simple test --mode=smf` runs at least 95 % of specs that pass in
  interpreter mode.

---

## B4 · Bitfield sugar missing (QoL — high payback for AES / SHA / GCM)

**Memory:** referenced in driver-framework C.3 follow-up
(`project_driver_framework.md`).

**Repro**

```spl
# What we want to write:
val s = (state[i] & 0xFF000000u32) >> 24
state[i].bits[24..32] = byte
```

Today every AES round, every SHA word permutation, and the GCM polynomial
multiplier is hand-written byte-by-byte with shift-and-mask. The crypto port
will multiply this out by ~10× if not addressed.

**Fix**
- Add `bits[lo..hi]` get/set sugar on integer types, lowering to mask + shift
  in HIR before codegen.
- Add `u32::byte(i: u32) -> u8` and `u32::with_byte(i, b)` helpers in stdlib —
  small, no compiler change required, do this regardless.
- Document in `doc/07_guide/quick_reference/syntax_quick_reference.md`.

**Acceptance**
- New `test/unit/compiler/bitfield_sugar_test.spl` covers slice get, slice
  set, multi-slice set in one assignment, and aliasing rules.
- AES round code in `lib/common/crypto/aes/round.spl` rewrites cleanly with
  the new sugar (≥30 % LoC reduction).

---

## B5 · `match` on integer constants — verify jump-table codegen

Speculative until measured. The TLS suite dispatcher (`tls/cipher.spl:19-`)
is a 7-arm `if/elif` chain on a `u16` cipher_id. The §5 plan grows that to
~15 arms (TLS 1.3 + ECDHE_ECDSA fill-ins). If the compiler emits a linear
chain, hot-path latency under handshake-storm benchmarks will regress.

**Repro / test**

```spl
fn dispatch(id: u16) -> i64:
    match id:
        0xC02F: 1
        0xC030: 2
        0xCCA8: 3
        0x1301: 4
        0x1302: 5
        0x1303: 6
        # ... 10 more
        else: 0
```

Inspect emitted Cranelift IR for `BrTable` vs sequential `BrIf`.

**Fix (if linear)**
- Add a HIR→codegen pass that detects dense integer `match` and lowers to a
  jump table when arm count ≥ 4 and key span ≤ 1024.

**Acceptance**
- Cranelift IR for the test contains a `br_table`.
- Microbench on 16-arm dispatch: ≤2× cost of a single direct call.

**Status (2026-04-25):** Landed in the **Rust seed** as commit
`379a08503d` (`feat(mir,codegen): jump-table lowering for dense int match`).
The Rust seed adds `MirTerminator::Switch`, the `try_collect_int_match` /
`lower_int_switch` HIR-to-MIR pass, and the Cranelift `br_table` translation.
`test/unit/compiler/codegen/match_switch_codegen_spec.spl` (7 examples)
passes through `bin/simple` (Rust seed interpreter mode).

### B5b · Self-hosted compiler has no MIR lowering for `match` (prerequisite)

A follow-on attempt to port B5 to the self-hosted compiler at
`src/compiler/` revealed the port's premise is empirically wrong:
**self-hosted MIR has no `MatchCase` lowering at all** — there is no
nested-If chain to optimize, because there is no chain to begin with.

Empirical evidence (worktree `agent-ac3bca955ef32802a`, 2026-04-25):

- `src/compiler/50.mir/mir_lowering_expr.spl` enumerates 32 explicit
  `case` arms for `HirExprKind` (lines 50-263). `MatchCase` is not one
  of them. The `case _:` fallback at line 263 raises
  `self.error("unsupported MIR expression: {expr.kind}", nil)`.
- No desugar/rewrite pass elsewhere in `src/compiler/` rewrites
  `HirExprKind.MatchCase` into nested `If`. Grep across all 15 hits in
  the self-hosted tree shows only `scan_*` analysis visitors plus the
  HIR builder itself.
- The MIR `Switch` machinery is otherwise complete: the
  `MirTerminator.Switch(value, targets, default)` variant exists
  (`mir_instructions.spl:451`); `SwitchCase{value:i64, target:BlockId}`
  exists (`mir_instructions.spl:431`); all backends (x86_64 / aarch64 /
  riscv32 / riscv64 / wat / lean / mir_to_llvm / c / vhdl /
  llvm_lib_translate_expr) already destructure
  `case Switch(value, targets, default)` and read `target.value`,
  `target.target.id` (i.e. they assume `[SwitchCase]`, not
  `[(i64, BlockId)]`); the interpreter handles `Switch` at
  `95.interp/mir_interpreter.spl:681`.
- **Latent builder bug:** `MirBuilder.terminate_switch` in
  `mir_data.spl:359` declares `targets: [(i64, BlockId)]` instead of
  `[SwitchCase]`. There are zero callsites today, so the mismatch is
  dormant; whoever first calls it will trip a struct-vs-tuple error.
- No regression: `match` works via `bin/simple` because the binary IS
  the Rust seed (per `feedback_sspec_compile_pipeline.md`); the
  self-hosted MIR pipeline is reached only by stack-3 self-compilation,
  which has no automated test coverage of `match` codegen today
  (`test/unit/compiler/mir/mir_lowering_new_spec.spl` and
  `test/unit/compiler/driver/pipeline_mir_spec.spl` are both `skipped`
  with the comment `"pre-existing test failures - functions/imports
  not available"`).

**Why this is not a single-PR port.** B5 in the seed was a localized
optimization layered on top of an existing nested-If lowering. Porting
it to self-hosted requires first writing the entire `MatchCase` →
MIR pattern-compilation pipeline that handles all 9 `HirPatternKind`
variants (`Wildcard`, `Literal`, `Binding`, `Tuple`, `Array`,
`Struct`, `Enum`, `Or`, `Range`), wiring guard expressions, and
threading temp locals/result merges. Only after that lands does the
B5 detector port (`try_collect_int_match` mirror, ≥4 arms / ≤1024
span) become a small, additive change.

**Recommended sequencing**

1. **Prereq:** implement HIR `MatchCase` → MIR lowering in
   `src/compiler/50.mir/mir_lowering_stmts.spl` (or a new
   `mir_lowering_match.spl`). Mirror `lower_if` structure: lower
   scrutinee once into a temp local, allocate per-arm + merge blocks,
   threading result. Start with `HirPatternKind.Literal(IntLit)` +
   `Wildcard` (covers crypto cipher dispatch); error on the other
   seven kinds with a precise message until follow-up tickets land.
2. **Fix latent builder bug:** retype
   `MirBuilder.terminate_switch(targets: [(i64, BlockId)])` to
   `targets: [SwitchCase]` so it matches the terminator's actual
   field type and the backends' destructuring.
3. **Then port B5:** add a `try_collect_int_match` equivalent that
   peels the freshly-built nested-If chain (or, preferably, peels
   the original `MatchCase` arms directly since we own the lowering
   now) and emits `MirTerminator.Switch` when arm count ≥ 4 and key
   span ≤ 1024. Mirror SWITCH_MIN_ARMS = 4 / SWITCH_MAX_SPAN = 1024
   from the Rust seed.
4. **Self-hosted regression test:** add
   `test/unit/compiler/codegen/match_switch_self_hosted_spec.spl`
   that exercises a 5-arm dense match through whatever entry point
   the self-hosted MIR pipeline supports (likely
   `MirLowering.new(...).lower_module(...)` directly, mirroring the
   commented-out body of `pipeline_mir_spec.spl`).

Until step 1 lands, the self-hosted port of B5 cannot be done — there
is no chain to detect. This is filed here so the next agent does not
re-discover the missing infrastructure.

---

## B5b · `MatchCase` → MIR in the self-hosted compiler

**Status: Phase 1 DONE (2026-04-25). Phase 2a DONE (2026-04-25). Phase 2b deferred — see list below.**

The Rust seed (B5) detects dense integer matches after the HIR `LetIn { ... If
chain }` desugaring and emits `MirTerminator.Switch`. The self-hosted MIR
lowerer in `src/compiler/50.mir/mir_lowering_expr.spl` did NOT handle the
`HirExprKind.MatchCase` variant at all — every `match` expression fell through
to the generic `case _:` arm, hit `self.error("unsupported MIR expression: ...")`,
and downstream the release self-hosted binary crashed (`malloc_consolidate:
invalid chunk size`) instead of producing a clean diagnostic.

A dormant signature bug in `MirBuilder.terminate_switch` also blocked any
caller: it declared `targets: [(i64, BlockId)]` but
`MirTerminator.Switch` expects `[SwitchCase]`. Zero callers existed when the
bug was discovered, so it was inert.

### Phase 1 (this work)

- `src/compiler/50.mir/mir_data.spl` — corrected
  `MirBuilder.terminate_switch` signature to `targets: [SwitchCase]`.
- `src/compiler/50.mir/mir_lowering_expr.spl` — added
  `case MatchCase(scrutinee, arms):` in `lower_expr` plus three helpers:
  - `lower_match_case` — gates Phase 1 patterns; rejects everything else
    with a clear `B5b Phase 2 not yet implemented: pattern kind X` diagnostic.
  - `should_emit_switch` — same heuristic as the Rust seed
    (`SWITCH_MIN_ARMS = 4`, `SWITCH_MAX_SPAN = 1024`).
  - `emit_switch_dispatch` / `emit_if_chain_dispatch` — dense path emits
    `MirTerminator.Switch`; sparse path emits a chained `If` cascade. Both
    use a temp-then-merge pattern matching `lower_if`. Scrutinee is
    evaluated once into a temp to avoid duplicating side effects.
- `test/unit/compiler/codegen/match_switch_self_hosted_spec.spl` — new
  regression spec covering dense / sparse / wide-span / TLS-shape arms.

Phase 1 accepts ONLY:

- `HirPatternKind.Wildcard` (as the default arm)
- `HirPatternKind.Literal(IntLit n)` (constant-int arms)

A wildcard default arm is required (no exhaustiveness analysis in Phase 1).

### Phase 2a (this work — DONE 2026-04-25)

Tractable subset of Phase 2 — patterns that slot cleanly into the
existing dense-vs-sparse partition without requiring a full
pattern-compilation tree:

- `HirPatternKind.Binding(symbol, _)` — irrefutable default arm that
  also binds the scrutinee to a local symbol. Implemented by tracking
  `default_binding: SymbolId?` alongside `default_body` and inserting
  `self.local_map[symbol] = scrut_local` immediately before lowering
  the default body in both `emit_switch_dispatch` and
  `emit_if_chain_dispatch`. Mutability flag is irrelevant at MIR level
  (it only matters during borrow-check) and is intentionally ignored.
- `HirPatternKind.Or(patterns)` when every alternative is
  `Literal(IntLit n)`. Each alternative is expanded into its own
  `int_cases` entry pointing at the shared arm body, so the existing
  dense / sparse dispatch handles them with no further changes. Or
  patterns whose alternatives include any non-IntLit fall through to
  the existing Phase 2 diagnostic
  (`B5b Phase 2 not yet implemented: pattern kind Or with non-IntLit alternatives`).

Phase 2a additions to the regression spec
(`test/unit/compiler/codegen/match_switch_self_hosted_spec.spl`):

- `binding_default` — int arms + binding default referencing the bound
  symbol (`y + 1000`).
- `binding_only` — match whose only arm is a binding (no int_cases at
  all; cascade tail = default).
- `or_dense` — Or arms that, after expansion, hit the Switch path
  (≥ 4 keys, span ≤ 1024).
- `or_sparse` — Or arms that fall through to the if-chain.

### Phase 2b (still DEFERRED — pending in this same B5b ticket)

The full pattern-compilation pipeline is genuinely multi-day; the user
explicitly accepted the partial scope. Phase 2b will add lowering for:

- `HirPatternKind.Literal(non-IntLit)` — bool / char / string / float
  literal arms (deferred because they break the clean
  `int_cases: [(i64, HirBlock)]` partition; would need a parallel
  `non_int_cases` lane plus per-type comparison emitters).
- `HirPatternKind.Tuple(elements)` — destructured tuple arms.
- `HirPatternKind.Array(elements, rest)` — fixed-length and rest patterns.
- `HirPatternKind.Struct(type_, fields)` — record destructuring.
- `HirPatternKind.Enum(type_, variant, payload)` — discriminant test +
  payload destructuring (Tuple / Struct payload variants).
- `HirPatternKind.Or(patterns)` with non-IntLit alternatives — needs
  the same parallel non_int_cases lane as non-IntLit Literal.
- `HirPatternKind.Range(start, end, inclusive)` — range tests.
- Match-arm guards (`HirMatchArm.has_guard / .guard`) — combine
  pattern-test + guard before branching to the arm body.
- Result type merging across arms with non-uniform body types
  (Phase 1 hard-codes `MirType.i64()` for the result temp).
- Exhaustiveness handling for matches without a wildcard / binding arm
  (currently rejected with a Phase 2 diagnostic).

### Acceptance gates met for Phase 1 + 2a

- 5-arm dense int match dispatches correctly (every arm + wildcard).
- Sparse (2-arm) and wide-span (>1024) matches still work via the
  if-chain fallback.
- Binding default arms expose the scrutinee under the bound symbol
  inside the arm body (both Switch and if-chain paths).
- Or-of-IntLit alternatives expand into independent dispatch entries
  and continue to use the dense Switch when they push key-count past
  the SWITCH_MIN_ARMS threshold.
- Other pattern kinds (Tuple, Array, Struct, Enum, Range, non-IntLit
  Literal, Or-with-non-IntLit) still emit
  `B5b Phase 2 not yet implemented: pattern kind X`
  rather than the cryptic `unsupported MIR expression`.
- `MirBuilder.terminate_switch` signature uses `[SwitchCase]`.
- Regression spec at
  `test/unit/compiler/codegen/match_switch_self_hosted_spec.spl`.

---

## B6 · Constant-time compare must not be branch-folded

**Repro**

```spl
fn ct_eq(a: [u8], b: [u8]) -> bool:
    if a.len() != b.len(): return false
    var diff: u8 = 0u8
    var i: u64 = 0
    while i < a.len():
        diff = diff | (a[i] ^ b[i])
        i = i + 1
    diff == 0u8
```

After codegen optimization, inspect the IR / asm to confirm:
- No early-exit branch on `diff != 0`.
- `^` and `|` both lowered as ALU ops, not specialized.

**Fix (if optimizer breaks CT)**
- Add a `@no_branch_fold` attribute or a `std.crypto.black_box(x)` intrinsic
  that the optimizer must treat as opaque. ML-KEM rejection sampling and
  Curve25519 conditional swap need the same primitive.

**Acceptance**
- `cargo test ct_eq_no_branch` parses Cranelift IR and asserts no
  `brif diff` is present in the inner loop.

---

## B7 · Hunt-list (open only on a real repro during crypto port)

These are **not** opened pre-emptively. As §1–§6 of the crypto plan land,
each speculative item below either becomes a real bug entry under
`doc/08_tracking/bug/bug_*.md` with a minimal repro, or is closed as
"verified fine".

| Tag | Speculative bug | First likely encounter |
|-----|-----------------|------------------------|
| H-1 | `u32.to_be_bytes` not folded — emits function call | SHA-256 message scheduling |
| H-2 | const `[u8;256]` AES S-box re-initialized every call | First AES KAT |
| H-3 | `u64.mul_hi` emits libcall instead of `mulhi` instruction | Curve25519 26-bit limb math |
| H-4 | GF(2^128) carryless mul slow — no `clmul` intrinsic | GCM ghash |
| H-5 | `[u64].push` over big-int RSA modulus quadratic | RSA-PSS sign |
| H-6 | Keccak `f1600` rotations: `rotl(x, n)` not folded | SHA-3 / ML-KEM |
| H-7 | `for byte in bytes:` interpreter overhead vs index loop | Any KAT loader |
| H-8 | `extern fn` newly added but bootstrap not rebuilt → silent NoOp | Per `feedback_extern_bootstrap_rebuild.md` — process, not a code bug |

---

## Sequencing

```
B1 (error detail) ──► B3 (sspec compile) ──► crypto KAT can run compiled
                  └──► B2 (interpreter perf) — independent track, parallel
B4 (bitfield sugar) — start before §2 (AES T-tables, SHA round)
B5 (match jump table) — needed by §5.2 cipher dispatcher
B6 (CT compare guard) — must be in place before §3 (ML-KEM) and §5.4 (PQ TLS)
B7 — open as encountered
```

Ship gate for each crypto-plan milestone:

- **M1 (SSH advert)** needs: B1 (so test failures are debuggable).
- **M3 (TLS 1.3)** needs: B1, B3, B5, B6.
- **M5 (PQ on both)** needs: B1, B2, B3, B6.

---

## Memory hygiene

- `MEMORY.md` index entry for `feedback_cranelift_shr_bug.md` says "broken;
  use division workaround". The file body already records the FR-DRIVER-0002b
  fix (2026-04-18). Update the index hook to read "fixed in compiled mode" so
  future sessions don't waste time on a dead workaround.
- After each B-task lands, update the matching `feedback_*.md` so the memory
  reflects the post-fix reality, not the historical incident.
