# riscv64 freestanding: `text != ""` is TRUE for a zero-length text
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: **OPEN** — codegen defect, not fixed. One call site was repaired
  (see below); the comparison itself is still wrong everywhere else.
- Date: 2026-09-01
- Measured in-guest under real OpenSBI v1.4 `-bios fw_payload` (never
  `-kernel`, never `isa-debug-exit`), nonce `919b943728da5c1c`, lane
  `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`
  row 2, gate selftest OK (23 fixtures), freshly built Rust seed.

## The measurement

An in-memory branch trace inside the real
`module_decl_at` (`src/compiler/10.frontend/core/_Ast/module_state.spl`)
recorded, for a MISSING environment entry:

```
trace=900    entered the env-first tail with index 0
trace=800    env_value.len() == 0      <- the text IS zero length
trace=700    the `env_value != ""` arm was taken ANYWAY
```

`.len()` and `!=` disagree about the same value in the same expression, in the
same boot. `.len()` is the one telling the truth.

## Why this is expensive rather than merely wrong

`if x != "":` is the ordinary way to ask "is this text non-empty" and it
appears throughout the compiler. On this lane it is a constant `true`, so every
such guard falls into its non-empty arm carrying an empty value. In
`module_decl_at` that meant returning `ast_parse_i64("") == 0` for EVERY index,
so a module with N top-level declarations converted as N copies of its first
one — silently, with zero errors from either lowering stage. It cost four
boots and three prior sessions to find, because the failure surfaces as a
missing `main` several stages downstream.

## What is known and not known

- **Known:** `.len()` on the same value is correct (0). `ast_parse_i64("")`
  correctly returns 0 via its own `raw == ""` guard, so `==` against the empty
  literal appears to work where `!=` does not — but this is ONE observation and
  is not established as a general asymmetry.
- **Known:** the value came from `rt_env_get(key) ?? ""` where `rt_env_get`
  returned nil; probe2 confirmed `?? ` fires (a `?? "<NIL>"` printed `<NIL>`).
  So the operand is whatever `??` yields for the `""` literal.
- **NOT known:** whether the defect is in `??`'s materialisation of the literal,
  in text `!=` lowering, or in an identity-vs-content comparison. A verbatim
  replica of the same source in a DIFFERENT module compiled into the same image
  answered CORRECTLY, which points at something context-dependent (literal
  pooling / interning) rather than at the operator alone. Do not assume; the
  last four assumptions on this lane were all wrong.

## Repaired call site (not a fix for this bug)

`module_decl_at` now asks `env_value.len() > 0`. That repairs the declaration
loss and preserves hosted semantics exactly, but it does not fix the
comparison, and every other `!= ""` in the tree is still affected on this
target.


---

# FIXED (2026-11-05, worktree lane) — the lowering this bug lived in was
# replaced at tip; the riscv freestanding runtime was missing the replacement's
# helper, and this change ports it.

## What tip actually looks like (measured, not assumed)

Commit `060926039bc` ("Fix typed text equality across source and ABI",
2026-11-03) changed the game two days before this verification: statically
typed `String` `==`/`!=` now lowers, at MIR level, to a single runtime call
`rt_text_eq_any(left, right)` on EVERY backend (`lowering_expr_ops.rs`, the
`BinOp::Eq | BinOp::NotEq && left.ty == STRING && right.ty == STRING` arm),
with `!=` emitted as `eq XOR 1`. The old inline comparison path this bug
documented no longer exists, so the 2026-09-01 "context-dependent wrong
answer" symptom cannot recur in that form.

But the riscv freestanding runtime had **no `rt_text_eq_any` at all** — the
x86_64 port's own comment (`baremetal_stubs.c`, above
`rt_text_eq_raw_raw`) records that this function "never [was] ported to the
freestanding lane". Measured at tip by rebuilding the row-2 kernel on this
host: the link dies hard —

```
ld.lld: error: undefined symbol: rt_text_eq_any
```

— i.e. at tip `text != ""` on this lane did not miscompile; the kernel did
not link at all. (The aarch64/arm32/arm64/x86_32 freestanding runtimes are in
the same state per their own comments; only x86_64 and now riscv define it.
Those lanes are outside this record.)

## The fix

Ported `rt_text_eq_any` into `examples/09_embedded/simple_os/arch/common/riscv_common.h`
(shared by the riscv32 and riscv64 baremetal runtimes, which both `#include`
it), placed right after `rt_native_neq` and reusing its exact safety
machinery:

- **nil-sentinel aware**: `NIL_VALUE` (3) on either side answers equal only
  to itself — this is the `rt_env_get(key) ?? ""` miss path from the original
  measurement, where the operand is whatever `??` materialises.
- **heap-vs-raw**: routes through the existing `riscv_heap_string` /
  `riscv_text_eq_heap_vs_raw`, so a heap string (e.g. a `.substring()`
  result) compares by CONTENT against a raw untagged `""` literal, under the
  plausibility guards (raw word must live inside the image; small words
  rejected) that fence the 2026-08-11 raw-literal defect.
- **raw-vs-raw**: new `riscv_text_eq_raw_raw` compares two raw literals by
  bounded char content (identity fast path first), because a bare literal is
  a `char*` global and address-only comparison makes two distinct empty
  literals "not equal" forever.

Semantics mirror the hosted implementation (`runtime_native.c`) and the
x86_64 freestanding port. Return convention is raw 0/1, matching the
`RUNTIME_FUNCS` spec (`[I64, I64] -> [I64]`) the Cranelift/LLVM backends
emit against.

## Why a source-shape guard rather than a host behavioural test

The defect is freestanding-link-shaped: the hosted interpreter and the LLVM
hosted backend were always correct, and a host test cannot exercise the
baremetal link. Guard:
`scripts/check/check-riscv-text-eq-any.shs` — extracts EVERY `rt_text_eq_any`
definition under `arch/common` + `arch/riscv32` + `arch/riscv64` and judges
each body separately for (a) the nil arm and (b) a raw-content path, with a
fatal 6-fixture `--selftest` including the duplicate-definition case (one
good sibling must not excuse a bad one) and the nil-only stub case. GREEN
after the fix: `PASS — 1 definition(s) checked, all nil-aware and
raw-content-comparing`.

## In-guest verification (real OpenSBI v1.4 fw_payload, never -kernel)

Same probe run as the sibling records
(`examples/09_embedded/simple_os/arch/riscv64/freestanding_cmp_probe_entry.spl`,
steps 8-10; probe rc=0; serial log
`build/os/riscv64_cmp_probe/probe.serial.log`). Every comparison shape
recorded in this document, plus the bare-literal controls:

```
[probe] coalesced env len = EXPECTED                  <- 0
[probe] coalesced env == "" = true (EXPECTED)
[probe] coalesced env != "" = false (EXPECTED)        <- THE 2026-09-01 measurement, now correct
[probe] heap empty len = EXPECTED                     <- 0
[probe] heap empty == "" = true (EXPECTED)
[probe] heap empty != "" = false (EXPECTED)
[probe] "" == "" = true (EXPECTED)
[probe] "" != "" = false (EXPECTED)
[probe] nonempty == literal = true (EXPECTED)
[probe] nonempty != same literal = false (EXPECTED)
[probe] diff content != = true (EXPECTED)
```

Command (from the worktree root):

```
ENTRY=examples/09_embedded/simple_os/arch/riscv64/freestanding_cmp_probe_entry.spl \
SIMPLE_BIN=<rust seed> sh scripts/check/run-riscv64-text-probe-opensbi.shs
```

## Not covered by this fix (stated, not papered over)

- The `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` dialect (a
  different tag convention) also lacks `rt_text_eq_any`; its native-build
  lane will hit the same undefined symbol if it lowers typed text equality.
  Follow-up, outside this record.
- The repaired `module_decl_at` call site (`env_value.len() > 0`) stays as
  is; it is correct and need not revert.
- The full interpreter/buildrun gate kernels still fail to link at tip on
  unrelated missing symbols (`rt_value_truthy`, `rt_value_as_bool`,
  `rt_transient_heap_adopt`, `rt_session_alloc_begin/end`,
  `spl_collection_capture_note_*`); the probe kernel's minimal closure
  sidesteps them. That breakage predates this change.

**Status: FIXED (2026-11-05), behaviorally verified in-guest.**

---

# P3 TRIAGE ADDENDUM (2026-11-11, lane boot8) — SUPERSEDED

Verdict: **SUPERSEDED — already fixed (2026-11-05); re-verified by source + guard this lane.**

This doc's "FIXED (2026-11-05)" section records the lowering change
(`060926039bc`, typed text equality → `rt_text_eq_any` on every backend) plus
the riscv freestanding port of `rt_text_eq_any`, behaviorally verified in-guest.
Spot-checked at `work/p3-boot8-20261111` HEAD (`7d4140c1a6b3`):

- Source: `rt_text_eq_any` is defined (nil-sentinel-aware, heap-vs-raw and
  raw-vs-raw content paths) at
  `examples/09_embedded/simple_os/arch/common/riscv_common.h:615`.
- Guard: `sh scripts/check/check-riscv-text-eq-any.shs` →
  `PASS — 1 definition(s) checked, all nil-aware and raw-content-comparing`
  (rc=0).
- Ancestry: the lowering change `060926039bc` IS an ancestor of this HEAD.

Host-limit note: in-guest re-run is not possible on this Windows host;
verification here is source-presence + guard. The in-guest proof (every
comparison shape EXPECTED, including `coalesced env != "" = false`) stands from
the cited 2026-11-05 section.
