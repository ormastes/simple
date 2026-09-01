# `guard` Capability-Matrix Row vs Observed Guard-Page Behaviour

> `mem_infra_matrix()` in `src/lib/common/mem_infra/config.spl` advertises, per backend, whether `--mem-infra=guard` gives you guard pages. A capability matrix is a safety claim: someone reads `guard: true`, enables it to hunt a use-after-free, and trusts a clean run to mean the UAF is not there.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `guard` Capability-Matrix Row vs Observed Guard-Page Behaviour

`mem_infra_matrix()` in `src/lib/common/mem_infra/config.spl` advertises, per backend, whether `--mem-infra=guard` gives you guard pages. A capability matrix is a safety claim: someone reads `guard: true`, enables it to hunt a use-after-free, and trusts a clean run to mean the UAF is not there.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`mem_infra_matrix()` in `src/lib/common/mem_infra/config.spl` advertises, per
backend, whether `--mem-infra=guard` gives you guard pages. A capability matrix
is a safety claim: someone reads `guard: true`, enables it to hunt a
use-after-free, and trusts a clean run to mean the UAF is not there.

Until 2026-08-02 that row read `interpreter: true, cranelift: true, llvm: true`
and two of the three were false. The guard-page allocator exists only in
`src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs`; cranelift and
llvm both resolve `rt_alloc` to the C runtime, which has no `mmap`/`mprotect`
guard mechanism at all.

This spec exists so that row can never drift back to a claim nobody measured.
It does not read source, count `grep` hits, or check that an env var is
consumed — any of those can be true while the protection does nothing. It
commits a **real use-after-free** in a child process and observes which side of
the fault the process reaches:

| outcome | meaning |
|---------|---------|
| child prints `uaf_probe: survived` and exits 0 | the write landed on ordinary freed heap — **no guard page** |
| child dies on SIGSEGV, never prints `survived` | the write hit a `PROT_NONE` page — **guard page is real** |

Each backend is then asserted to match its own matrix row, so the matrix and
the runtime cannot disagree without this spec going red.

## Sabotage control

Every backend is run twice: once with `SIMPLE_MEM_GUARD_RATE=1` and once with
the knob unset. The knob-off run must survive on *every* backend. That is what
makes the interpreter's trap meaningful — it shows the SIGSEGV is caused by the
guard being switched on, not by the fixture being inherently fatal. A spec that
only ran the guard-on case would pass just as happily against a probe that
segfaulted for unrelated reasons.

## What the JIT arm actually measures (CORRECTED 2026-08-09)

An earlier version of this spec ran the probe under `SIMPLE_EXECUTION_MODE=jit`
and asserted the UAF **survives**, on the premise that "cranelift resolves
`rt_alloc` to the C runtime". That premise is false for this lane and the
assertion was measurably wrong — the child dies on SIGSEGV at
`SIMPLE_MEM_GUARD_RATE=1`.

Reason: `bin/simple run` under `SIMPLE_EXECUTION_MODE=jit` does **not** link the
C runtime for externs. The JIT emits a call to the `rt_interp_call` trampoline,
which resolves every extern through the same Rust dispatch table the
tree-walk interpreter uses (`interpreter_extern/mod.rs`). So `rt_alloc`/`rt_free`
in the in-process JIT lane are `mem_guard.rs` — guard pages included. The JIT
arm therefore measures the **in-process JIT lane**, which shares the
interpreter's allocator; it does not and cannot measure the cranelift *backend*
allocator of a finished native artifact.

That is still a worthwhile assertion — it pins the allocator the JIT lane
actually binds — but it is NOT evidence about the matrix's `cranelift` row.

## Backend coverage

The `interpreter` and in-process `jit` lanes are exercised here directly.

**Scoped out (no automated coverage):** the true cranelift/llvm *native-linked*
allocator. Reaching it requires a full `native-build` (minutes, not seconds),
which is why both native rows are asserted here only statically. `llvm` was
measured by hand on 2026-08-02 and is recorded in
`doc/08_tracking/bug/mem_infra_guard_row_false_on_native_backends_2026-07-31.md`
— the native binary survived the UAF at `SIMPLE_MEM_GUARD_RATE=1`, and `nm`
showed it binds a plain-`malloc` C `rt_alloc`, the same no-guard implementation
cranelift resolves. Its matrix row is still asserted here as a static check.

## Related Specifications

- test/01_unit/compiler/interp/mem_guard_rate_spec.spl — sampling-count gate (interpreter only)
- test/01_unit/lib/mem_infra/config_spec.spl — matrix/resolution unit contract
- doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md

## Scenarios

### guard capability-matrix row matches observed guard-page behaviour

#### traps a use-after-free on the interpreter, which claims guard: true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- traps a use-after-free on the interpreter, which claims guard: true
- Confirm the matrix claims guard support on the interpreter
- Sabotage control: with the guard knob unset the same UAF must survive
- With SIMPLE_MEM_GUARD_RATE=1 the UAF must NOT survive - the guard page traps it


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("traps a use-after-free on the interpreter, which claims guard: true")
step("Confirm the matrix claims guard support on the interpreter")
assert_equal(mem_infra_row_supported("guard", "interpreter"), true)

step("Sabotage control: with the guard knob unset the same UAF must survive")
assert_equal(survived_uaf("interpreter", false), true)

step("With SIMPLE_MEM_GUARD_RATE=1 the UAF must NOT survive - the guard page traps it")
assert_equal(survived_uaf("interpreter", true), false)
```

</details>

#### traps a use-after-free on the in-process JIT lane, which shares the interpreter allocator

- traps a use-after-free on the in-process JIT lane, which shares the interpreter allocator
- Sabotage control: with the guard knob unset the same UAF survives
- With SIMPLE_MEM_GUARD_RATE=1 the UAF must NOT survive on the JIT lane either
- The matrix row for the natively-linked cranelift backend is still guard: false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("traps a use-after-free on the in-process JIT lane, which shares the interpreter allocator")
# See "What the JIT arm actually measures" above. This arm pins the
# allocator the JIT lane really binds (mem_guard.rs, via the
# rt_interp_call trampoline) - it is NOT evidence about the cranelift
# matrix row, which describes a natively-linked artifact.
step("Sabotage control: with the guard knob unset the same UAF survives")
assert_equal(survived_uaf("jit", false), true)

step("With SIMPLE_MEM_GUARD_RATE=1 the UAF must NOT survive on the JIT lane either")
assert_equal(survived_uaf("jit", true), false)

step("The matrix row for the natively-linked cranelift backend is still guard: false")
# Not measured by the arm above; hand-measured native-build evidence is
# in doc/08_tracking/bug/mem_infra_guard_row_false_on_native_backends_2026-07-31.md.
assert_equal(mem_infra_row_supported("guard", "cranelift"), false)
```

</details>

#### claims guard: false on llvm, which links the same no-guard C rt_alloc as cranelift

- claims guard: false on llvm, which links the same no-guard C rt_alloc as cranelift
- Confirm the matrix does not claim guard support on llvm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("claims guard: false on llvm, which links the same no-guard C rt_alloc as cranelift")
step("Confirm the matrix does not claim guard support on llvm")
assert_equal(mem_infra_row_supported("guard", "llvm"), false)
```

</details>

#### never expands auto into guard on a backend that cannot honour it

- never expands auto into guard on a backend that cannot honour it
- auto on the interpreter includes guard - it is genuinely supported there
- auto on cranelift and llvm must omit guard rather than silently claim it


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never expands auto into guard on a backend that cannot honour it")
step("auto on the interpreter includes guard - it is genuinely supported there")
assert_equal(_contains(mem_infra_auto_rows("interpreter"), "guard"), true)

step("auto on cranelift and llvm must omit guard rather than silently claim it")
assert_equal(_contains(mem_infra_auto_rows("cranelift"), "guard"), false)
assert_equal(_contains(mem_infra_auto_rows("llvm"), "guard"), false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MEM-GUARD-BACKEND-PARITY-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3fc3ffa6f0cb16da63c18ed25fae40279e3e0668cc75bd871601aef6d298110`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3fc3ffa6f0cb16da63c18ed25fae40279e3e0668cc75bd871601aef6d298110`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3fc3ffa6f0cb16da63c18ed25fae40279e3e0668cc75bd871601aef6d298110`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl
mirror: doc/06_spec/01_unit/lib/mem_infra/guard_backend_parity_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/mem_infra/guard_backend_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/mem_infra/guard_backend_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'traps a use-after-free on the interpreter, which claims guard: true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'traps a use-after-free on the in-process JIT lane, which shares the interpreter allocator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'claims guard: false on llvm, which links the same no-guard C rt_alloc as cranelift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
