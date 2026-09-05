# `harden` Capability-Matrix Row vs Observed Quarantine Behaviour

> `mem_infra_matrix()` in `src/lib/common/mem_infra/config.spl` advertises, per backend, whether `--mem-infra=harden` gives you write-after-free detection. A capability matrix is a safety claim: someone reads `harden: true`, enables it, runs a clean check, and concludes their heap is not being corrupted.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `harden` Capability-Matrix Row vs Observed Quarantine Behaviour

`mem_infra_matrix()` in `src/lib/common/mem_infra/config.spl` advertises, per backend, whether `--mem-infra=harden` gives you write-after-free detection. A capability matrix is a safety claim: someone reads `harden: true`, enables it, runs a clean check, and concludes their heap is not being corrupted.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/mem_infra/harden_backend_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`mem_infra_matrix()` in `src/lib/common/mem_infra/config.spl` advertises, per
backend, whether `--mem-infra=harden` gives you write-after-free detection. A
capability matrix is a safety claim: someone reads `harden: true`, enables it,
runs a clean check, and concludes their heap is not being corrupted.

Until 2026-08-02 that row read `interpreter: true, cranelift: true, llvm: true`
and it had never been verified on any backend. One of the three was false. This
spec is the sibling of `guard_backend_parity_spec.spl`, which corrected the same
class of unverified claim on the `guard` row.

## What is actually measured

`harden` is a quarantine allocator: `rt_free` poisons the user bytes with 0xDE
and parks the block in a ring instead of releasing it; a check call reports how
many parked blocks are no longer all-poison.

The probe makes that count **differential** — three blocks are freed, then
tampered one at a time:

| observed sequence | meaning |
|-------------------|---------|
| `t0=0 t1=1 t2=2 t3=3` | the count tracks OUR writes exactly — harden is real |
| `t0=0 t1=0 t2=0 t3=0` | nothing was quarantined — harden is inert |

This distinction matters more than it looks. A check that returns a flat 0 is
indistinguishable from a check whose symbol failed to resolve, and under
cranelift an unresolved extern silently returns 0 rather than erroring. A flat
`3,3,3,3` would mean the ring is populated but never poisoned. Only the
monotonic 0,1,2,3 is positive evidence of working detection.

## Per-backend result (measured 2026-08-02, Rust seed)

- **interpreter — true.** `rt_mem_harden_check()` reports 1 after a
  write-after-free and 0 before it; the freed bytes read back as
  0xDEDEDEDEDEDEDEDE.
- **in-process JIT lane — true.** The tamper count tracks exactly (0,1,2,3).

  CORRECTED 2026-08-09. An earlier version of this note claimed "the seed
  process links the C quarantine from `src/runtime/runtime_memory.c`". It does
  not. `bin/simple run` under `SIMPLE_EXECUTION_MODE=jit` resolves externs
  through the `rt_interp_call` trampoline into the same Rust dispatch table the
  interpreter uses, so the quarantine exercised here is `memory.rs`, not the C
  one. Until 2026-08-09 the `_native` spelling was simply **not registered** in
  that table: every call logged "unknown extern function" and yielded 0, so
  this arm read `t0=0 t1=0 t2=0 t3=0` — bit-identical to the knob-off sabotage
  control below, which was therefore vacuous exactly when it mattered. Fixed by
  registering `rt_mem_harden_check_native` alongside `rt_mem_harden_check` in
  `interpreter_extern/mod.rs`; this also resolves
  `doc/08_tracking/bug/mem_infra_harden_check_symbol_divergence_2026-08-02.md`
  for both lanes that consult that table.

  This arm is NOT evidence about a natively-linked cranelift artifact — that
  needs a full `native-build` and has no automated coverage. See
  `doc/08_tracking/bug/mem_infra_parity_specs_cranelift_arm_demotes_to_interpreter_2026-08-09.md`.
- **llvm — FALSE, corrected.** `native-build` links the `simple-core` runtime
  lane, whose `rt_alloc` comes from `runtime_native.c`: plain `malloc`, no
  quarantine, no poison, not even a `getenv` gate. `runtime_memory.o` is not in
  that lane, so a probe calling the check does not link at all
  (`ld.lld: error: undefined symbol: rt_mem_harden_check_native`) and
  `SIMPLE_MEM_HARDEN=1` is inert in a finished native artifact.

The two `rt_alloc` definitions are NOT resolved by `-z muldefs`
first-definition-wins: each runtime archive contains exactly one of them, so no
duplicate-symbol choice is ever made. It is lane selection, not symbol
shadowing.

## Sabotage control

Every backend arm is run twice: once with `SIMPLE_MEM_HARDEN=1` and once with
the knob unset. The knob-off run must report a flat zero everywhere. That is
what makes the detection meaningful — it shows the counts are caused by harden
being switched on, not by the fixture reporting numbers regardless.

## Backend coverage

`interpreter` and `cranelift` are exercised here directly. `llvm` needs a full
`native-build` (minutes, not seconds) so it is asserted statically here and was
measured by hand; the transcript is in the bug doc above. Its row is still
checked so the matrix cannot drift back.

## Related Specifications

- test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl — the sibling row
- test/01_unit/lib/mem_infra/config_spec.spl — matrix/resolution unit contract
- doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md

## Scenarios

### harden capability-matrix row matches observed quarantine behaviour

#### detects write-after-free on the interpreter, which claims harden: true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects write-after-free on the interpreter, which claims harden: true
- Confirm the matrix claims harden support on the interpreter
- With SIMPLE_MEM_HARDEN=1 the tampered block is reported
- Sabotage control: with the knob unset nothing is quarantined


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects write-after-free on the interpreter, which claims harden: true")
step("Confirm the matrix claims harden support on the interpreter")
assert_equal(mem_infra_row_supported("harden", "interpreter"), true)

step("With SIMPLE_MEM_HARDEN=1 the tampered block is reported")
val harden_on = run_fixture("interpreter", POISON_FIXTURE, true)
assert_equal(harden_on.contains("tampered_check=1"), true)

step("Sabotage control: with the knob unset nothing is quarantined")
val harden_off = run_fixture("interpreter", POISON_FIXTURE, false)
assert_equal(harden_off.contains("tampered_check=0"), true)
```

</details>

#### detects write-after-free on the in-process JIT lane, which claims harden: true

- detects write-after-free on the in-process JIT lane, which claims harden: true
- Confirm the matrix claims harden support on cranelift
- With SIMPLE_MEM_HARDEN=1 the tamper count tracks our writes exactly
- Sabotage control: with the knob unset every count stays zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects write-after-free on the in-process JIT lane, which claims harden: true")
step("Confirm the matrix claims harden support on cranelift")
assert_equal(mem_infra_row_supported("harden", "cranelift"), true)

step("With SIMPLE_MEM_HARDEN=1 the tamper count tracks our writes exactly")
val harden_on = run_fixture("jit", TAMPER_FIXTURE, true)
assert_equal(harden_on.contains("t0=0"), true)
assert_equal(harden_on.contains("t1=1"), true)
assert_equal(harden_on.contains("t2=2"), true)
assert_equal(harden_on.contains("t3=3"), true)

step("Sabotage control: with the knob unset every count stays zero")
val harden_off = run_fixture("jit", TAMPER_FIXTURE, false)
assert_equal(harden_off.contains("t0=0"), true)
assert_equal(harden_off.contains("t1=0"), true)
assert_equal(harden_off.contains("t2=0"), true)
assert_equal(harden_off.contains("t3=0"), true)
```

</details>

#### claims harden: false on llvm, whose core runtime lane has no quarantine

- claims harden: false on llvm, whose core runtime lane has no quarantine
- The matrix must NOT claim harden support on llvm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("claims harden: false on llvm, whose core runtime lane has no quarantine")
step("The matrix must NOT claim harden support on llvm")
assert_equal(mem_infra_row_supported("harden", "llvm"), false)
```

</details>

#### never expands auto into harden on a backend that cannot honour it

- never expands auto into harden on a backend that cannot honour it
- auto must omit harden on llvm rather than silently claim it


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never expands auto into harden on a backend that cannot honour it")
step("auto must omit harden on llvm rather than silently claim it")
assert_equal(_contains(mem_infra_auto_rows("llvm"), "harden"), false)
```

</details>

#### never degrades another row into harden on llvm, where harden is inert

- never degrades another row into harden on llvm, where harden is inert
- strict on cranelift may degrade to harden - it is real there
- strict on llvm must error instead of enabling an inert harden
- asan on llvm is natively supported, so it never reaches a fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never degrades another row into harden on llvm, where harden is inert")
step("strict on cranelift may degrade to harden - it is real there")
val cl = resolve_mem_infra(["strict"], "cranelift", false)
assert_equal(_contains(cl.enabled, "harden"), true)
assert_equal(cl.errors.len(), 0)

step("strict on llvm must error instead of enabling an inert harden")
val llvm = resolve_mem_infra(["strict"], "llvm", false)
assert_equal(_contains(llvm.enabled, "harden"), false)
assert_equal(llvm.errors.len(), 1)

step("asan on llvm is natively supported, so it never reaches a fallback")
val asan = resolve_mem_infra(["asan"], "llvm", false)
assert_equal(_contains(asan.enabled, "asan"), true)
assert_equal(asan.errors.len(), 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MEM-HARDEN-BACKEND-PARITY-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `df2b3f8b13f3e7e117347434e96f897af38166ba49b0b4ba154b7b27603b2bd1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df2b3f8b13f3e7e117347434e96f897af38166ba49b0b4ba154b7b27603b2bd1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df2b3f8b13f3e7e117347434e96f897af38166ba49b0b4ba154b7b27603b2bd1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/mem_infra/harden_backend_parity_spec.spl
mirror: doc/06_spec/01_unit/lib/mem_infra/harden_backend_parity_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/mem_infra/harden_backend_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/mem_infra/harden_backend_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/mem_infra/harden_backend_parity_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/mem_infra/harden_backend_parity_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects write-after-free on the interpreter, which claims harden: true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/mem_infra/harden_backend_parity_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects write-after-free on the in-process JIT lane, which claims harden: true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/mem_infra/harden_backend_parity_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'claims harden: false on llvm, whose core runtime lane has no quarantine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
