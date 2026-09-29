# hardening_preset_policy_spec

> Hardening preset policy — regression + opt-out contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hardening_preset_policy_spec

Hardening preset policy — regression + opt-out contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hardening_preset_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Hardening preset policy — regression + opt-out contract.

AC-8 (simpleos-alpine-harden-musl-busybox): PIE/SSP/RELRO must be an
additive per-preset policy. Desktop/Hosted stays unconditionally hardened.
Embedded gains an opt-out. SSP is config-only (codegen deferred).

REGRESSION GUARD: Hosted assertions must always pass — desktop link flags
must remain byte-identical (PIE + RELRO + bind-now always on).

## Scenarios

### Hardening preset policy

#### Hosted preset (regression guard — desktop stays fully hardened)

#### PIE is on

- PIE is on
   - Expected: h.pie is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PIE is on")
val h = resolve_hardening("hosted")
expect(h.pie).to_equal(true)
```

</details>

#### SSP is on

- SSP is on
   - Expected: h.ssp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SSP is on")
val h = resolve_hardening("hosted")
expect(h.ssp).to_equal(true)
```

</details>

#### RELRO is on

- RELRO is on
   - Expected: h.relro is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RELRO is on")
val h = resolve_hardening("hosted")
expect(h.relro).to_equal(true)
```

</details>

#### bind-now is on

- bind-now is on
   - Expected: h.bind_now is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bind-now is on")
val h = resolve_hardening("hosted")
expect(h.bind_now).to_equal(true)
```

</details>

#### Baremetal preset (embedded opt-out)

#### PIE is off

- PIE is off
   - Expected: h.pie is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PIE is off")
val h = resolve_hardening("baremetal")
expect(h.pie).to_equal(false)
```

</details>

#### SSP is off

- SSP is off
   - Expected: h.ssp is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SSP is off")
val h = resolve_hardening("baremetal")
expect(h.ssp).to_equal(false)
```

</details>

#### RELRO is off

- RELRO is off
   - Expected: h.relro is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RELRO is off")
val h = resolve_hardening("baremetal")
expect(h.relro).to_equal(false)
```

</details>

#### bind-now is off

- bind-now is off
   - Expected: h.bind_now is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bind-now is off")
val h = resolve_hardening("baremetal")
expect(h.bind_now).to_equal(false)
```

</details>

#### EmbeddedWithHeap preset (configurable middle tier)

#### PIE is off

- PIE is off
   - Expected: h.pie is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PIE is off")
val h = resolve_hardening("embedded_with_heap")
expect(h.pie).to_equal(false)
```

</details>

#### SSP is off

- SSP is off
   - Expected: h.ssp is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SSP is off")
val h = resolve_hardening("embedded_with_heap")
expect(h.ssp).to_equal(false)
```

</details>

#### RELRO is on (MMU present, keep GOT protection)

- RELRO is on (MMU present, keep GOT protection)
   - Expected: h.relro is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RELRO is on (MMU present, keep GOT protection)")
val h = resolve_hardening("embedded_with_heap")
expect(h.relro).to_equal(true)
```

</details>

#### bind-now is on

- bind-now is on
   - Expected: h.bind_now is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bind-now is on")
val h = resolve_hardening("embedded_with_heap")
expect(h.bind_now).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c5ceb6a34cdec6056ca088f9758b40afa8217dc5df7f7adf91e84ce96c745168`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5ceb6a34cdec6056ca088f9758b40afa8217dc5df7f7adf91e84ce96c745168`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5ceb6a34cdec6056ca088f9758b40afa8217dc5df7f7adf91e84ce96c745168`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hardening_preset_policy_spec.spl
mirror: doc/06_spec/01_unit/compiler/hardening_preset_policy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hardening_preset_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hardening_preset_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hardening_preset_policy_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PIE is on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hardening_preset_policy_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SSP is on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hardening_preset_policy_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RELRO is on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
