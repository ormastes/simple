# Name-keyed method dispatch with no receiver type — the defect CLASS

> MIR method-call lowering keys on the method NAME alone; the receiver's TYPE is not part of the dispatch decision. When a name is not recognised as belonging to the receiver's builtin family, lowering falls through to the `str.<name>` arm. `src/runtime/runtime_native.c` (~line 4626) then hits the shared guard

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Name-keyed method dispatch with no receiver type — the defect CLASS

MIR method-call lowering keys on the method NAME alone; the receiver's TYPE is not part of the dispatch decision. When a name is not recognised as belonging to the receiver's builtin family, lowering falls through to the `str.<name>` arm. `src/runtime/runtime_native.c` (~line 4626) then hits the shared guard

## At a Glance

| Field | Value |
|-------|-------|
| Category | Codegen / MIR method-call dispatch (similar-problem detection) |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/nontext_receiver_method_dispatch_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

MIR method-call lowering keys on the method NAME alone; the receiver's TYPE is
not part of the dispatch decision. When a name is not recognised as belonging
to the receiver's builtin family, lowering falls through to the `str.<name>`
arm. `src/runtime/runtime_native.c` (~line 4626) then hits the shared guard

    rt_refuse_non_text_receiver(method, receiver)

which prints

    Runtime error: str.<m> was called on a receiver that is not text. This
    method has no compiled implementation for that receiver type -- a
    code-generation dispatch gap, not a program error.

and `exit(70)`s.

That guard is wired to **exactly seven** names:

    clear, drop, pop, rev, reverse, sorted, take

Every one of them is also a legitimate Dict or Array method. `Dict.clear()` was
found the hard way — a program died in production-shaped code. The other six
were never checked. This spec sweeps the whole guarded set instead of waiting
for each to be discovered individually.

| name | non-text receiver exercised |
|---|---|
| `clear` | Dict **and** Array (two distinct lowering families) |
| `pop` | Array |
| `rev` | Array |
| `reverse` | Array |
| `sorted` | Array |
| `take` | Array |
| `drop` | Array |

## Why one probe file per name

A guard hit is `exit(70)`; a codegen gap can also be a hard PANIC. Either
aborts the process. A combined probe would therefore report only the FIRST
broken name and silently hide every later one — measured: a single combined
fixture reported `array_clear` and nothing after it. Each name is consequently
its own `probe_nontext_receiver_*.spl`, natively built and run in isolation.

## Why this spec shells out

A spec body runs on the tree-walk INTERPRETER, which has no such dispatch gap.
**No in-process example can go red on this class at all.** The only oracle with
teeth is a native build executed as a subprocess.

## The gap has two exit shapes, and both are asserted absent

The runtime guard's `exit(70)` is only one of them. Reverting the `Dict.clear`
fix and native-building the reproducer's probe produces instead:

    PANIC: unresolved method call: clear

with `exit 1` — the lowering never reached the `str.clear` arm at all, it
simply found no arm. Measured 2026-08-17 on the real revert. Both shapes are
the same defect from a caller's point of view (the program dies on a method
the language says exists), so this spec asserts both are absent, plus a
positive `END` marker so the absence checks cannot pass vacuously on an
aborted process.

## Attribution control (measured 2026-08-17)

A natively built fixture using the SAME array shapes but NO guarded method name
(`val a = [1, 2, 3]` then `a[0]` and `a.len()`) prints `CTL idx=1 len=3 END`
and exits 0. Array literals, indexing and `len` are therefore healthy under
native codegen, and the aborts the array probes below produce are attributable
to the guarded method names, not to the surrounding fixture.

## This spec is allowed to be RED

The assertion is deliberately not weakened to accommodate names that are still
broken. A red here names a real, unfixed member of the class and should be
filed, not papered over.

## Scenarios

### every guard-refused method name works on a non-text receiver

#### clears a Dict — the already-fixed member, kept as the control arm

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- clears a Dict — the already-fixed member, kept as the control arm


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears a Dict — the already-fixed member, kept as the control arm")
check_dispatch("dict_clear", "PROBE dict_clear len=0")
```

</details>

#### clears an Array

- clears an Array


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears an Array")
check_dispatch("array_clear", "PROBE array_clear len=0")
```

</details>

#### pops from an Array

- pops from an Array


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pops from an Array")
check_dispatch("array_pop", "PROBE array_pop popped=3")
```

</details>

#### reverses an Array via rev

- reverses an Array via rev


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses an Array via rev")
check_dispatch("array_rev", "PROBE array_rev first=3")
```

</details>

#### reverses an Array via reverse

- reverses an Array via reverse


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses an Array via reverse")
check_dispatch("array_reverse", "PROBE array_reverse first=3")
```

</details>

#### sorts an Array

- sorts an Array


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts an Array")
check_dispatch("array_sorted", "PROBE array_sorted first=1")
```

</details>

#### takes a prefix of an Array

- takes a prefix of an Array


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes a prefix of an Array")
check_dispatch("array_take", "PROBE array_take len=2")
```

</details>

#### drops a prefix of an Array

- drops a prefix of an Array


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops a prefix of an Array")
check_dispatch("array_drop", "PROBE array_drop len=2")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `525e8f729a3357a6351591ed2b974d8bff1a9c4f22f25c55de95526e93c9c63c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `525e8f729a3357a6351591ed2b974d8bff1a9c4f22f25c55de95526e93c9c63c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `525e8f729a3357a6351591ed2b974d8bff1a9c4f22f25c55de95526e93c9c63c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/nontext_receiver_method_dispatch_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/nontext_receiver_method_dispatch_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/nontext_receiver_method_dispatch_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/nontext_receiver_method_dispatch_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/nontext_receiver_method_dispatch_class_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears a Dict — the already-fixed member, kept as the control arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/nontext_receiver_method_dispatch_class_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears an Array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/nontext_receiver_method_dispatch_class_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pops from an Array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
