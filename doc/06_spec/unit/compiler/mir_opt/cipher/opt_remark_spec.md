# Opt Remark Specification

> Tests covering pattern_idiom_stats_with_remark — cipher_remark=true, pattern_idiom_stats_zero — cipher_remark=false, run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + AES callee, run_pattern_idiom_pass_x86 — cipher_remark=false + AES caps + AES callee, run_pattern_idiom_pass_x86 — cipher_remark=true + no caps + AES callee, run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + non-cipher callee, run_pattern_idiom_pass_x86 — SHA256 callee + sha_ni caps + cipher_remark=true, run_pattern_idiom_pass_x86 — CRC32 callee + sse42 caps + cipher_remark=true.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opt Remark Specification

## Scenarios

### pattern_idiom_stats_with_remark — cipher_remark=true

#### returns stats with cipher_remark set to true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns stats with cipher_remark set to true
   - Expected: s.cipher_remark is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns stats with cipher_remark set to true")
val s = pattern_idiom_stats_with_remark()
expect(s.cipher_remark).to_equal(true)
```

</details>

#### starts with zero cipher_hits

- starts with zero cipher_hits
   - Expected: s.cipher_hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with zero cipher_hits")
val s = pattern_idiom_stats_with_remark()
expect(s.cipher_hits).to_equal(0)
```

</details>

### pattern_idiom_stats_zero — cipher_remark=false

#### returns stats with cipher_remark set to false

- returns stats with cipher_remark set to false
   - Expected: s.cipher_remark is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns stats with cipher_remark set to false")
val s = pattern_idiom_stats_zero()
expect(s.cipher_remark).to_equal(false)
```

</details>

### run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + AES callee

#### instruction becomes Intrinsic when cipher_remark=true

- instruction becomes Intrinsic when cipher_remark=true
   - Expected: is_intrinsic is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("instruction becomes Intrinsic when cipher_remark=true")
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_aes()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_intrinsic = match inst.kind:
    case Intrinsic(dest, name, args): true
    case _: false
expect(is_intrinsic).to_equal(true)
```

</details>

#### intrinsic name is crypto_aes_round when cipher_remark=true

- intrinsic name is crypto_aes_round when cipher_remark=true
   - Expected: intrinsic_name equals `crypto_aes_round`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("intrinsic name is crypto_aes_round when cipher_remark=true")
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_aes()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val intrinsic_name = match inst.kind:
    case Intrinsic(dest, name, args): name
    case _: ""
expect(intrinsic_name).to_equal("crypto_aes_round")
```

</details>

### run_pattern_idiom_pass_x86 — cipher_remark=false + AES caps + AES callee

#### instruction still becomes Intrinsic when cipher_remark=false

- instruction still becomes Intrinsic when cipher_remark=false
   - Expected: is_intrinsic is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("instruction still becomes Intrinsic when cipher_remark=false")
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_aes()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_intrinsic = match inst.kind:
    case Intrinsic(dest, name, args): true
    case _: false
expect(is_intrinsic).to_equal(true)
```

</details>

### run_pattern_idiom_pass_x86 — cipher_remark=true + no caps + AES callee

#### instruction stays Call when caps lack AES

- instruction stays Call when caps lack AES
   - Expected: is_call is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("instruction stays Call when caps lack AES")
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_none()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_call = match inst.kind:
    case Call(dest, func_op, args): true
    case _: false
expect(is_call).to_equal(true)
```

</details>

### run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + non-cipher callee

#### instruction stays Call for non-cipher callee

- instruction stays Call for non-cipher callee
   - Expected: is_call is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("instruction stays Call for non-cipher callee")
val m    = make_call_module("std.io.print")
val caps = make_x86_caps_aes()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_call = match inst.kind:
    case Call(dest, func_op, args): true
    case _: false
expect(is_call).to_equal(true)
```

</details>

### run_pattern_idiom_pass_x86 — SHA256 callee + sha_ni caps + cipher_remark=true

#### SHA256 call becomes Intrinsic with sha_ni caps and cipher_remark=true

- SHA256 call becomes Intrinsic with sha_ni caps and cipher_remark=true
   - Expected: is_intrinsic is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA256 call becomes Intrinsic with sha_ni caps and cipher_remark=true")
val m    = make_call_module("std.common.crypto.sha256.compress_block")
val caps = make_x86_caps_sha_ni()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_intrinsic = match inst.kind:
    case Intrinsic(dest, name, args): true
    case _: false
expect(is_intrinsic).to_equal(true)
```

</details>

### run_pattern_idiom_pass_x86 — CRC32 callee + sse42 caps + cipher_remark=true

#### CRC32 call becomes Intrinsic with sse42 caps and cipher_remark=true

- CRC32 call becomes Intrinsic with sse42 caps and cipher_remark=true
   - Expected: is_intrinsic is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRC32 call becomes Intrinsic with sse42 caps and cipher_remark=true")
val m    = make_call_module("std.common.crypto.crc32.update_byte")
val caps = make_x86_caps_sse42()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_intrinsic = match inst.kind:
    case Intrinsic(dest, name, args): true
    case _: false
expect(is_intrinsic).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/mir_opt/cipher/opt_remark_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pattern_idiom_stats_with_remark — cipher_remark=true, pattern_idiom_stats_zero — cipher_remark=false, run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + AES callee, run_pattern_idiom_pass_x86 — cipher_remark=false + AES caps + AES callee, run_pattern_idiom_pass_x86 — cipher_remark=true + no caps + AES callee, run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + non-cipher callee, run_pattern_idiom_pass_x86 — SHA256 callee + sha_ni caps + cipher_remark=true, run_pattern_idiom_pass_x86 — CRC32 callee + sse42 caps + cipher_remark=true.
- pattern_idiom_stats_with_remark — cipher_remark=true
- pattern_idiom_stats_zero — cipher_remark=false
- run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + AES callee
- run_pattern_idiom_pass_x86 — cipher_remark=false + AES caps + AES callee
- run_pattern_idiom_pass_x86 — cipher_remark=true + no caps + AES callee
- run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + non-cipher callee
- run_pattern_idiom_pass_x86 — SHA256 callee + sha_ni caps + cipher_remark=true
- run_pattern_idiom_pass_x86 — CRC32 callee + sse42 caps + cipher_remark=true

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `9ff7e413e5bea400ed853ce2ba9376726b47f79cb78feeebec4b37c9e6381421`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9ff7e413e5bea400ed853ce2ba9376726b47f79cb78feeebec4b37c9e6381421`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9ff7e413e5bea400ed853ce2ba9376726b47f79cb78feeebec4b37c9e6381421`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/mir_opt/cipher/opt_remark_spec.spl
mirror: doc/06_spec/unit/compiler/mir_opt/cipher/opt_remark_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mir_opt/cipher/opt_remark_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mir_opt/cipher/opt_remark_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mir_opt/cipher/opt_remark_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/mir_opt/cipher/opt_remark_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns stats with cipher_remark set to true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/cipher/opt_remark_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with zero cipher_hits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/cipher/opt_remark_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns stats with cipher_remark set to false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
