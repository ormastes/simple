# predictable_iv_key_session_id_spec

> Security spec — AES IV/key and web session IDs must use the OS CSPRNG.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# predictable_iv_key_session_id_spec

Security spec — AES IV/key and web session IDs must use the OS CSPRNG.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/07_security/predictable_iv_key_session_id_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Security spec — AES IV/key and web session IDs must use the OS CSPRNG.

Second sweep of the weak-randomness family (2026-08-17), sibling to
`csprng_salt_iv_spec.spl`. Three more generators were expanding a
CONSTANT seed through the glibc LCG (x = x*1103515245 + 12345 mod 2^31),
or expanding the clock, instead of drawing from the OS CSPRNG:

  - `common.aes.utilities.generate_aes_key(size)` used seed=42, so every
    process produced the SAME AES key. Its exact old output for size=4
    was 27,184,145,246.
  - `common.aes.utilities.generate_iv()` / `generate_nonce()` used
    seed=123, so every call in every process returned the SAME 16-byte
    IV. Under CTR/GCM identical IV + identical key is keystream reuse,
    which leaks plaintext_A XOR plaintext_B outright; under CBC it leaks
    first-block equality. Its exact old output for the first 4 bytes was
    152,241,214,87.
  - `nogc_sync_mut.web_framework.session.generate_session_id()` expanded
    `current_timestamp()` through the fixed multiplier 2654435761, making
    the whole ID a pure function of creation time. A session ID is a
    bearer credential: an attacker who knew roughly when a session was
    created could enumerate the few candidate seconds and recover it.
    Two sessions created in the same clock tick also collided outright.

All three now draw from the OS CSPRNG via the `rt_random_i64` extern.

The generalization each `it` block encodes: a CSPRNG-backed generator
never repeats across successive calls, and never reproduces the exact
byte stream of the seeded generator it replaced.

## Scenarios

### CSPRNG-backed AES key, IV and session-ID generation

#### generate_aes_key does not reproduce the old seed=42 LCG stream

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generate_aes_key does not reproduce the old seed=42 LCG stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("generate_aes_key does not reproduce the old seed=42 LCG stream")
val k = generate_aes_key(16)
val k0: i64 = k[0]
val k1: i64 = k[1]
expect (k0 == OLD_AESKEY_LCG_0 and k1 == OLD_AESKEY_LCG_1) == false
```

</details>

#### generate_aes_key returns a different key on successive calls

- generate_aes_key returns a different key on successive calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("generate_aes_key returns a different key on successive calls")
val a = generate_aes_key(16)
val b = generate_aes_key(16)
var same = 0
var i = 0
while i < 16:
    val av: i64 = a[i]
    val bv: i64 = b[i]
    if av == bv:
        same = same + 1
    i = i + 1
# 16 identical bytes from a real CSPRNG has probability 2^-128.
expect same < 16
```

</details>

#### generate_aes_key yields in-range bytes of the requested size

- generate_aes_key yields in-range bytes of the requested size


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("generate_aes_key yields in-range bytes of the requested size")
val k = generate_aes_key(32)
var bad = 0
var i = 0
while i < 32:
    val kv: i64 = k[i]
    if kv < 0:
        bad = bad + 1
    if kv > 255:
        bad = bad + 1
    i = i + 1
expect bad == 0
expect k.length() == 32
```

</details>

#### generate_iv does not reproduce the old seed=123 LCG stream

- generate_iv does not reproduce the old seed=123 LCG stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("generate_iv does not reproduce the old seed=123 LCG stream")
val iv = generate_iv()
val v0: i64 = iv[0]
val v1: i64 = iv[1]
expect (v0 == OLD_IV_LCG_0 and v1 == OLD_IV_LCG_1) == false
```

</details>

#### generate_iv returns a distinct IV on successive calls

- generate_iv returns a distinct IV on successive calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("generate_iv returns a distinct IV on successive calls")
# This is the keystream-reuse guard: a repeated CTR/GCM IV under
# the same key is a total confidentiality break.
val a = generate_iv()
val b = generate_iv()
var same = 0
var i = 0
while i < 16:
    val av: i64 = a[i]
    val bv: i64 = b[i]
    if av == bv:
        same = same + 1
    i = i + 1
expect same < 16
expect a.length() == 16
```

</details>

#### generate_nonce returns a distinct nonce on successive calls

- generate_nonce returns a distinct nonce on successive calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("generate_nonce returns a distinct nonce on successive calls")
val a = generate_nonce()
val b = generate_nonce()
var same = 0
var i = 0
while i < 16:
    val av: i64 = a[i]
    val bv: i64 = b[i]
    if av == bv:
        same = same + 1
    i = i + 1
expect same < 16
expect a.length() == 16
```

</details>

#### generate_session_id returns a distinct id on successive calls

- generate_session_id returns a distinct id on successive calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("generate_session_id returns a distinct id on successive calls")
# The old clock-derived id collided whenever two sessions were
# created within the same tick; these two calls are back to back.
val a = generate_session_id()
val b = generate_session_id()
expect (a == b) == false
```

</details>

#### generate_session_id yields 16 lowercase hex characters

- generate_session_id yields 16 lowercase hex characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("generate_session_id yields 16 lowercase hex characters")
val sid = generate_session_id()
expect sid.length() == 16
val digits = "0123456789abcdef"
var bad = 0
var i = 0
while i < 16:
    val c = sid.char_at(i)
    if digits.contains(c) == false:
        bad = bad + 1
    i = i + 1
expect bad == 0
```

</details>

#### generate_session_id does not repeat across many draws

- generate_session_id does not repeat across many draws


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("generate_session_id does not repeat across many draws")
# A clock-derived id repeats heavily in a tight loop; a CSPRNG-backed
# 64-bit id effectively never does.
val first = generate_session_id()
var repeats = 0
var i = 0
while i < 32:
    if generate_session_id() == first:
        repeats = repeats + 1
    i = i + 1
expect repeats == 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SECURITY`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2924ef3d3379523f92e2b6f778b9ce111becb7d9356dd6a1aad122fffc7e49f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2924ef3d3379523f92e2b6f778b9ce111becb7d9356dd6a1aad122fffc7e49f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2924ef3d3379523f92e2b6f778b9ce111becb7d9356dd6a1aad122fffc7e49f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/07_security/predictable_iv_key_session_id_spec.spl
mirror: doc/06_spec/07_security/predictable_iv_key_session_id_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/07_security/predictable_iv_key_session_id_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/07_security/predictable_iv_key_session_id_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/07_security/predictable_iv_key_session_id_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generate_aes_key does not reproduce the old seed=42 LCG stream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/07_security/predictable_iv_key_session_id_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generate_aes_key returns a different key on successive calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/07_security/predictable_iv_key_session_id_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generate_aes_key yields in-range bytes of the requested size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
