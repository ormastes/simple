# csprng_salt_iv_spec

> Security spec — salt/IV/nonce generators must use the OS CSPRNG.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# csprng_salt_iv_spec

Security spec — salt/IV/nonce generators must use the OS CSPRNG.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/07_security/csprng_salt_iv_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Security spec — salt/IV/nonce generators must use the OS CSPRNG.

Regression guard for the weak-randomness family swept on 2026-08-08:

  - `std.bcrypt.salt.generate_random_bytes` used a constant-seeded LCG
    (seed=12345), so every bcrypt salt and every password-reset token
    was byte-for-byte identical. Its exact old output for count=4 was
    126,223,44,245.
  - `tls._TlsUtilities.hex_encoding.generate_random` used an LCG seeded
    ONLY from the `length` argument, so TLS server_random was constant
    for a given length across every handshake and every process. Its
    exact old output for length=4 was 180,2,59,33.

Both now draw from the OS CSPRNG via the `rt_random_i64` extern.

## Scenarios

### CSPRNG-backed salt and nonce generation

#### bcrypt generate_random_bytes does not reproduce the old LCG stream

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bcrypt generate_random_bytes does not reproduce the old LCG stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("bcrypt generate_random_bytes does not reproduce the old LCG stream")
val a = generate_random_bytes(4)
val a0: i64 = a[0]
val a1: i64 = a[1]
expect (a0 == OLD_BCRYPT_LCG_0 and a1 == OLD_BCRYPT_LCG_1) == false
```

</details>

#### bcrypt generate_random_bytes returns distinct output on successive calls

- bcrypt generate_random_bytes returns distinct output on successive calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("bcrypt generate_random_bytes returns distinct output on successive calls")
val a = generate_random_bytes(16)
val b = generate_random_bytes(16)
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

#### bcrypt generate_random_bytes yields in-range bytes

- bcrypt generate_random_bytes yields in-range bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("bcrypt generate_random_bytes yields in-range bytes")
val a = generate_random_bytes(16)
var bad = 0
var i = 0
while i < 16:
    val av: i64 = a[i]
    if av < 0:
        bad = bad + 1
    if av > 255:
        bad = bad + 1
    i = i + 1
expect bad == 0
expect a.length() == 16
```

</details>

#### TLS generate_random does not reproduce the old length-seeded LCG stream

- TLS generate_random does not reproduce the old length-seeded LCG stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("TLS generate_random does not reproduce the old length-seeded LCG stream")
val t = generate_random(4)
val t0: i64 = t[0]
val t1: i64 = t[1]
expect (t0 == OLD_TLS_LCG_0 and t1 == OLD_TLS_LCG_1) == false
```

</details>

#### TLS generate_random returns distinct output on successive calls

- TLS generate_random returns distinct output on successive calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("TLS generate_random returns distinct output on successive calls")
val a = generate_random(32)
val b = generate_random(32)
var same = 0
var i = 0
while i < 32:
    val av: i64 = a[i]
    val bv: i64 = b[i]
    if av == bv:
        same = same + 1
    i = i + 1
expect same < 32
```

</details>

#### TLS generate_random yields in-range bytes of the requested length

- TLS generate_random yields in-range bytes of the requested length


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SECURITY
step("TLS generate_random yields in-range bytes of the requested length")
val t = generate_random(32)
var bad = 0
var i = 0
while i < 32:
    val tv: i64 = t[i]
    if tv < 0:
        bad = bad + 1
    if tv > 255:
        bad = bad + 1
    i = i + 1
expect bad == 0
expect t.length() == 32
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `17de12916b52a5c82916fb19f31d74bc260d088495cf9015e0d078c08c8a4731`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17de12916b52a5c82916fb19f31d74bc260d088495cf9015e0d078c08c8a4731`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17de12916b52a5c82916fb19f31d74bc260d088495cf9015e0d078c08c8a4731`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/07_security/csprng_salt_iv_spec.spl
mirror: doc/06_spec/07_security/csprng_salt_iv_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/07_security/csprng_salt_iv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/07_security/csprng_salt_iv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/07_security/csprng_salt_iv_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bcrypt generate_random_bytes does not reproduce the old LCG stream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/07_security/csprng_salt_iv_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bcrypt generate_random_bytes returns distinct output on successive calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/07_security/csprng_salt_iv_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bcrypt generate_random_bytes yields in-range bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
