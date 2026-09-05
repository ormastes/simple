# Sendfile Routing Specification

> Validates the sendfile routing module:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sendfile Routing Specification

Validates the sendfile routing module:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | FR-NET-0003 (WQ-2) |
| Category | Stdlib / HTTP / Static-File Routing |
| Difficulty | 2/5 |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http/sendfile_routing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the sendfile routing module:
- portable-read fallback when sendfile unavailable
- sendfile selected when supported
- zero-copy does NOT route to sendfile when unsupported
- explicit backend label returned for the verification gate

## Scenarios

### Portable-read fallback when sendfile unavailable (WQ-2a)

#### portable backend with file body routes to PortableRead

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- portable backend with file body routes to PortableRead
   - Expected: label equals `portable-read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("portable backend with file body routes to PortableRead")
val caps = sendfile_caps_portable("poll-socket")
val backend = route_sendfile(caps, true)
val label = sendfile_backend_label(backend)
expect(label).to_equal("portable-read")
```

</details>

#### portable backend detection returns false

- portable backend detection returns false
   - Expected: detect_sendfile_support(caps) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("portable backend detection returns false")
val caps = sendfile_caps_portable("poll-socket")
expect(detect_sendfile_support(caps)).to_equal(false)
```

</details>

#### portable backend guard passes for PortableRead

- portable backend guard passes for PortableRead
   - Expected: sendfile_guard_ok(caps, backend) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("portable backend guard passes for PortableRead")
val caps = sendfile_caps_portable("poll-socket")
val backend = route_sendfile(caps, true)
expect(sendfile_guard_ok(caps, backend)).to_equal(true)
```

</details>

### Sendfile selected when supported (WQ-2b)

#### sendfile backend with file body routes to Sendfile

- sendfile backend with file body routes to Sendfile
   - Expected: label equals `sendfile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sendfile backend with file body routes to Sendfile")
val caps = sendfile_caps_with_sendfile("io-uring")
val backend = route_sendfile(caps, true)
val label = sendfile_backend_label(backend)
expect(label).to_equal("sendfile")
```

</details>

#### sendfile backend detection returns true

- sendfile backend detection returns true
   - Expected: detect_sendfile_support(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sendfile backend detection returns true")
val caps = sendfile_caps_with_sendfile("io-uring")
expect(detect_sendfile_support(caps)).to_equal(true)
```

</details>

#### full backend with file body routes to Sendfile

- full backend with file body routes to Sendfile
   - Expected: label equals `sendfile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full backend with file body routes to Sendfile")
val caps = sendfile_caps_full("io-uring-zc")
val backend = route_sendfile(caps, true)
val label = sendfile_backend_label(backend)
expect(label).to_equal("sendfile")
```

</details>

#### sendfile guard passes for Sendfile on capable backend

- sendfile guard passes for Sendfile on capable backend
   - Expected: sendfile_guard_ok(caps, backend) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sendfile guard passes for Sendfile on capable backend")
val caps = sendfile_caps_with_sendfile("io-uring")
val backend = route_sendfile(caps, true)
expect(sendfile_guard_ok(caps, backend)).to_equal(true)
```

</details>

### Zero-copy does NOT route to sendfile when unsupported (WQ-2c)

#### zero-copy-only backend with file body routes to PortableRead

- zero-copy-only backend with file body routes to PortableRead
   - Expected: label equals `portable-read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-copy-only backend with file body routes to PortableRead")
val caps = sendfile_caps_with_zero_copy("dpdk-zc")
val backend = route_sendfile(caps, true)
val label = sendfile_backend_label(backend)
expect(label).to_equal("portable-read")
```

</details>

#### zero-copy-only backend detection returns false for sendfile

- zero-copy-only backend detection returns false for sendfile
   - Expected: detect_sendfile_support(caps) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-copy-only backend detection returns false for sendfile")
val caps = sendfile_caps_with_zero_copy("dpdk-zc")
expect(detect_sendfile_support(caps)).to_equal(false)
```

</details>

#### zero-copy-only guard rejects manually constructed Sendfile

- zero-copy-only guard rejects manually constructed Sendfile
   - Expected: sendfile_guard_ok(caps, SendfileBackend.Sendfile) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-copy-only guard rejects manually constructed Sendfile")
val caps = sendfile_caps_with_zero_copy("dpdk-zc")
expect(sendfile_guard_ok(caps, SendfileBackend.Sendfile)).to_equal(false)
```

</details>

#### zero-copy-only guard passes for PortableRead

- zero-copy-only guard passes for PortableRead
   - Expected: sendfile_guard_ok(caps, SendfileBackend.PortableRead) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-copy-only guard passes for PortableRead")
val caps = sendfile_caps_with_zero_copy("dpdk-zc")
expect(sendfile_guard_ok(caps, SendfileBackend.PortableRead)).to_equal(true)
```

</details>

### Explicit backend label for verification gate (WQ-2d)

#### Sendfile label is sendfile

- Sendfile label is sendfile
   - Expected: sendfile_backend_label(SendfileBackend.Sendfile) equals `sendfile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sendfile label is sendfile")
expect(sendfile_backend_label(SendfileBackend.Sendfile)).to_equal("sendfile")
```

</details>

#### PortableRead label is portable-read

- PortableRead label is portable-read
   - Expected: sendfile_backend_label(SendfileBackend.PortableRead) equals `portable-read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PortableRead label is portable-read")
expect(sendfile_backend_label(SendfileBackend.PortableRead)).to_equal("portable-read")
```

</details>

#### Unsupported label is unsupported

- Unsupported label is unsupported
   - Expected: sendfile_backend_label(SendfileBackend.Unsupported) equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Unsupported label is unsupported")
expect(sendfile_backend_label(SendfileBackend.Unsupported)).to_equal("unsupported")
```

</details>

#### no-file-body routes to Unsupported

- no-file-body routes to Unsupported
   - Expected: label equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no-file-body routes to Unsupported")
val caps = sendfile_caps_with_sendfile("io-uring")
val backend = route_sendfile(caps, false)
val label = sendfile_backend_label(backend)
expect(label).to_equal("unsupported")
```

</details>

#### guard passes for Unsupported on any backend

- guard passes for Unsupported on any backend
   - Expected: sendfile_guard_ok(caps, SendfileBackend.Unsupported) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard passes for Unsupported on any backend")
val caps = sendfile_caps_portable("poll-socket")
expect(sendfile_guard_ok(caps, SendfileBackend.Unsupported)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `39d302732890f1107042538b9df000e9f30b4b91d889c264e713b636edefdbb3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `39d302732890f1107042538b9df000e9f30b4b91d889c264e713b636edefdbb3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `39d302732890f1107042538b9df000e9f30b4b91d889c264e713b636edefdbb3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/http/sendfile_routing_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/http/sendfile_routing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/http/sendfile_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/http/sendfile_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/http/sendfile_routing_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'portable backend with file body routes to PortableRead' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http/sendfile_routing_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'portable backend detection returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http/sendfile_routing_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'portable backend guard passes for PortableRead' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
