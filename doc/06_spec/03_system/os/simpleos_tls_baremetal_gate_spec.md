# Simpleos Tls Baremetal Gate Specification

> Tests covering SimpleOS baremetal TLS gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Tls Baremetal Gate Specification

## Scenarios

### SimpleOS baremetal TLS gate

#### reports embedded certificate material once real DER is present

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports embedded certificate material once real DER is present
   - Expected: has_embedded_certs() is true
   - Expected: get_embedded_key_der().len().to_u64() equals `48u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports embedded certificate material once real DER is present")
expect(has_embedded_certs()).to_equal(true)
expect(get_embedded_cert_der().len().to_u64()).to_be_greater_than(256u64)
expect(get_embedded_key_der().len().to_u64()).to_equal(48u64)
```

</details>

#### exposes baremetal TLS info for embedded DER material

- exposes baremetal TLS info for embedded DER material
   - Expected: info.available is true
   - Expected: info.key_der.len().to_u64() equals `48u64`
   - Expected: info.production_ready is false
   - Expected: info.blocker equals `placeholder_entropy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes baremetal TLS info for embedded DER material")
val info = get_baremetal_tls_info()

expect(info.available).to_equal(true)
expect(info.cert_der.len().to_u64()).to_be_greater_than(256u64)
expect(info.key_der.len().to_u64()).to_equal(48u64)
expect(info.production_ready).to_equal(false)
expect(info.blocker).to_equal("placeholder_entropy")
```

</details>

#### keeps TLS production readiness blocked while platform shims are placeholders

- keeps TLS production readiness blocked while platform shims are placeholders
   - Expected: baremetal_tls_platform_ready() is false
   - Expected: baremetal_tls_blocker() equals `placeholder_entropy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps TLS production readiness blocked while platform shims are placeholders")
expect(baremetal_tls_platform_ready()).to_equal(false)
expect(baremetal_tls_blocker()).to_equal("placeholder_entropy")
```

</details>

#### keeps tls13_accept fail-closed without a ClientHello record

- keeps tls13_accept fail-closed without a ClientHello record
   - Expected: "accepted-before-record-io" equals ``
   - Expected: reason equals `no_client_hello_record`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps tls13_accept fail-closed without a ClientHello record")
val config = Tls13ServerConfig(
    cert_chain: [_sample_cert_der()],
    server_pkcs8: _sample_key_der(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)

match tls13_accept_client_hello_record_for_test([], config):
    Tls13AcceptResult.Accepted(_ctx):
        expect("accepted-before-record-io").to_equal("")
    Tls13AcceptResult.Failed(reason):
        expect(reason).to_equal("no_client_hello_record")
```

</details>

#### keeps the boot plan explicit about TLS production blockers

- keeps the boot plan explicit about TLS production blockers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the boot plan explicit about TLS production blockers")
val plan = rt_file_read_text("doc/03_plan/os/riscv/riscv_rtl_simpleos_boot.md")

expect(plan).to_contain("TLS Baremetal")
expect(plan).to_contain("Blocked, not complete")
expect(plan).to_contain("ClientHello record")
expect(plan).to_contain("offline-generated")
expect(plan).to_contain("deterministic placeholder")
expect(plan).to_contain("placeholder_entropy")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_tls_baremetal_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS baremetal TLS gate.
- SimpleOS baremetal TLS gate

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f0e0ecf57c2f091cfc7878f1c490a981345065e0e7bcbd207b0bff91b28acde0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0e0ecf57c2f091cfc7878f1c490a981345065e0e7bcbd207b0bff91b28acde0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0e0ecf57c2f091cfc7878f1c490a981345065e0e7bcbd207b0bff91b28acde0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/simpleos_tls_baremetal_gate_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_tls_baremetal_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos_tls_baremetal_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_tls_baremetal_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_tls_baremetal_gate_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports embedded certificate material once real DER is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_tls_baremetal_gate_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes baremetal TLS info for embedded DER material' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_tls_baremetal_gate_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps TLS production readiness blocked while platform shims are placeholders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
