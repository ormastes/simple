# Claude Full proxy utils

> Pure Simple coverage for proxy env selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full proxy utils

Pure Simple coverage for proxy env selection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/proxy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for proxy env selection.

## Scenarios

### Claude full proxy utils

#### prefers HTTPS lowercase then uppercase before HTTP variants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prefers HTTPS lowercase then uppercase before HTTP variants
- Check proxy URL priority
   - Expected: getProxyUrl(env) equals `Some("https-lower")`
   - Expected: getProxyUrl(fallback) equals `Some("https-upper")`
   - Expected: getProxyUrl(httpFallback) equals `Some("http-lower")`
   - Expected: getProxyUrl(upperHttp) equals `Some("http-upper")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prefers HTTPS lowercase then uppercase before HTTP variants")
step("Check proxy URL priority")
val env = ProxyEnv.new("https-lower", "https-upper", "http-lower", "http-upper", "", "")
expect(getProxyUrl(env)).to_equal(Some("https-lower"))

val fallback = ProxyEnv.new("", "https-upper", "http-lower", "http-upper", "", "")
expect(getProxyUrl(fallback)).to_equal(Some("https-upper"))

val httpFallback = ProxyEnv.new("", "", "http-lower", "http-upper", "", "")
expect(getProxyUrl(httpFallback)).to_equal(Some("http-lower"))

val upperHttp = ProxyEnv.new("", "", "", "http-upper", "", "")
expect(getProxyUrl(upperHttp)).to_equal(Some("http-upper"))
```

</details>

#### treats empty proxy env values as unset

- treats empty proxy env values as unset
- Check empty values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats empty proxy env values as unset")
step("Check empty values")
val env = ProxyEnv.new("", "", "", "", "", "")
expect(getProxyUrl(env)).to_be_nil()
expect(getNoProxy(env)).to_be_nil()
```

</details>

#### prefers lowercase no_proxy over uppercase NO_PROXY

- prefers lowercase no_proxy over uppercase NO_PROXY
- Check no_proxy priority
   - Expected: getNoProxy(env) equals `Some("lower")`
   - Expected: getNoProxy(fallback) equals `Some("upper")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prefers lowercase no_proxy over uppercase NO_PROXY")
step("Check no_proxy priority")
val env = ProxyEnv.new("", "", "", "", "lower", "upper")
expect(getNoProxy(env)).to_equal(Some("lower"))

val fallback = ProxyEnv.new("", "", "", "", "", "upper")
expect(getNoProxy(fallback)).to_equal(Some("upper"))
```

</details>

#### matches no_proxy wildcards and domain entries

- matches no_proxy wildcards and domain entries
- Check no_proxy matching
   - Expected: shouldBypassProxy("https://api.example.com/v1", Some("localhost,.example.com")) is true
   - Expected: shouldBypassProxy("https://api.example.com/v1", Some("localhost .example.com")) is true
   - Expected: shouldBypassProxy("https://api.example.com?x=1", Some("api.example.com")) is true
   - Expected: shouldBypassProxy("https://api.example.com:8443#section", Some("api.example.com:8443")) is true
   - Expected: shouldBypassProxy("https://example.com", Some(".example.com")) is true
   - Expected: shouldBypassProxy("https://other.test", Some("*")) is true
   - Expected: shouldBypassProxy("not-a-url", Some("*")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches no_proxy wildcards and domain entries")
step("Check no_proxy matching")
expect(shouldBypassProxy("https://api.example.com/v1", Some("localhost,.example.com"))).to_equal(true)
expect(shouldBypassProxy("https://api.example.com/v1", Some("localhost .example.com"))).to_equal(true)
expect(shouldBypassProxy("https://api.example.com?x=1", Some("api.example.com"))).to_equal(true)
expect(shouldBypassProxy("https://api.example.com:8443#section", Some("api.example.com:8443"))).to_equal(true)
expect(shouldBypassProxy("https://example.com", Some(".example.com"))).to_equal(true)
expect(shouldBypassProxy("https://other.test", Some("*"))).to_equal(true)
expect(shouldBypassProxy("not-a-url", Some("*"))).to_equal(true)
```

</details>

#### matches no_proxy ports and bracketed ipv6 hosts

- matches no_proxy ports and bracketed ipv6 hosts
- Check no_proxy host and port matching
   - Expected: shouldBypassProxy("https://api.example.com:8443/v1", Some("api.example.com:8443")) is true
   - Expected: shouldBypassProxy("https://api.example.com:8443/v1", Some("api.example.com:8080")) is false
   - Expected: shouldBypassProxy("https://[::1]:8443/v1", Some("[::1]:8443")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches no_proxy ports and bracketed ipv6 hosts")
step("Check no_proxy host and port matching")
expect(shouldBypassProxy("https://api.example.com:8443/v1", Some("api.example.com:8443"))).to_equal(true)
expect(shouldBypassProxy("https://api.example.com:8443/v1", Some("api.example.com:8080"))).to_equal(false)
expect(shouldBypassProxy("https://[::1]:8443/v1", Some("[::1]:8443"))).to_equal(true)
```

</details>

#### does not bypass when no_proxy is unset or unmatched

- does not bypass when no_proxy is unset or unmatched
- Check no_proxy misses
   - Expected: shouldBypassProxy("https://api.example.com", nil) is false
   - Expected: shouldBypassProxy("https://api.example.com", Some("")) is false
   - Expected: shouldBypassProxy("not-a-url", Some("example.com")) is false
   - Expected: shouldBypassProxy("https://api.example.com", Some("internal.test")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not bypass when no_proxy is unset or unmatched")
step("Check no_proxy misses")
expect(shouldBypassProxy("https://api.example.com", nil)).to_equal(false)
expect(shouldBypassProxy("https://api.example.com", Some(""))).to_equal(false)
expect(shouldBypassProxy("not-a-url", Some("example.com"))).to_equal(false)
expect(shouldBypassProxy("https://api.example.com", Some("internal.test"))).to_equal(false)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd0c1ba6cdcfd87c29b5f20ccd5dad39be6d743548a16d0d9bce05d70dcd28d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd0c1ba6cdcfd87c29b5f20ccd5dad39be6d743548a16d0d9bce05d70dcd28d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd0c1ba6cdcfd87c29b5f20ccd5dad39be6d743548a16d0d9bce05d70dcd28d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/proxy_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/proxy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/proxy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/proxy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/proxy_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers HTTPS lowercase then uppercase before HTTP variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/proxy_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats empty proxy env values as unset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/proxy_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers lowercase no_proxy over uppercase NO_PROXY' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
