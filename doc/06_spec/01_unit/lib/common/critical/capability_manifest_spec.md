# capability_manifest_spec

> The lint severity and the runtime gate both read these keys, so the parser

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# capability_manifest_spec

The lint severity and the runtime gate both read these keys, so the parser

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/critical/capability_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## One source of truth for the mode

    The lint severity and the runtime gate both read these keys, so the parser
    must agree with `config/critical_mode.sdn` exactly.

## Scenarios

### critical.* config parsing

#### defaults to allow/auto/disabled when there is no critical section

- defaults to allow/auto/disabled when there is no critical section
   - Expected: cfg.dynamic_acquire equals `allow`
   - Expected: cfg.gpu_backend equals `auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to allow/auto/disabled when there is no critical section")
val cfg = parse_critical_mode_config("gpu:\n  backend: vulkan\n")
expect(cfg.enabled).to_be_false()
expect(cfg.dynamic_acquire).to_equal("allow")
expect(cfg.gpu_backend).to_equal("auto")
expect(cfg.loaded).to_be_false()
```

</details>

#### reads enabled, dynamic_acquire and the nested gpu backend

- reads enabled, dynamic_acquire and the nested gpu backend
   - Expected: cfg.dynamic_acquire equals `warn`
   - Expected: cfg.gpu_backend equals `cuda(sm80)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads enabled, dynamic_acquire and the nested gpu backend")
val content = "critical:\n  enabled: true\n  dynamic_acquire: warn\n  gpu:\n    backend: cuda(sm80)\n"
val cfg = parse_critical_mode_config(content)
expect(cfg.enabled).to_be_true()
expect(cfg.dynamic_acquire).to_equal("warn")
expect(cfg.gpu_backend).to_equal("cuda(sm80)")
expect(cfg.loaded).to_be_true()
```

</details>

#### reads dynamic_acquire: error (the promoted target state)

- reads dynamic_acquire: error (the promoted target state)
   - Expected: cfg.dynamic_acquire equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads dynamic_acquire: error (the promoted target state)")
val content = "critical:\n  enabled: true\n  dynamic_acquire: error\n"
val cfg = parse_critical_mode_config(content)
expect(cfg.dynamic_acquire).to_equal("error")
```

</details>

#### ignores comments

- ignores comments
   - Expected: cfg.dynamic_acquire equals `warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores comments")
val content = "critical:\n  # dynamic_acquire: error\n  dynamic_acquire: warn\n"
val cfg = parse_critical_mode_config(content)
expect(cfg.dynamic_acquire).to_equal("warn")
```

</details>

#### stops at the next top-level section so other streams' keys do not leak in

- stops at the next top-level section so other streams' keys do not leak in
   - Expected: cfg.gpu_backend equals `auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops at the next top-level section so other streams' keys do not leak in")
val content = "critical:\n  enabled: true\n  dynamic_acquire: warn\ngpu:\n  backend: vulkan\n"
val cfg = parse_critical_mode_config(content)
expect(cfg.enabled).to_be_true()
expect(cfg.gpu_backend).to_equal("auto")
```

</details>

#### the shipped default config is non-critical, warn, auto

- the shipped default config is non-critical, warn, auto
   - Expected: cfg.dynamic_acquire equals `allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the shipped default config is non-critical, warn, auto")
val cfg = default_critical_mode_config()
expect(cfg.enabled).to_be_false()
expect(cfg.dynamic_acquire).to_equal("allow")
```

</details>

### boot-time probe-vs-manifest gate

#### outside critical mode

#### passes even when the probe disagrees with the manifest

- passes even when the probe disagrees with the manifest


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes even when the probe disagrees with the manifest")
val r = verify_gpu_manifest_pin("cuda(sm80)", "vulkan", false)
expect(r.ok).to_be_true()
```

</details>

#### passes with an auto manifest

- passes with an auto manifest


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes with an auto manifest")
val r = verify_gpu_manifest_pin("auto", "vulkan", false)
expect(r.ok).to_be_true()
```

</details>

#### in critical mode with a matching probe

#### passes and produces no report

- passes and produces no report
   - Expected: r.report equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes and produces no report")
val r = verify_gpu_manifest_pin("cuda(sm80)", "cuda(sm80)", true)
expect(r.ok).to_be_true()
expect(r.report).to_equal("")
```

</details>

#### in critical mode with a mismatching probe

#### refuses with DCA003 and names both sides

- refuses with DCA003 and names both sides
   - Expected: r.code equals `DCA003`
   - Expected: r.manifest_backend equals `cuda(sm80)`
   - Expected: r.probed_backend equals `vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses with DCA003 and names both sides")
val r = verify_gpu_manifest_pin("cuda(sm80)", "vulkan", true)
expect(r.ok).to_be_false()
expect(r.code).to_equal("DCA003")
expect(r.report.contains("REFUSING TO START")).to_be_true()
expect(r.report.contains("cuda(sm80)")).to_be_true()
expect(r.report.contains("vulkan")).to_be_true()
expect(r.manifest_backend).to_equal("cuda(sm80)")
expect(r.probed_backend).to_equal("vulkan")
```

</details>

#### refuses when the probe finds nothing at all

- refuses when the probe finds nothing at all
   - Expected: r.code equals `DCA003`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses when the probe finds nothing at all")
val r = verify_gpu_manifest_pin("cuda(sm80)", "", true)
expect(r.ok).to_be_false()
expect(r.code).to_equal("DCA003")
expect(r.report.contains("no backend detected")).to_be_true()
```

</details>

#### does not offer the probed backend as a fallback

- does not offer the probed backend as a fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not offer the probed backend as a fallback")
val r = verify_gpu_manifest_pin("cuda(sm80)", "vulkan", true)
expect(r.report.contains("falling back")).to_be_false()
expect(r.report.contains("does not fall back")).to_be_true()
```

</details>

#### in critical mode with an unpinned manifest

#### refuses with DCA002 before any probe comparison

- refuses with DCA002 before any probe comparison
   - Expected: r.code equals `DCA002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses with DCA002 before any probe comparison")
val r = verify_gpu_manifest_pin("auto", "vulkan", true)
expect(r.ok).to_be_false()
expect(r.code).to_equal("DCA002")
expect(r.report.contains("REFUSING TO START")).to_be_true()
```

</details>

#### refuses on an unset manifest backend

- refuses on an unset manifest backend
   - Expected: r.code equals `DCA002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses on an unset manifest backend")
val r = verify_gpu_manifest_pin("", "vulkan", true)
expect(r.ok).to_be_false()
expect(r.code).to_equal("DCA002")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `9cb2ca03a84d9f547fe5fbf5c22ce07746076422c427a853427b6d4f5411bc8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9cb2ca03a84d9f547fe5fbf5c22ce07746076422c427a853427b6d4f5411bc8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9cb2ca03a84d9f547fe5fbf5c22ce07746076422c427a853427b6d4f5411bc8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/critical/capability_manifest_spec.spl
mirror: doc/06_spec/01_unit/lib/common/critical/capability_manifest_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/critical/capability_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/critical/capability_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/critical/capability_manifest_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to allow/auto/disabled when there is no critical section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/critical/capability_manifest_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads enabled, dynamic_acquire and the nested gpu backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/critical/capability_manifest_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads dynamic_acquire: error (the promoted target state)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
