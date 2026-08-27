# ui_build_cli_spec

> ui_build CLI Integration Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ui_build_cli_spec

ui_build CLI Integration Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | html_ui_toolchain AC-3, AC-4, AC-6, AC-8 |
| Category | Tooling |
| Status | In Progress |
| Design | doc/05_design/ui/html_ui/html_ui_toolchain.md |
| Source | `test/02_integration/app/ui_build/ui_build_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

ui_build CLI Integration Specification

Overview
--------
Integration tests for `bin/simple run src/app/ui_build/main.spl` CLI.
Each `it` block uses isolated /tmp directories to avoid cross-contamination.
Commands run via `shell_output` from the repo root.

SMF stubs: compiled SMFs are currently 219-byte stubs (known gap,
doc/08_tracking/bug/emit_smf_stub_drops_module_content_2026-06-12.md). A
parallel change adds a `WARN stub smf:` line and `OK payload ... decoded`
verify line. These specs tolerate but do not require those additions. Stable
assertions: file existence, SMF first-4-bytes == `SMF\\0` (hex 534d4600),
sidecar contains form/elements, verify output contains "PASS" or "FAIL".

Examples
--------
  bin/simple run src/app/ui_build/main.spl -- build page.html -o /tmp/out --form=std
  bin/simple run src/app/ui_build/main.spl -- build page.html -o /tmp/out --form=dyn
  bin/simple run src/app/ui_build/main.spl -- verify /tmp/out/page.uib.sdn

## Scenarios

### ui_build CLI

#### std build produces an SMF with SMF\\0 magic and a sidecar with form and elements

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- std build produces an SMF with SMF\\0 magic and a sidecar with form and elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("std build produces an SMF with SMF\\0 magic and a sidecar with form and elements")
shell_output("rm -rf /tmp/ui_build_spec_std && mkdir -p /tmp/ui_build_spec_std/out")
make_page("/tmp/ui_build_spec_std")
ui_build("build /tmp/ui_build_spec_std/page.html -o /tmp/ui_build_spec_std/out --form=std")
assert_true(file_exists("/tmp/ui_build_spec_std/out/page.smf"))
assert_true(file_exists("/tmp/ui_build_spec_std/out/page.uib.sdn"))
val magic = smf_magic_hex("/tmp/ui_build_spec_std/out/page.smf")
assert_true(magic.contains("534d4600"))
val sidecar = file_read("/tmp/ui_build_spec_std/out/page.uib.sdn")
assert_true(sidecar.contains("form:"))
assert_true(sidecar.contains("elements:"))
shell_output("rm -rf /tmp/ui_build_spec_std")
```

</details>

#### dyn build produces an SMF artifact and a sidecar listing artifacts

- dyn build produces an SMF artifact and a sidecar listing artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("dyn build produces an SMF artifact and a sidecar listing artifacts")
shell_output("rm -rf /tmp/ui_build_spec_dyn && mkdir -p /tmp/ui_build_spec_dyn/out")
make_page("/tmp/ui_build_spec_dyn")
ui_build("build /tmp/ui_build_spec_dyn/page.html -o /tmp/ui_build_spec_dyn/out --form=dyn")
assert_true(file_exists("/tmp/ui_build_spec_dyn/out/page.smf"))
assert_true(file_exists("/tmp/ui_build_spec_dyn/out/page.uib.sdn"))
val sidecar = file_read("/tmp/ui_build_spec_dyn/out/page.uib.sdn")
assert_true(sidecar.contains("artifacts:"))
shell_output("rm -rf /tmp/ui_build_spec_dyn")
```

</details>

#### verify prints PASS on a freshly built std artifact

- verify prints PASS on a freshly built std artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("verify prints PASS on a freshly built std artifact")
shell_output("rm -rf /tmp/ui_build_spec_vpass && mkdir -p /tmp/ui_build_spec_vpass/out")
make_page("/tmp/ui_build_spec_vpass")
ui_build("build /tmp/ui_build_spec_vpass/page.html -o /tmp/ui_build_spec_vpass/out --form=std")
val out = ui_build_capture("verify /tmp/ui_build_spec_vpass/out/page.uib.sdn")
assert_true(out.contains("PASS"))
shell_output("rm -rf /tmp/ui_build_spec_vpass")
```

</details>

#### verify prints FAIL after the smf artifact is truncated in a scratch copy

- verify prints FAIL after the smf artifact is truncated in a scratch copy


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("verify prints FAIL after the smf artifact is truncated in a scratch copy")
shell_output("rm -rf /tmp/ui_build_spec_vfail && mkdir -p /tmp/ui_build_spec_vfail/out")
make_page("/tmp/ui_build_spec_vfail")
ui_build("build /tmp/ui_build_spec_vfail/page.html -o /tmp/ui_build_spec_vfail/out --form=std")
# Copy to scratch so we don't poison sibling its; patch sidecar paths via sed
shell_output("cp -r /tmp/ui_build_spec_vfail/out /tmp/ui_build_spec_vfail/scratch")
shell_output("sed -i 's|/tmp/ui_build_spec_vfail/out|/tmp/ui_build_spec_vfail/scratch|g' /tmp/ui_build_spec_vfail/scratch/page.uib.sdn")
# Truncate the SMF to 10 bytes — too small for the 179-byte minimum
shell_output("dd if=/dev/zero of=/tmp/ui_build_spec_vfail/scratch/page.smf bs=1 count=10 2>/dev/null")
val out = ui_build_capture("verify /tmp/ui_build_spec_vfail/scratch/page.uib.sdn")
assert_true(out.contains("FAIL"))
shell_output("rm -rf /tmp/ui_build_spec_vfail")
```

</details>

#### theme showcase std build produces sidecar with at least 40 element entries

- theme showcase std build produces sidecar with at least 40 element entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("theme showcase std build produces sidecar with at least 40 element entries")
shell_output("rm -rf /tmp/ui_build_spec_theme && mkdir -p /tmp/ui_build_spec_theme/out")
val theme = "src/lib/common/ui/theme_html/theme_showcase.html"
ui_build("build " + theme + " -o /tmp/ui_build_spec_theme/out --form=std")
assert_true(file_exists("/tmp/ui_build_spec_theme/out/theme_showcase.smf"))
assert_true(file_exists("/tmp/ui_build_spec_theme/out/theme_showcase.uib.sdn"))
val cnt = shell_output(
    "grep -c '^  - ' /tmp/ui_build_spec_theme/out/theme_showcase.uib.sdn 2>/dev/null || echo 0"
).trim()
val n = cnt.to_i64() ?? 0
assert_true(n >= 40)
shell_output("rm -rf /tmp/ui_build_spec_theme")
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


## Related Documentation

- **Design:** `doc/05_design/ui/html_ui/html_ui_toolchain.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e2b87bd5fd7743d6fa0f594a935e53f4a3fceea907c3e2ac0a997998aab74fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e2b87bd5fd7743d6fa0f594a935e53f4a3fceea907c3e2ac0a997998aab74fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e2b87bd5fd7743d6fa0f594a935e53f4a3fceea907c3e2ac0a997998aab74fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/ui_build/ui_build_cli_spec.spl
mirror: doc/06_spec/02_integration/app/ui_build/ui_build_cli_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/ui_build/ui_build_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/ui_build/ui_build_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/ui_build/ui_build_cli_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'std build produces an SMF with SMF\\0 magic and a sidecar with form and elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/ui_build/ui_build_cli_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dyn build produces an SMF artifact and a sidecar listing artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/ui_build/ui_build_cli_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verify prints PASS on a freshly built std artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
