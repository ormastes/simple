# Famous-Site Corpus Div Geometry Simple Binary Contract

> The wrapper compares stored Chrome metrics against Pure Simple Draw IR in bounded chunks. This contract prevents `src/compiler_rust/**` from being accepted as the Simple renderer for web-renderer hardening evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Famous-Site Corpus Div Geometry Simple Binary Contract

The wrapper compares stored Chrome metrics against Pure Simple Draw IR in bounded chunks. This contract prevents `src/compiler_rust/**` from being accepted as the Simple renderer for web-renderer hardening evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/famous_site_corpus_div_geometry_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The wrapper compares stored Chrome metrics against Pure Simple Draw IR in
bounded chunks. This contract prevents `src/compiler_rust/**` from being
accepted as the Simple renderer for web-renderer hardening evidence.

## Requirements

**Requirements:** N/A

- REQ-FAMOUS-SITE-DIV-GEOMETRY-BIN-001: Default Simple binary selection is
  self-hosted only.
- REQ-FAMOUS-SITE-DIV-GEOMETRY-BIN-002: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence before any chunk run.
- REQ-FAMOUS-SITE-DIV-GEOMETRY-BIN-003: Evidence records selected Simple
  binary, source, and status fields.

## Plan

**Plan:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Confirm `summary.env` reports `simple-bin-forbidden`.
5. Confirm no chunk log was created for the forbidden path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before counting corpus rows or launching any
chunk process, making forbidden seed rejection cheap and deterministic.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/famous_site_corpus_div_geometry_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### Famous-site corpus div geometry Simple binary contract

#### selects self hosted Simple and records launcher provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects self hosted Simple and records launcher provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects self hosted Simple and records launcher provenance")
val script = file_read("scripts/check/check-famous-site-corpus-div-geometry-chunks.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("simple_bin=$SIMPLE_BIN")
expect(script).to_contain("simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### rejects explicit Rust seed before corpus chunk execution

- rejects explicit Rust seed before corpus chunk execution
   - Expected: code equals `0`
   - Expected: chunk_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before corpus chunk execution")
val root = "build/test-famous-site-corpus-div-geometry-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-famous-site-corpus-div-geometry-chunks.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/summary.env")
expect(evidence).to_contain("status=unavailable")
expect(evidence).to_contain("reason=simple-bin-forbidden")
expect(evidence).to_contain("simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("simple_bin_status=forbidden")

val (_chunk_out, _chunk_err, chunk_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/chunk_0_6.log"])
expect(chunk_code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-FAMOUS-SITE-DIV-GEOMETRY-BIN-001:`
- `REQ-FAMOUS-SITE-DIV-GEOMETRY-BIN-002:`
- `REQ-FAMOUS-SITE-DIV-GEOMETRY-BIN-003:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82799a95a849f470c2bef8da2c1841844a84a23a0a61b9df84766b8d117b78d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82799a95a849f470c2bef8da2c1841844a84a23a0a61b9df84766b8d117b78d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82799a95a849f470c2bef8da2c1841844a84a23a0a61b9df84766b8d117b78d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/check/famous_site_corpus_div_geometry_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/famous_site_corpus_div_geometry_simple_bin_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/famous_site_corpus_div_geometry_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/famous_site_corpus_div_geometry_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/famous_site_corpus_div_geometry_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/famous_site_corpus_div_geometry_simple_bin_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects self hosted Simple and records launcher provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/famous_site_corpus_div_geometry_simple_bin_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects explicit Rust seed before corpus chunk execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
