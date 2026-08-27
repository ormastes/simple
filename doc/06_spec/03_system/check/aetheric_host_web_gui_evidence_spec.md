# Aetheric host Web/GUI evidence contract

> The wrapper is intentionally fail-closed: a missing exact-current binary or a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aetheric host Web/GUI evidence contract

The wrapper is intentionally fail-closed: a missing exact-current binary or a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/aetheric_host_web_gui_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The wrapper is intentionally fail-closed: a missing exact-current binary or a
partial/fixture proof cannot become a rendering PASS.

## Scenarios

### Aetheric host Web/GUI evidence

#### requires canonical production proof fields and UI access history

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires canonical production proof fields and UI access history
- Inspect the fail-closed Aetheric proof contract
- Reject a missing binary before any proof can be accepted
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires canonical production proof fields and UI access history")
step("Inspect the fail-closed Aetheric proof contract")
val source = file_read(WRAPPER)
expect(source).to_contain("production-html-webir-drawir-electron")
expect(source).to_contain("aetheric-host-web-gui-v1")
expect(source).to_contain("ui_access_snapshot_status")
expect(source).to_contain("ui_access_history_status")
expect(source).to_contain("blur_or_tolerance_used")
expect(source).to_contain("synthetic_fixture")
expect(source).to_contain("missing-production-proof")
expect(source).to_contain("source-revision-mismatch")
expect(source).to_contain("binary-sha256-mismatch")
expect(source).to_contain("capture-sha256-mismatch")
expect(source).to_contain("html-sha256-mismatch")
expect(source).to_contain("observation-sha256-mismatch")
expect(source).to_contain("generator-binary-sha256-mismatch")
expect(source).to_contain("renderer-binary-sha256-mismatch")
expect(source).to_contain("ui-access-revision-not-pass")
expect(source).to_contain("ui-access-sha256-mismatch")
expect(source).to_contain("[ \"$(field css_animation_probe)\" = true ]")
expect(source).to_contain("css-animation-not-applied")
expect(source).to_contain("pixel-artifact-sha256-mismatch")
expect(source).to_contain("screenshot-sha256-mismatch")
expect(source).to_contain("artifact-outside-build-or-linked")
expect(source).to_contain("artifact_under_build_dir")
expect(source).to_contain("EXPECTED_ELECTRON_VERSION=\"42.5.0\"")
expect(source).to_contain("electron-version-mismatch")
expect(source).to_contain("aetheric_electron_identity.js")
expect(source).to_contain("verify-proof --root \"$ROOT_DIR\" --proof \"$PROOF_PATH\"")
expect(source).to_contain("stage4_verify_candidate_provenance")

step("Reject a missing binary before any proof can be accepted")
val root = "build/test-aetheric-host-web-gui-missing-bin"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=" + root + "/missing BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh " + WRAPPER + " > " + root + "/stdout.txt 2>&1 || true"
val (_out, _err, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)
val output = file_read(root + "/stdout.txt")
expect(output).to_contain("aetheric_host_web_gui_status=fail")
expect(output).to_contain("aetheric_host_web_gui_reason=missing-simple-bin")
```

</details>

#### rejects a producer pass marker without the required live artifacts

- rejects a producer pass marker without the required live artifacts
- Reject a partial proof rather than promoting a synthetic PASS
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a producer pass marker without the required live artifacts")
step("Reject a partial proof rather than promoting a synthetic PASS")
val root = "build/test-aetheric-host-web-gui-partial-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + "/fixture && printf '#!/bin/sh\\nexit 0\\n' > " + root + "/fixture/simple && chmod +x " + root + "/fixture/simple && printf 'schema=aetheric-host-web-gui-v1\\nstatus=pass\\nproducer=production-html-webir-drawir-electron\\n' > " + root + "/proof.env && SIMPLE_BIN=$PWD/" + root + "/fixture/simple AETHERIC_HOST_WEB_GUI_PROOF=$PWD/" + root + "/proof.env BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh " + WRAPPER + " > " + root + "/stdout.txt 2>&1 || true"
val (_out, _err, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)
val output = file_read(root + "/stdout.txt")
expect(output).to_contain("aetheric_host_web_gui_status=fail")
expect(output).to_contain("aetheric_host_web_gui_reason=unprovenanced-simple-bin")
```

</details>

#### keeps source, binary, and artifact provenance fail-closed

- keeps source, binary, and artifact provenance fail-closed
- Keep concrete negative provenance outcomes in the executable contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps source, binary, and artifact provenance fail-closed")
step("Keep concrete negative provenance outcomes in the executable contract")
val source = file_read(WRAPPER)
# These are ordered after complete-field validation so a future change
# cannot silently turn a stale revision, altered binary, or swapped
# artifact into a PASS by checking only the shape of its SHA string.
expect(source).to_contain("[ \"$(field source_revision)\" = \"$CURRENT_REVISION\" ]")
expect(source).to_contain("[ \"$(field binary_sha256)\" = \"$(sha256_file \"$SIMPLE_BIN\")\" ]")
expect(source).to_contain("artifact_under_build_dir \"$(field \"$path_key\")\"")
expect(source).to_contain("[ \"$(field capture_sha256)\" = \"$(sha256_file \"$(field capture_path)\")\" ]")
expect(source).to_contain("[ \"$(field html_sha256)\" = \"$(sha256_file \"$(field html_path)\")\" ]")
expect(source).to_contain("[ \"$(field observation_sha256)\" = \"$(sha256_file \"$(field observation_path)\")\" ]")
```

</details>

#### isolates native caches and binds every renderer and UI provider

- isolates native caches and binds every renderer and UI provider
- Inspect the producer's per-entry native cache and provider scopes
- Require the proof writer to hash the exact admitted providers
- Bind the launched Electron and Chromium versions into the observation
- Behaviorally verify exact local Electron paths, hashes, and metadata
   - Expected: identity_code equals `0`
   - Expected: identity_err equals ``
- Keep provider paths, hashes, manifest bindings, and cache scopes fail closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("isolates native caches and binds every renderer and UI provider")
step("Inspect the producer's per-entry native cache and provider scopes")
val producer = file_read(PRODUCER)
expect(producer).to_contain("\"$NATIVE_CACHE/generator\"")
expect(producer).to_contain("\"$NATIVE_CACHE/renderer\"")
expect(producer).to_contain("\"$NATIVE_CACHE/ui-access\"")
expect(producer).to_contain("\"$RENDERER_WM_PROVIDER:$RENDERER_C_WM_PROVIDER\"")
expect(producer).to_contain("\"$SQLITE_OBJECT:$SQLITE_SYSTEM_PROVIDER\"")
expect(producer).to_contain("src/runtime/runtime_sqlite.c")
expect(producer).to_contain("libsqlite3.tbd")
expect(producer).to_contain("require_global_symbol \"$SQLITE_OBJECT\" rt_sqlite_open")
expect(producer).to_contain("schema=aetheric-host-web-gui-provider-provenance-v1")
expect(producer).to_contain("--electron-launcher \"$ELECTRON_RESOLVED_BIN\"")
expect(producer).to_contain("--electron-app-executable \"$ELECTRON_APP_EXECUTABLE\"")
expect(producer).to_contain("--electron-package \"$ELECTRON_PACKAGE\"")
expect(producer).to_contain("--electron-lock \"$ELECTRON_LOCK\"")

step("Require the proof writer to hash the exact admitted providers")
val writer = file_read(PROOF_WRITER)
expect(writer).to_contain("required(\"--provider-provenance\")")
expect(writer).to_contain("required(\"--renderer-wm-provider\")")
expect(writer).to_contain("required(\"--renderer-c-wm-provider\")")
expect(writer).to_contain("required(\"--ui-sqlite-provider\")")
expect(writer).to_contain("required(\"--ui-sqlite-system-provider\")")
expect(writer).to_contain("provider_provenance_sha256: sha256(providerProvenancePath)")
expect(writer).to_contain("required(\"--electron-launcher\")")
expect(writer).to_contain("required(\"--electron-app-executable\")")
expect(writer).to_contain("required(\"--electron-package\")")
expect(writer).to_contain("required(\"--electron-lock\")")
expect(writer).to_contain("electron_process_version: value(observation, \"electron_process_version\")")
expect(writer).to_contain("resolveElectronIdentity")

step("Bind the launched Electron and Chromium versions into the observation")
val capture = file_read(CAPTURE)
expect(capture).to_contain("aethericObservation.electron_process_version = process.versions.electron")
expect(capture).to_contain("aethericObservation.chrome_process_version = process.versions.chrome")

step("Behaviorally verify exact local Electron paths, hashes, and metadata")
val (identity_out, identity_err, identity_code) = process_run("node", [IDENTITY_TEST])
expect(identity_code).to_equal(0)
expect(identity_out).to_contain("aetheric-electron-identity-tests: PASS")
expect(identity_err).to_equal("")

step("Keep provider paths, hashes, manifest bindings, and cache scopes fail closed")
val wrapper = file_read(WRAPPER)
expect(wrapper).to_contain("provider-path-not-canonical")
expect(wrapper).to_contain("provider-sha256-mismatch")
expect(wrapper).to_contain("provider-provenance-sha256-mismatch")
expect(wrapper).to_contain("provider-provenance-binding-mismatch")
expect(wrapper).to_contain("provider-provenance-sqlite-source-mismatch")
expect(wrapper).to_contain("provider-provenance-sqlite-sdk-mismatch")
expect(wrapper).to_contain("provider-provenance-cache-scope-mismatch")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-008`
- `REQ-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `715df54afeeb85c1f9da29d14631e9b4b1e8f386edd9fb6cec8242440dc05667`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `715df54afeeb85c1f9da29d14631e9b4b1e8f386edd9fb6cec8242440dc05667`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `715df54afeeb85c1f9da29d14631e9b4b1e8f386edd9fb6cec8242440dc05667`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/aetheric_host_web_gui_evidence_spec.spl
mirror: doc/06_spec/03_system/check/aetheric_host_web_gui_evidence_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/check/aetheric_host_web_gui_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/aetheric_host_web_gui_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/aetheric_host_web_gui_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/aetheric_host_web_gui_evidence_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/check/aetheric_host_web_gui_evidence_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires canonical production proof fields and UI access history' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/aetheric_host_web_gui_evidence_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a producer pass marker without the required live artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/aetheric_host_web_gui_evidence_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'isolates native caches and binds every renderer and UI provider' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
