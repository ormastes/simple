# Production Host WM Fullscreen Evidence Contract

> Pins the fail-closed launcher contract for REQ-1, REQ-5, REQ-6, REQ-7, and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production Host WM Fullscreen Evidence Contract

Pins the fail-closed launcher contract for REQ-1, REQ-5, REQ-6, REQ-7, and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/wm_production_fullscreen_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pins the fail-closed launcher contract for REQ-1, REQ-5, REQ-6, REQ-7, and
REQ-8. Negative cases prove that forbidden compilers and missing cached
production artifacts cannot launch a GUI or fabricate evidence.

## Scenarios

### Production host WM fullscreen evidence contract

#### rejects a Rust seed resolved path before production launch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a Rust seed resolved path before production launch
- Run the production evidence gate with an explicit Rust seed path
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a Rust seed resolved path before production launch")
step("Run the production evidence gate with an explicit Rust seed path")
val root = "build/test-wm-production-fullscreen-rust-seed"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/debug/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-wm-production-fullscreen-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)
val output = file_read(root + "/stdout.txt")
expect(output).to_contain("wm_production_fullscreen_reason=simple-bin-forbidden")
expect(output).to_contain("wm_production_fullscreen_simple_bin_status=forbidden")
expect(output).to_contain("wm_production_fullscreen_launch_log=missing")
```

</details>

#### rejects a missing explicitly selected cached production artifact

- rejects a missing explicitly selected cached production artifact
- Run the gate with a nonexistent compiled hosted entry
   - Expected: code equals `0`
   - Expected: files_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a missing explicitly selected cached production artifact")
step("Run the gate with a nonexistent compiled hosted entry")
val root = "build/test-wm-production-fullscreen-artifact"
val simple_bin = root + "/simple-contract-fixture"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '#!/bin/sh\n# SIMPLE_LINK_OBJECTS provider is missing or not a file:\nprintf \"Simple contract fixture\\\\n\"\n' > " + simple_bin + " && chmod +x " + simple_bin + " && SIMPLE_BIN=" + simple_bin + " HOSTED_WM_ARTIFACT=" + root + "/missing-hosted-entry BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-wm-production-fullscreen-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)
val output = file_read(root + "/stdout.txt")
expect(output).to_contain("wm_production_fullscreen_reason=cached-production-artifact-missing")
expect(output).to_contain("wm_production_fullscreen_entry=src/os/hosted/hosted_entry.spl")
expect(output).to_contain("wm_production_fullscreen_simple_bin_status=pass")
expect(output).to_contain("wm_production_fullscreen_snapshot_hook=ready")
expect(output).to_contain("wm_production_fullscreen_capture_hook=ready")
expect(output).to_contain("wm_production_fullscreen_input_hook=ready")
expect(output).to_contain("wm_production_fullscreen_windowed_capture=missing")
expect(output).to_contain("wm_production_fullscreen_fullscreen_capture=missing")
expect(output).to_contain("wm_production_fullscreen_restored_capture=missing")
expect(output).to_contain("wm_production_fullscreen_launch_log=missing")
val (_files_out, _files_err, files_code) = process_run("/bin/sh", ["-c", "test ! -e " + root + "/out/launch.log && test ! -e " + root + "/out/windowed.ppm && test ! -e " + root + "/out/fullscreen.ppm && test ! -e " + root + "/out/restored.ppm"])
expect(files_code).to_equal(0)
```

</details>

#### implements the complete live evidence contract and never targets examples

- implements the complete live evidence contract and never targets examples
- Inspect the production wrapper contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements the complete live evidence contract and never targets examples")
step("Inspect the production wrapper contract")
val script = file_read("scripts/check/check-wm-production-fullscreen-evidence.shs")
expect(script).to_contain("SIMPLE_WM_EVIDENCE_SNAPSHOT_PATH")
expect(script).to_contain("SIMPLE_WM_EVIDENCE_CAPTURE_PATH")
expect(script).to_contain("SIMPLE_WM_EVIDENCE_INPUT_FIFO")
expect(script).to_contain("internal-scene-changed-across-physical-mode")
expect(script).to_contain("restored-native-geometry-mismatch")
expect(script).to_contain("snapshot-provenance-invalid")
expect(script).to_contain("ppm-invalid-or-semantic-pixels-missing")
expect(script).to_contain("fullscreen-capture-not-distinct")
expect(script).to_contain("issue 8 'maximize'")
expect(script).to_contain("internal-maximize-geometry-mismatch")
expect(script).to_contain("internal-maximize-restore-mismatch")
expect(script).to_contain("wm_production_fullscreen_internal_maximize_hook=verified")
expect(script.contains("unsupported-v1")).to_be(false)
expect(script).to_contain("production-native-build-incomplete")
expect(script).to_contain("build_simple_runtime_sffi.shs")
expect(script).to_contain("host-runtime-provider-incomplete")
expect(script).to_contain("rt_engine2d_rocm_download_pixels")
expect(script).to_contain("SIMPLE_NO_STUB_FALLBACK=1")
expect(script).to_contain("simple-bin-external-provider-link-support-missing")
expect(script).to_contain("SIMPLE_LINK_OBJECTS provider is missing or not a file:")
expect(script).to_contain("SIMPLE_LINK_OBJECTS=\"$SPL_WINIT_LIB:$SIMPLE_RUNTIME_DYLIB:$SIMPLE_RUNTIME_C_DYLIB\"")
expect(script).to_contain("host-runtime-provider-not-linked")
expect(script).to_contain("provider_linked")
expect(script.contains("DYLD_INSERT_LIBRARIES")).to_be(false)
expect(script).to_contain("-newer \"$NATIVE_BIN\"")
expect(script).to_contain("Generating [1-9][0-9]* stub functions")
expect(script).to_contain("HOSTED_WM_ARTIFACT")
expect(script.contains("examples/")).to_be(false)
```

</details>

#### routes explicit runtime providers through the pure-Simple final link without stub fallback

- routes explicit runtime providers through the pure-Simple final link without stub fallback
- Inspect the pure-Simple provider ownership contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes explicit runtime providers through the pure-Simple final link without stub fallback")
step("Inspect the pure-Simple provider ownership contract")
val native_link = compiler_native_link_source()
val linker_wrapper = file_read("src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl")
expect(native_link).to_contain("llvm_configured_external_link_objects")
expect(native_link).to_contain("SIMPLE_LINK_OBJECTS provider is missing or empty")
expect(native_link).to_contain("all_objects = all_objects.push(provider)")
expect(native_link).to_contain("llvm_external_provider_rpath_flags(external_providers)")
expect(native_link).to_contain("not pass them to cleanup_runtime_objects")
expect(linker_wrapper).to_contain("cc_fallback_extra_flags")
expect(linker_wrapper).to_contain("-Wl,-rpath,")
```

</details>

#### ships runtime bridges with the hosted TLS implementation enabled

- ships runtime bridges with the hosted TLS implementation enabled
- Inspect the production bridge and TLS feature contracts


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ships runtime bridges with the hosted TLS implementation enabled")
step("Inspect the production bridge and TLS feature contracts")
val winit_builder = file_read("scripts/build/build_spl_winit.shs")
val runtime_builder = file_read("scripts/build/build_simple_runtime_sffi.shs")
val runtime_manifest = file_read("src/compiler_rust/runtime/Cargo.toml")
val runtime_net = file_read(
    "src/compiler_rust/runtime/src/value/net.rs"
)
expect(winit_builder).to_contain("src/runtime/spl_winit")
expect(winit_builder).to_contain("libspl_winit.$EXT")
expect(runtime_builder).to_contain("-p simple-runtime")
expect(runtime_builder).to_contain(
    "--features runtime-symbol-table,vulkan,runtime-tls)"
)
expect(runtime_manifest).to_contain(
    "runtime-tls = [\"dep:rustls\", \"dep:rustls-platform-verifier\", " +
    "\"dep:rustls-pemfile\"]"
)
expect(runtime_net).to_contain(
    "#[cfg(feature = \"runtime-tls\")]\ninclude!(\"net_tls.rs\");"
)
expect(runtime_net).to_contain("include!(\"net_http_job.rs\");")
expect(runtime_builder).to_contain("libsimple_runtime_c_wm.$EXT")
expect(winit_builder).to_contain("@rpath/")
expect(runtime_builder).to_contain("@rpath/")
```

</details>

#### fails Vulkan closed unless one same frame proves device readback

- fails Vulkan closed unless one same frame proves device readback
- Inspect the Vulkan-only frame-marker branch in the production wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails Vulkan closed unless one same frame proves device readback")
step("Inspect the Vulkan-only frame-marker branch in the production wrapper")
val script = file_read("scripts/check/check-wm-production-fullscreen-evidence.shs")
expect(script).to_contain("REQUESTED_GUI_BACKEND")
expect(script).to_contain("[ \"$REQUESTED_GUI_BACKEND\" = vulkan ]")
expect(script).to_contain("grep -E '(^|[ ;])backend=vulkan([; ]|$)'")
expect(script).to_contain("grep -E '(^|[ ;])source=device_readback([; ]|$)'")
expect(script).to_contain("grep -E '(^|[ ;])handle=[1-9][0-9]*([; ]|$)'")
expect(script).to_contain("grep -E '(^|[ ;])checksum=[1-9][0-9]*([; ]|$)'")
expect(script).to_contain("vulkan_frame_marker '^\\[hosted-wm\\] frame-presented '")
expect(script).to_contain("vulkan_frame_marker '^\\[hosted-wm\\] evidence-ack nonce=10 '")
expect(script).to_contain("vulkan_frame_marker '^\\[hosted-wm\\] evidence-ack nonce=11 '")
expect(script).to_contain("vulkan_frame_marker '^\\[hosted-wm\\] evidence-ack nonce=12 '")
expect(script).to_contain("vulkan-fullscreen-device-readback-marker-missing")
expect(script).to_contain("ppm_engine2d_checksum")
expect(script).to_contain("vulkan-windowed-same-frame-checksum-mismatch")
expect(script).to_contain("vulkan-fullscreen-same-frame-checksum-mismatch")
expect(script).to_contain("vulkan-restored-same-frame-checksum-mismatch")
expect(script).to_contain("wm_production_fullscreen_backend_handle=$verified_backend_handle")
expect(script).to_contain("wm_production_fullscreen_same_frame_readback=$verified_same_frame_readback")
expect(script).to_contain("wm_production_fullscreen_readback_checksum=$verified_readback_checksum")
expect(script).to_contain("wm_production_fullscreen_presented_checksum=$verified_presented_checksum")
```

</details>

#### keeps the established presented-buffer contract for non-Vulkan runs

- keeps the established presented-buffer contract for non-Vulkan runs
- Inspect the non-Vulkan provenance branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the established presented-buffer contract for non-Vulkan runs")
step("Inspect the non-Vulkan provenance branch")
val script = file_read("scripts/check/check-wm-production-fullscreen-evidence.shs")
expect(script).to_contain(".render.backend == \"simple-2d-winit-buffer\"")
expect(script).to_contain(".render.readback == \"presented-pixel-buffer\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-1`
- `REQ-5`
- `REQ-6`
- `REQ-7`
- `REQ-8.`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `136088d14cfa568d08fc1382c40e722b0ebc6192052ba3ffa8f43afb882b8bab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `136088d14cfa568d08fc1382c40e722b0ebc6192052ba3ffa8f43afb882b8bab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `136088d14cfa568d08fc1382c40e722b0ebc6192052ba3ffa8f43afb882b8bab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/wm_production_fullscreen_evidence_spec.spl
mirror: doc/06_spec/03_system/check/wm_production_fullscreen_evidence_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/wm_production_fullscreen_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/wm_production_fullscreen_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/wm_production_fullscreen_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/wm_production_fullscreen_evidence_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a Rust seed resolved path before production launch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/wm_production_fullscreen_evidence_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes explicit runtime providers through the pure-Simple final link without stub fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/wm_production_fullscreen_evidence_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships runtime bridges with the hosted TLS implementation enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
