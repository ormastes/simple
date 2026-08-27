# x86_64 SimpleOS WM QEMU preflight

> Verifies static ownership and the evidence route for the production x86_64

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64 SimpleOS WM QEMU preflight

Verifies static ownership and the evidence route for the production x86_64

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/x86_64_wm_qemu_preflight_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies static ownership and the evidence route for the production x86_64
desktop without starting QEMU. Live framebuffer and input proof remains a
separate host-gated operation.

## Scenarios

### x86_64 SimpleOS WM QEMU static preflight

#### routes theme, SIMD, framebuffer and events through canonical owners

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes theme, SIMD, framebuffer and events through canonical owners
- Inspect the canonical desktop theme and first-frame route
- Require the legacy command to delegate to production evidence
   - Expected: compat does not contain `ENTRY="examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl"`
- Require retained QMP framebuffer and input evidence
- Run static-only preflight without starting QEMU
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes theme, SIMD, framebuffer and events through canonical owners")
step("Inspect the canonical desktop theme and first-frame route")
val entry = file_read(ENTRY)
expect(entry).to_contain("install_generated_simpleos_wm_theme()")
expect(entry).to_contain("Engine2dWmFrameExecutor.create_host_gpu")
expect(entry).to_contain("shell.render_baremetal_first_frame(wm_frame_executor)")
expect(entry).to_contain("[engine2d-simd] arch=x86_64 isa=sse2 enabled=1")

step("Require the legacy command to delegate to production evidence")
val compat = file_read(COMPAT)
expect(compat).to_contain("check-simpleos-wm-fullscreen-evidence.shs")
expect(compat.contains("ENTRY=\"examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl\"")).to_equal(false)

step("Require retained QMP framebuffer and input evidence")
val canonical = file_read(CANONICAL)
expect(canonical).to_contain("ENTRY=\"examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl\"")
expect(canonical).to_contain("input-send-event")
expect(canonical).to_contain("pmemsave")
expect(canonical).to_contain("scancode=87 kind=press")
expect(canonical).to_contain("scancode=215 kind=release")
expect(canonical).to_contain("wait_release_receipt")
expect(entry).to_contain("shell.run_baremetal(wm_frame_executor)")

step("Run static-only preflight without starting QEMU")
val (out, _err, code) = process_run("/bin/sh", [PREFLIGHT])
expect(code).to_equal(0)
expect(out).to_contain("simpleos_x86_64_wm_qemu_preflight_status=pass")
expect(out).to_contain("simpleos_x86_64_wm_qemu_preflight_live_qemu=not-started-host-gate")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-1`
- `REQ-2`
- `REQ-7`
- `REQ-8`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7d34c8611288e568b53bc9cac2ca259a3684d9f9a3f706f600e7481edf2466f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7d34c8611288e568b53bc9cac2ca259a3684d9f9a3f706f600e7481edf2466f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7d34c8611288e568b53bc9cac2ca259a3684d9f9a3f706f600e7481edf2466f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/x86_64_wm_qemu_preflight_spec.spl
mirror: doc/06_spec/03_system/gui/x86_64_wm_qemu_preflight_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/gui/x86_64_wm_qemu_preflight_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/x86_64_wm_qemu_preflight_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/x86_64_wm_qemu_preflight_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/x86_64_wm_qemu_preflight_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/x86_64_wm_qemu_preflight_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes theme, SIMD, framebuffer and events through canonical owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
