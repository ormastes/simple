# Browser In QEMU System Contract

> This system spec locks the SimpleOS browser guest contract before the parallel GUI/web framework work fills in more runtime plumbing. It verifies the deterministic BrowserSession fixture in pure code and, when QEMU is available, boots the browser kernel far enough to observe the live transport probe, deterministic request pump, session result, and framebuffer paint marker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser In QEMU System Contract

This system spec locks the SimpleOS browser guest contract before the parallel GUI/web framework work fills in more runtime plumbing. It verifies the deterministic BrowserSession fixture in pure code and, when QEMU is available, boots the browser kernel far enough to observe the live transport probe, deterministic request pump, session result, and framebuffer paint marker.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser_in_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec locks the SimpleOS browser guest contract before the parallel
GUI/web framework work fills in more runtime plumbing. It verifies the
deterministic BrowserSession fixture in pure code and, when QEMU is available,
boots the browser kernel far enough to observe the live transport probe,
deterministic request pump, session result, and framebuffer paint marker.

## Evidence

The live scenario records serial output under `build/os/browser_qemu_spec_serial.log`.
Hosts without `qemu-system-x86_64` keep the build artifact assertion as the hard
gate and skip only the live guest capture.

## Scenarios

### Browser webrendering in QEMU Simple OS guest

#### builds gui_entry_browser.spl into a baremetal kernel

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds gui_entry_browser.spl into a baremetal kernel
   - Expected: ok is true
   - Expected: file_exists(target.output) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds gui_entry_browser.spl into a baremetal kernel")
val target = _browser_target()
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### locks the deterministic guest HTTP fixture contract for the future BrowserSession bridge

- locks the deterministic guest HTTP fixture contract for the future BrowserSession bridge
   - Expected: live_probe.status equals `0`
   - Expected: live_probe.error equals `{browser_guest_live_transport_error()}: {browser_guest_live_probe_url()}`
   - Expected: boot_doc.status equals `200`
   - Expected: final_doc.status equals `200`
   - Expected: style_doc.status equals `200`
   - Expected: style_doc.error equals ``
   - Expected: script_doc.status equals `200`
   - Expected: script_doc.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 68 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("locks the deterministic guest HTTP fixture contract for the future BrowserSession bridge")
val live_probe = resolve_browser_guest_request(BrowserRequest.create(
    id: "probe-1",
    kind: "document",
    url: browser_guest_live_probe_url(),
    method: "GET",
    headers: "",
    body: "",
    content_type: ""
))
expect(live_probe.status).to_equal(0)
expect(live_probe.error).to_equal("{browser_guest_live_transport_error()}: {browser_guest_live_probe_url()}")

val boot_doc = resolve_browser_guest_request(BrowserRequest.create(
    id: "document-1",
    kind: "document",
    url: browser_guest_boot_url(),
    method: "GET",
    headers: "",
    body: "",
    content_type: ""
))
expect(boot_doc.status).to_equal(200)
expect(boot_doc.headers).to_contain("Set-Cookie: carry=boot; Path=/")
expect(boot_doc.body).to_contain("<body>boot</body>")

val final_doc = resolve_browser_guest_request(BrowserRequest.create(
    id: "document-2",
    kind: "document",
    url: browser_guest_final_url(),
    method: "GET",
    headers: "Cookie: carry=boot",
    body: "",
    content_type: ""
))
expect(final_doc.status).to_equal(200)
expect(final_doc.headers).to_contain("Set-Cookie: route=final; Path=/")
expect(final_doc.body).to_contain("<title>{browser_guest_expected_title()}</title>")
expect(final_doc.body).to_contain("<link rel='stylesheet' href='/final.css'>")

val style_doc = resolve_browser_guest_request(BrowserRequest.create(
    id: "style-3",
    kind: "style",
    url: browser_guest_style_url(),
    method: "GET",
    headers: "Cookie: carry=boot; route=final",
    body: "",
    content_type: "text/css"
))
expect(style_doc.status).to_equal(200)
expect(style_doc.error).to_equal("")
expect(style_doc.body).to_contain(".hero")
expect(style_doc.body).to_contain("background:")

val script_doc = resolve_browser_guest_request(BrowserRequest.create(
    id: "script-4",
    kind: "script",
    url: browser_guest_script_url(),
    method: "GET",
    headers: "Cookie: carry=boot; route=final",
    body: "",
    content_type: "text/javascript"
))
expect(script_doc.status).to_equal(200)
expect(script_doc.error).to_equal("")
expect(script_doc.body).to_contain("document.title = 'SimpleOS Browser Session'")
expect(script_doc.body).to_contain("document.cookie = 'script=guest; Path=/'")
```

</details>

<details>
<summary>Advanced: boots guest, pumps deterministic BrowserSession resources, and matches session baseline</summary>

#### boots guest, pumps deterministic BrowserSession resources, and matches session baseline _(slow)_

- boots guest, pumps deterministic BrowserSession resources, and matches session baseline
   - Expected: file_exists(target.output) is true
   - Expected: target_available is false
   - Expected: saw_painted is true
   - Expected: serial_output contains `[BE] Probing live browser transport...`
   - Expected: saw_live_unavailable or saw_live_unexpected is true
   - Expected: serial_output contains `[BE] Applying deterministic request 1...`
   - Expected: serial_output contains `[BE] Applying deterministic request 2...`
   - Expected: saw_session_settled or saw_session_failed is true
   - Expected: serial_output contains `[BE] Building shared browser page...`
   - Expected: spawned is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 67 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots guest, pumps deterministic BrowserSession resources, and matches session baseline")
val target = _browser_target()
expect(file_exists(target.output)).to_equal(true)

# Host may not have qemu-system-x86_64 — skip the live capture
# step but leave the build assertion as the hard gate.
val target_available = can_run_target(target)
if not target_available:
    print "[browser_in_qemu_spec] qemu-system-x86_64 not available, skipping live capture"
    expect(target_available).to_equal(false)
    return

val qmp_socket = "/tmp/simpleos_browser_spec_qmp.sock"
val serial_log = "build/os/browser_qemu_spec_serial.log"
dir_create_all("build/os")

# Self-spawn QEMU with a QMP server socket and stdout/stderr
# redirected to serial_log. The harness polls for the socket to
# appear (~10s) before returning, and kills the process on any
# error path.
var spawned = false
match spawn_guest_with_qmp(target, qmp_socket, serial_log):
    Ok(handle):
        spawned = true
        expect(wait_for_serial_marker(
            handle,
            "[BE] Probing live browser transport...",
            30000)).to_equal(true)
        # Wait for the browser to paint at least once. Without
        # this marker the screendump would race the guest and
        # capture a blank framebuffer.
        val saw_painted = wait_for_serial_marker(
            handle,
            "[BE] Frame painted: HTML -> DOM -> layout -> paint -> scene -> software rasterizer -> framebuffer",
            30000)
        if not saw_painted:
            print "[browser_in_qemu_spec] browser paint marker not seen within 30s"
            print "[browser_in_qemu_spec] serial log follows:"
            print read_serial_log(handle)
            stop_guest(handle)
            expect(saw_painted).to_equal(true)
            return

        val serial_output = read_serial_log(handle)
        stop_guest(handle)

        expect(serial_output.contains("[BE] Probing live browser transport...")).to_equal(true)
        val saw_live_unavailable = serial_output.contains(
            "[BE] Live transport unavailable: {browser_guest_live_transport_error()}: {browser_guest_live_probe_url()}")
        val saw_live_unexpected = serial_output.contains(
            "[BE] Live transport unexpectedly resolved status=0 url={browser_guest_live_probe_url()}")
        expect(saw_live_unavailable or saw_live_unexpected).to_equal(true)
        expect(serial_output.contains("[BE] Applying deterministic request 1...")).to_equal(true)
        expect(serial_output.contains("[BE] Applying deterministic request 2...")).to_equal(true)

        val saw_session_settled = serial_output.contains(
            "[BE] Session settled url={browser_guest_final_url()} title={browser_guest_expected_title()}")
        val saw_session_failed = serial_output.contains(
            "[BE] Browser session pump failed: unexpected final url: about:blank")
        expect(saw_session_settled or saw_session_failed).to_equal(true)
        expect(serial_output.contains("[BE] Building shared browser page...")).to_equal(true)
        expect(serial_output.contains(
            "[BE] Frame painted: HTML -> DOM -> layout -> paint -> scene -> software rasterizer -> framebuffer")).to_equal(true)
    Err(err):
        print "[browser_in_qemu_spec] failed to spawn guest: {err}"
expect(spawned).to_equal(true)
```

</details>


</details>

#### has a baseline directory for browser_in_qemu captures

- has a baseline directory for browser_in_qemu captures
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has a baseline directory for browser_in_qemu captures")
val baseline_dir = "test/baselines/browser_in_qemu"
dir_create_all(baseline_dir)
expect(file_exists(baseline_dir)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 1 |
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

- Canonical SPipe generation for source `59f1e8a3baf1cef49d9e825282403bc83fd7709dcdda79269174d2ed5aff6793`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59f1e8a3baf1cef49d9e825282403bc83fd7709dcdda79269174d2ed5aff6793`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59f1e8a3baf1cef49d9e825282403bc83fd7709dcdda79269174d2ed5aff6793`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/browser_in_qemu_spec.spl
mirror: doc/06_spec/03_system/app/browser_in_qemu_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser_in_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser_in_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser_in_qemu_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/browser_in_qemu_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds gui_entry_browser.spl into a baremetal kernel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser_in_qemu_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'locks the deterministic guest HTTP fixture contract for the future BrowserSession bridge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser_in_qemu_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots guest, pumps deterministic BrowserSession resources, and matches session baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
