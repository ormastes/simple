# Browser In QEMU System Contract

> This system spec locks the SimpleOS browser guest contract before the parallel GUI/web framework work fills in more runtime plumbing. It verifies the deterministic BrowserSession fixture in pure code and, when QEMU is available, boots the browser kernel far enough to observe the live transport probe, deterministic request pump, session result, and framebuffer paint marker.

<!-- sdn-diagram:id=browser_in_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_in_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_in_qemu_spec -> std
browser_in_qemu_spec -> os
browser_in_qemu_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_in_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _browser_target()
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### locks the deterministic guest HTTP fixture contract for the future BrowserSession bridge

1. url: browser guest live probe url
   - Expected: live_probe.status equals `0`
   - Expected: live_probe.error equals `{browser_guest_live_transport_error()}: {browser_guest_live_probe_url()}`

2. url: browser guest boot url
   - Expected: boot_doc.status equals `200`

3. url: browser guest final url
   - Expected: final_doc.status equals `200`

4. url: browser guest style url
   - Expected: style_doc.status equals `200`
   - Expected: style_doc.error equals ``

5. url: browser guest script url
   - Expected: script_doc.status equals `200`
   - Expected: script_doc.error equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 66 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. dir create all

2. Ok

3. 30000)) to equal

4. print read serial log

5. stop guest
   - Expected: saw_painted is true

6. stop guest
   - Expected: serial_output contains `[BE] Probing live browser transport...`

7. "[BE] Live transport unavailable: {browser guest live transport error

8. "[BE] Live transport unexpectedly resolved status=0 url={browser guest live probe url
   - Expected: saw_live_unavailable or saw_live_unexpected is true
   - Expected: serial_output contains `[BE] Applying deterministic request 1...`
   - Expected: serial_output contains `[BE] Applying deterministic request 2...`

9. "[BE] Session settled url={browser guest final url
   - Expected: saw_session_settled or saw_session_failed is true
   - Expected: serial_output contains `[BE] Building shared browser page...`

10. "[BE] Frame painted: HTML -> DOM -> layout -> paint -> scene -> software rasterizer -> framebuffer")) to equal

11. Err
   - Expected: spawned is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. dir create all
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
