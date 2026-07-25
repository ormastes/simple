# SimpleOS Desktop Framebuffer Baseline Spec

> Builds the desktop target and, when live capture is enabled, compares the

<!-- sdn-diagram:id=simpleos_desktop_framebuffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_desktop_framebuffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_desktop_framebuffer_spec -> std
simpleos_desktop_framebuffer_spec -> os
simpleos_desktop_framebuffer_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_desktop_framebuffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Desktop Framebuffer Baseline Spec

Builds the desktop target and, when live capture is enabled, compares the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_desktop_framebuffer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Builds the desktop target and, when live capture is enabled, compares the
captured framebuffer against the committed baseline.

## Scenarios

### SimpleOS desktop framebuffer baseline (SYS-GUI-006)
_Desktop framebuffer checks must either compare live pixels or keep baseline assets valid._

#### builds desktop_e2e_entry.spl into a baremetal kernel when live capture is enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _desktop_target()
if not _live_framebuffer_capture_enabled():
    print "[simpleos_desktop_fb_spec] desktop build skipped; set SIMPLEOS_QEMU_DESKTOP_FRAMEBUFFER_LIVE=1 or UPDATE_BASELINE=1 to run"
    expect(target.output).to_contain("desktop")
else:
    val ok = build_os(target)
    expect(ok).to_equal(true)
    expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots desktop, captures framebuffer via QMP, and matches baseline

1. dir create all
2. dir create all
   - Expected: capture_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _desktop_target()
if not _live_framebuffer_capture_enabled():
    print "[simpleos_desktop_fb_spec] live framebuffer capture disabled; set SIMPLEOS_QEMU_DESKTOP_FRAMEBUFFER_LIVE=1 to run"
    expect(target.qemu_system).to_contain("qemu-system")
else:
    # Always rebuild here so live compare/update never captures stale
    # output left by an earlier run.
    val built = _build_once(target)
    expect(built).to_equal(true)
    if not built:
        print "[simpleos_desktop_fb_spec] desktop build failed; live capture not attempted"
    else:
        expect(file_exists(target.output)).to_equal(true)

        val disk_ok = ensure_desktop_disk_image()
        if not disk_ok:
            print "[simpleos_desktop_fb_spec] disk image unavailable, skipping live capture"
            expect(file_exists(target.output)).to_equal(true)
        else:
            # Host may not have qemu-system-x86_64 installed — skip the live
            # capture step but keep the build assertion as the hard gate so
            # a missing QEMU never silently hides a build regression.
            if not can_run_target(target):
                print "[simpleos_desktop_fb_spec] qemu-system-x86_64 not available, skipping live capture"
                expect(file_exists(target.output)).to_equal(true)
            else:
                val qmp_socket = "/tmp/simpleos_desktop_qmp.sock"
                val serial_log = "build/os/simpleos_desktop_qemu_serial.log"
                # QEMU's screendump path handling is host-policy sensitive; use /tmp
                # alongside the QMP socket to avoid repo-worktree permission drift.
                val capture_ppm = "/tmp/simpleos_desktop_capture.ppm"
                val baseline_dir = "test/baselines/simpleos_desktop_framebuffer"
                val baseline_path = "{baseline_dir}/desktop_scene.ppm"

                dir_create_all(baseline_dir)
                dir_create_all("build/os")

                val capture_ok = _run_live_capture(target, qmp_socket, serial_log, capture_ppm, baseline_path)
                expect(capture_ok).to_equal(true)
```

</details>

#### has a baseline directory for simpleos_desktop_framebuffer captures

1. dir create all
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline_dir = "test/baselines/simpleos_desktop_framebuffer"
dir_create_all(baseline_dir)
expect(file_exists(baseline_dir)).to_equal(true)
```

</details>

#### has a committed non-empty desktop framebuffer baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline_path = "test/baselines/simpleos_desktop_framebuffer/desktop_scene.ppm"
val (ok, pixels, width, height, err) = _read_baseline_ppm(baseline_path)
if not ok:
    print "[simpleos_desktop_fb_spec] invalid baseline: {err}"
expect(ok).to_equal(true)
expect(width).to_equal(1024)
expect(height).to_equal(768)
expect(_non_black_count(pixels)).to_be_greater_than(0)
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
