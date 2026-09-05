# GUI Showcase Performance Probe-Exit Contract

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

## Overview

Prevents partial 4K/8K benchmark output from becoming retained performance
evidence after the producer crashes or times out. This focused contract checks
exit admission only; it does not launch a renderer or prove the 200 FPS target.

## Scenarios

### GUI showcase performance probe exit

#### rejects every nonzero producer exit before parsing partial rows

- Run the zero, failure, and timeout exit classifier
  - Expected: the wrapper self-test exits `0` and emits
    `widget_showcase_perf_probe_exit_self_test_status=pass`.
- Verify the producer gate uses the checked classifier
  - Expected: the live producer rejects `probe_rc != 0` before row parsing and
    does not retain the previous width-marker exception.

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.

```simple
step("Run the zero, failure, and timeout exit classifier")
val (stdout, _stderr, code) = process_run(
    "/bin/sh", ["scripts/check/check-widget-showcase-4k-200fps.shs", "--self-test"])
expect(code).to_equal(0)
expect(stdout).to_contain("widget_showcase_perf_probe_exit_self_test_status=pass")
step("Verify the producer gate uses the checked classifier")
val source = file_read("scripts/check/check-widget-showcase-4k-200fps.shs")
expect(source).to_contain("if ! probe_exit_passes \"$probe_rc\"; then")
expect(source.contains("[ \"$probe_rc\" -ne 0 ] && ! grep")).to_be(false)
```

</details>

## Completion Boundary

This scenario proves fail-closed process-exit admission only. Native 4K/8K
throughput, RSS, framebuffer, backend, and RenderDoc rows remain separate gates.
