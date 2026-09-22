# SimpleOS WM Build-Progress Astra Review — 2026-09-22

Status: **ACCEPTED for the build-harness fix; live guest render benchmark unavailable**

Reviewed range: `e0dd873da1b..HEAD` on
`work/nil-array-source-20260922`, including both Astra P1 corrections after
`00682d6ddb8`.

## Reproducer and correctness evidence

The defect was an interruptible background heartbeat/build pair whose cleanup
was not owned by the exit trap. The focused regression test exercises normal
completion, command failure, and `TERM` while a 30-second worker is live. A
test-local `sleep` wrapper records the heartbeat sleep PID independently. Every
exit mode requires both worker and heartbeat-sleep PIDs to be absent afterward:

```text
$ sh test/system/simpleos/wm_native_build_progress_test.shs
PASS: WM native-build progress latency and descendant cleanup after completion, failure, and signal
```

Test SHA-256:
`ff8a8fec5afaa8a74b5da168373b4c33011b689fbccda3d5862e0a9dcbe0d466`.

The implementation keeps the worker and poll PIDs in the parent shell, waits
for the worker, immediately kills and reaps the poller, preserves the wrapped
command's nonzero result, and maps `INT`/`TERM` to 130/143 before the `EXIT`
cleanup runs. The heartbeat also owns its current sleep PID with local
`INT`/`TERM`/`EXIT` traps, so stopping the heartbeat kills and reaps its leaf
rather than reparenting it to PID 1. An Astra P1 review found that the earlier synchronous-poll form
made a fast command wait for the default five-second sleep. The focused test
now runs `/bin/true` with that default and rejects latency of one second or
more. A final Astra review then reproduced a PPID-1 orphan from the heartbeat's
foreground `sleep 5`; the independent descendant assertions reproduce that
failure without the local trap and pass with it. No unconditional success,
orphaned heartbeat descendant, or poll-interval latency path remains.

## Performance and memory review

The change does not modify the guest render closure. Exact Git tree identities
for the pre-change and reviewed revisions are equal:

| Tree | `e0dd873da1b` | reviewed `HEAD` |
|---|---|---|
| `src/os` | `f43b9dc1f00136e6b3ea76bc864e83f73bfef8c6` | `f43b9dc1f00136e6b3ea76bc864e83f73bfef8c6` |
| `src/lib` | `460bbd5f39dffbba05e457b31807e613270ec354` | `460bbd5f39dffbba05e457b31807e613270ec354` |

Therefore the rendered-frame hot path, allocation behavior, and guest maximum
RSS are structurally unchanged. The progress poll exists only while compiling;
it is neither linked into the kernel nor executed per frame. Its default wakeup
rate is one poll per five seconds, and the log-size probe runs only once per
60-second progress interval.

The corrected focused harness was measured with GNU `time` around the quick,
completion, failure, and signal workload:

| Wall seconds | Maximum RSS KiB |
|---:|---:|
| 2.21 | 2008 |

The quick-command subcase completed below its one-second rejection threshold;
before the P1 correction the reviewer measured 5.00 seconds and 2192 KiB for
the helper around `/bin/true` (direct baseline: 0.00 seconds and 884 KiB).

These are build-harness measurements, not guest-frame measurements. A live
frame-time/max-RSS comparison was not admitted because the only locally
resolved CLI (`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
SHA-256 `11a4cb54e47f29da3a39eda169c656af856221f1f965792a411a0ac95b05c6b3`)
self-identifies as the Rust bootstrap seed. Repository policy forbids promoting
seed execution as self-hosted Simple evidence. This review consequently makes
no new live-render performance claim; it accepts non-regression because the
entire guest render source trees are byte-identical and the new work is outside
the runtime artifact.

## Verdict

- Correctness reproducer: PASS.
- Worker/poll process ownership and failure propagation: PASS.
- Guest hot-path source and allocation-shape non-regression: PASS (identical
  `src/os` and `src/lib` trees).
- Build-harness bounded time/RSS observation: PASS.
- New live guest frame-time/max-RSS receipt: UNAVAILABLE, not substituted.
