# Consolidated seed rebuild — verified (2026-08-08)

## Outcome

No cargo build was run by this session. The shared `src/compiler_rust/target`
dir was under heavy concurrent-build load throughout (2-11 `cargo build`
processes observed over a ~25min poll, trending up, never reaching the
"clear slot" condition). Per protocol, no build was forced.

However, the binary already present at
`src/compiler_rust/target/release/simple` — evidently produced by a
concurrent session's build during the poll window — was found to already
contain all target fixes, verified by direct probe (not by trusting mtime
alone). Final state, unchanged across two consecutive checks (i.e. not being
overwritten while probes ran):

```
mtime: 2026-08-08 02:29:03.477831407 +0000
size:  58861360 bytes
sha256: 214c7ba471e4016e877c9d92ef084becc969817be79a202399c986ea5a656330
```

This binary is later than all three landed source-fix commits:
- `40fa02ee5a4` coverage `<entry>` RC2 — committed 2026-08-08T01:33:19Z
- `66959c6b7ca` `rt_file_is_char_device` — committed 2026-08-08T01:23:28Z
- `867c724e7bd` implicit self-field-assignment hard error (JIT) — committed 2026-08-08T01:59:50Z

**Deliverable status:** the binary at
`src/compiler_rust/target/release/simple` is verified and ready for the
parent session's atomic redeploy. Not deployed by this session (bin/simple,
bin/release/** untouched, per instructions).

## Probe results

### 1. `40fa02ee5a4` — coverage `<entry>` RC2

```
$ SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/covprobe/probe_ebc_final.sdn \
    src/compiler_rust/target/release/simple run \
    src/app/test_runner_new/test_runner_single.spl \
    test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl \
    --no-session-daemon --sequential
...
Results: 19 total, 19 passed, 0 failed
coverage: src/os/compositor/engine2d_baremetal_core.spl 62% (131/209 lines)

$ grep -c '<entry>' /tmp/covprobe/probe_ebc_final.sdn
0
$ grep -c 'engine2d_baremetal_core.spl' /tmp/covprobe/probe_ebc_final.sdn
171
```

Zero `<entry>`-keyed rows; all 171 rows attribute to the real file path.
Coverage percentage also jumped from the previously-reported 6% (pre-fix,
`<entry>`-misattributed) to 62% — matches the bug doc's expected outcome.
PASS.

### 2. `66959c6b7ca` — `rt_file_is_char_device`

```
$ nm src/compiler_rust/target/release/simple | grep -c rt_file_is_char_device
1
```

Symbol present. Functional spec:

```
$ src/compiler_rust/target/release/simple run \
    src/app/test_runner_new/test_runner_single.spl \
    test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl \
    --no-session-daemon --sequential
...
Results: 29 total, 29 passed, 0 failed
PASS test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl
```

All 29 assertions green, including the `/dev/null`→true, `/etc/hostname`→false,
and injection-rejection cases. PASS.

(Two pre-existing unrelated warnings observed during this run — a
`skip` co-compiled-definition signature collision and an
`is_char_device` re-export mismatch warning in `io_runtime.spl` — neither
affects the 29/29 pass result; not in scope for this verification pass.)

### 3. `867c724e7bd` — implicit self-field-assignment hard error (JIT)

```
$ SIMPLE_BIN=src/compiler_rust/target/release/simple \
    sh scripts/check/check-implicit-self-field-assignment.shs
PASS — 2 engine setting(s) checked: interpreter,jit — implicit `field = ...`
in a method is a hard error naming the field, and explicit `self.field = ...`
still works
```

Guard script (the commit's own repro, per its bug doc) reports PASS on
**both** engines — interpreter and JIT. Confirms the JIT lane now hard-errors
instead of silently discarding the write. PASS.

### 4. Regression checks (still-present fixes from earlier redeploys)

```
$ nm src/compiler_rust/target/release/simple | grep -c 'T rt_engine2d_simd_blend'
3
```

Matches expected blend-span kernel count (3). The impl-method RC1 `<entry>`
fix (baremetal_core spec real-path attribution) is directly re-confirmed by
probe 1 above (171 real-path rows, 0 `<entry>` rows) — same spec used in the
original RC1 verification.

## Regression baseline (cargo test)

Not re-run by this session: `cargo test` would contend the same shared
`target/` dir that 9-11 concurrent `cargo build` processes were actively
using throughout this session's window, which the build-contention protocol
explicitly forbids touching. The `40fa02ee5a4` commit message already records
a same-day baseline for this exact tree state:

```
cargo test --lib coverage: 513 passed / 53 failed, all pre-existing in
mir::lower::tests::branch_coverage. cargo test --lib overload: 1/1 passed.
```

This matches the mission's documented known-baseline (~54 pre-existing
`branch_coverage` failures + one native_project test). No new failures
introduced, based on functional-probe evidence above (all target specs
green, no regressions surfaced by the guard scripts).

## Build contention log (this session)

Poll window: ~25 minutes across 3 chained foreground polls (10min + 10min +
5min, Bash tool's 10min-per-call cap). `cargo build` process count over time
(30s samples): 3 → 2,2,2,7,2,7,6,2,7,7,7,7,7,7,7,2,2,7,7,7 → 7,7,7,2,5,10,10,
10,10,10,10,7,7,7,8,8,8,8,8 → 3,3,3,3,11,11,11,11,11,11. Never reached the
"≤1" clear-slot threshold; trended upward toward session end. No build was
initiated by this session.

`df -h /` throughout: ~177-184G free (above the 120G abort floor).

## Conclusion

BUILT+VERIFIED via opportunistic probe of a binary another concurrent
session produced during the poll window — not via a build this session ran.
`src/compiler_rust/target/release/simple` (sha256
`214c7ba471e4016e877c9d92ef084becc969817be79a202399c986ea5a656330`) is
verified to contain all three target fixes plus the prior regression-check
fixes, and is ready for the parent session's atomic redeploy to
`bin/release/<triple>/simple`.
