# Env-gated spec switches are silently INERT under `bin/simple test` (fail-open)

**Filed:** 2026-08-09 (stream P13, while adding `SIMPLE_REQUIRE_GPU` to the GPU lane specs)
**Status:** OPEN — one instance fixed (`SIMPLE_REQUIRE_GPU`), the general defect remains
**Severity:** high — it makes every env-gated strictness switch in a spec fail OPEN

## Symptom

An environment variable set by the caller does **not** reach the spec body under
`bin/simple test`. Measured with a tripwire assertion inside
`test/03_system/gpu_lane/cuda_debug_session_conformance_spec.spl`:

```
$ SIMPLE_REQUIRE_GPU=1 bin/simple test test/03_system/gpu_lane/cuda_debug_session_conformance_spec.spl
assert_equal failed: expected TRIPWIRE, got ENVSEEN[nil]        # via std.env.variables.env_get
assert_equal failed: expected TRIPWIRE, got ENVSEEN[false]      # via std.common.test_env_gate.test_env_available
```

The same variable, same shell, under `bin/simple run`, is read correctly:

```
$ SIMPLE_REQUIRE_GPU=1 bin/simple run p13_env.spl
ENVVAL=[1]
```

So this is not an accessor bug — **both** accessors are correct, and the raw
`rt_env_get` extern underlies both. The value never arrives.

Binary identity: `bin/release/x86_64-unknown-linux-gnu/simple`, 29577536 bytes,
mtime 2026-08-09 04:50:31, md5 `d96f87a191403fd53aca879ee689ecdf`
(worktree at origin/main `7f4004e1ff1`).

## Root cause — already documented, not generalised

`src/app/test_runner_new/test_runner_client.spl:426-440` describes this exact
defect class for `SIMPLE_COVERAGE` and `SIMPLE_TEST_BINARY`:

> The light daemon is a long-lived process whose environment is frozen at
> whichever invocation happened to start it; the v1 request carries only a
> header, an expiry and a path — **no environment at all**. So a spec that
> resolves [anything] from the environment reads the DAEMON's stale value, not
> the caller's.

The existing mitigation is an **allowlist**: each known variable gets its own
`*_bypass` flag that forces the direct lane (`cov_bypass`,
`binary_override_bypass`, `long_timeout_bypass`, `invoker_bypass`). Any variable
**not** on that list is silently frozen.

## Why this is worse than the documented instances

`SIMPLE_COVERAGE` under-reports; `SIMPLE_TEST_BINARY` tests the wrong binary.
Both are bad, but a **strictness** switch fails in the most dangerous direction:

- The switch exists to turn a permissive skip into a hard failure.
- Frozen, the spec observes the variable as unset and takes the **permissive**
  branch.
- The lane that explicitly demanded real device evidence gets a **green that
  proves nothing** — precisely the hole the switch was added to close.

A CI lane could run `SIMPLE_REQUIRE_GPU=1` forever, on a machine with no GPU,
and stay green.

## Fix applied (this instance only)

`src/app/test_runner_new/test_runner_client.spl` — added `require_gpu_bypass`
alongside the existing bypasses, so a request naming `SIMPLE_REQUIRE_GPU` takes
the direct lane where the child really does inherit it. Verified:

```
$ SIMPLE_REQUIRE_GPU=1 bin/simple test <cuda spec>
require-gpu: SIMPLE_REQUIRE_GPU set; bypassing test daemon so the requirement reaches the spec
```

Truth matrix, all four cells verified by sabotaging `_probe()` to force each
branch (device present = live RTX A6000):

| probe result | `SIMPLE_REQUIRE_GPU` | verdict | evidence in output |
|---|---|---|---|
| device (`probe()==""`) | unset | GREEN | 20 launches diffed |
| device | `1` | GREEN | 20 launches diffed |
| `skip:` (forced) | unset | GREEN | skip-clean, default preserved |
| `skip:` (forced) | `1` | **RED** | `expected DEVICE-RAN: cuda, got SKIPPED: skip:forced-sabotage` |

## The general defect remains OPEN

The allowlist approach means **the next env-gated spec switch will be inert
again, silently**. Every variable added to a spec must also be added here, and
nothing enforces or even detects that coupling.

Known-suspect existing callers that read env inside a spec body and may already
be inert under the daemon (NOT verified by this stream):

- `std.common.test_env_gate.{test_env_hardware_available, test_env_qemu_available,
  test_env_network_available, test_env_gpu_available}` — i.e. `SIMPLE_HW_TEST`,
  `SIMPLE_QEMU_TEST`, `SIMPLE_NET_TEST`, `SIMPLE_GPU_TEST`. This module exists
  *specifically* to gate specs on env, so if it is frozen, every gate built on
  it is fail-open. **This should be audited next.**
- `test/03_system/app/browser/feature/*_spec.spl` — `HOSTED_WM_ARTIFACT`,
  `HOSTED_WM_ARTIFACT_SHA256`.

## Proper fixes, in preference order

1. **Carry the caller's environment in the daemon request.** The v1 request
   format carries no environment at all; that is the actual defect. A v2 request
   that ships the caller's env removes the entire bug class and makes the
   allowlist unnecessary.
2. **Invert to a denylist / prefix rule** — bypass the daemon whenever any
   `SIMPLE_*` variable is set that the daemon did not start with. Fails closed.
3. **A guard** that greps spec sources for env reads and fails when a variable
   is not in the bypass list. Weakest — it only catches the specs, not lib code
   they call.

## Reproduce

```bash
# tripwire: assert the value the spec body actually observes
SIMPLE_REQUIRE_GPU=1 bin/simple test test/03_system/gpu_lane/cuda_debug_session_conformance_spec.spl
# before the fix: spec body observes nil/false while the caller has it set to "1"
```
