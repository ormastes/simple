# Env-gated spec switches are silently INERT under `bin/simple test` (fail-open)

**Filed:** 2026-08-09 (stream P13, while adding `SIMPLE_REQUIRE_GPU` to the GPU lane specs)
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
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

---

## P14 addendum (2026-08-09): `test_env_gate` family audited by measurement

P13 recommended auditing `src/lib/common/test_env_gate.spl`. Done. P13's guess
("likely inert too") is **half right, and the correction matters**: the gates are
not unconditionally inert. Env reaches a spec body **exactly once — at the
invocation that STARTS the light daemon**. Every later request reads that frozen
snapshot, in *either* direction.

### Measurement

Probe: `test/01_unit/lib/common/test_env_gate/p14_env_propagation_probe_spec.spl`
(7 its; each asserts the observed value in the ASSERT MESSAGE, since `step()`
output is not surfaced). Binary: `bin/release/x86_64-unknown-linux-gnu/simple`.

| # | daemon state | caller env | verbatim result |
|---|---|---|---|
| A | cold (`rm -rf .build/test_daemon_light`) | vars exported | `Results: 7 total, 7 passed, 0 failed` |
| B | warm from A | vars **un**exported | `Results: 7 total, 7 passed, 0 failed` ← **stale AVAILABLE** |
| C | cold | vars unexported | `Results: 7 total, 0 passed, 7 failed` (`expected observed=nil to equal observed=1`) |
| D | warm from C | vars exported | `Results: 7 total, 0 passed, 7 failed` ← **stale UNAVAILABLE** |

B and D are the defect; A and C prove the oracle is not a tautology (same file,
same assertions, opposite verdicts). `bin/simple run` on a direct probe printed
`HW=true` with `SIMPLE_HW_TEST=1` and `HW=false` without — the **run path is
correct**.

### Per-gate verdict

All eight gates share one code path (`test_env_available` → `rt_env_get`), so
the verdict is uniform and is a property of the *daemon*, not of any gate:

| gate | `bin/simple run` | `bin/simple test` | verdict |
|---|---|---|---|
| `SIMPLE_HW_TEST` | correct | frozen at daemon start | 2 in practice, 3 if daemon started with it set |
| `SIMPLE_QEMU_TEST` | correct | frozen | same |
| `SIMPLE_NET_TEST` | correct | frozen | same |
| `SIMPLE_GPU_TEST` | correct | frozen | same |
| `SIMPLE_CUDA_TEST` | correct | frozen | same |
| `SIMPLE_LLVM_TEST` | correct | frozen | same |
| `SIMPLE_VHDL_TEST` | correct | frozen | same |
| `SIMPLE_WASM_TEST` | correct | frozen | same |

**Steady state is outcome 2** (always-skip, vacuous green): the first
`bin/simple test` of a session starts the daemon with no gate vars, so every
later `SIMPLE_GPU_TEST=1 bin/simple test ...` still sees the gate CLOSED.
Outcome 3 (always-run) needs a daemon that was *started* with the var set.

### Blast radius

47 spec files reference `test_env_gate`; discounting the `test/unit/**` and
`test/feature/**` legacy mirrors, the gate's own unit spec, and the P14 probe,
**27 canonical specs are affected**:

- `SIMPLE_HW_TEST` (1): `test/01_unit/app/serial_mcp/serial_mcp_spec.spl`
- `SIMPLE_QEMU_TEST` (0), `SIMPLE_NET_TEST` (0): declared, no canonical consumer yet
- `SIMPLE_GPU_TEST` (14): `test/01_unit/lib/gpu/engine2d/{backend_qualcomm,device_detect,engine_platform,ffi_cuda,ffi_intel,ffi_rocm,ffi_vulkan}_spec.spl`, `test/01_unit/lib/gc_async_mut/processing/fault_injection_spec.spl`, `test/03_system/app/simpleos_gpu_host/{gpu_backend_failure_injection,macos_metal_processing_ir_failure_injection,processing_ir_fault_source_contract,processing_vulkan_fault_native_contract}_spec.spl`, `test/03_system/feature/usage/{tensor_interface,vulkan}_spec.spl`
- `SIMPLE_CUDA_TEST` (3): `test/03_system/feature/usage/{cuda,gpu_ptx_gen}_spec.spl`, `test/03_system/io_audio/simple_audio_cuda_q15_env_spec.spl`
- `SIMPLE_LLVM_TEST` (6): `test/03_system/feature/usage/llvm_backend{,_aarch64,_arm32,_i686,_riscv32,_riscv64}_spec.spl`
- `SIMPLE_VHDL_TEST` (2): `test/03_system/feature/usage/{vhdl,vhdl_golden}_spec.spl`
- `SIMPLE_WASM_TEST` (1): `test/03_system/feature/usage/wasm_compile_spec.spl`

Their hardware-path branches have effectively **never executed under
`bin/simple test`**; the green they contribute is the skip branch's green.

### Fix

`src/app/test_runner_new/test_runner_client.spl`: `_test_env_gate_vars()` /
`_test_env_gate_names()` + `env_gate_bypass`, folded into the existing
`daemon_ok` divert alongside `cov_bypass` / `require_gpu_bypass`. Verified
against the exact scenario D above: same warm gate-less daemon, vars exported →
`test-env-gate: SIMPLE_HW_TEST, SIMPLE_QEMU_TEST, SIMPLE_NET_TEST,
SIMPLE_GPU_TEST, SIMPLE_LLVM_TEST set; bypassing test daemon so the gate reaches
the spec` and `Results: 7 total, 7 passed, 0 failed` (was 0/7 before the edit).

The v2-request fix from the list above is still the right one and is **not** done
here: it needs a protocol change on both client and daemon, which is larger than
an audit stream should land blind.

### Residual gaps, stated plainly

- **Scenario B is not fixed.** A daemon started *with* a gate var set keeps
  reporting it available to later runs that do not set it. The bypass only
  triggers when the caller sets a var, and the request carries no environment,
  so there is nothing to compare against. Only the v2 request closes this.
- The bypass costs the daemon's warm-start saving on any gated run. Accepted:
  a correct slow answer beats a fast vacuous one.
- Not measured: whether the gated hardware branches actually *pass* on this host
  once they really run. This box has CUDA + Vulkan, no Metal, Linux — the Metal
  and Qualcomm specs would need their own host-awareness audit. Out of scope
  here, and deliberately not enabled.
