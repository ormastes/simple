# SOSIX Mac host runtime access — acceptance manual

Executable: `test/03_system/runtime/sosix_host_runtime_access_spec.spl`.
Plan: [platform/API matrix](../../../03_plan/sys_test/sosix_hal_runtime_access_2026-10-29.md).

This is a five-example accessibility smoke test through exported SOSIX leaves.
It does not measure whole-module coverage or qualify process launch. Run from
the checkout root with `SIMPLE_LIB=src` using the intended Simple runtime and
record its path, SHA-256, command, exit status, counts and retained output.

| Step | Observation required |
|---|---|
| Read host identity through SOSIX leaves | `macos` and PID greater than zero |
| Query host filesystem existence through SOSIX | `/bin/sh` present; unique missing path absent |
| Read PATH and a unique absent key through SOSIX | PATH present/nonempty; absent key nil |
| Sample both SOSIX clock domains | Monotonic advances after a 3 ms SOSIX sleep; realtime exceeds 10^18 ns |
| Read the linked V1 provider capability through SOSIX | Explicit `Unsupported` on Mac |

The first monotonic sample may be zero. A constant-zero clock still fails the
advancement assertion. A failed clock Result fails via unwrap. No elapsed-time
upper bound is imposed because scheduling delays are not clock-provider failure.

On other hosts, all five examples are explicitly skipped at describe level.
They must never become assertion-free passed examples. On Mac, acceptance
requires five executed and passed examples with zero failures or skips.

Interpreter, diagnostic seed and compiled Simple results are separate receipts.
An interpreter pass does not establish native symbol linkage; a native runner
crash or zero examples remains blocked. The V1 unavailable result verifies the
refusal boundary only. Strict V4 launch, cooperative snapshot launch, native
asynchronous filesystem providers, and non-Mac qualification are outside this
smoke test.
