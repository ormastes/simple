# SimpleOS QEMU primitive verification — 2026-08-08

Status: **FAIL (live proof unavailable)**. Configuration readiness and unit
coverage are recorded separately from live execution. No Ready state below is
promoted to Pass, and no 80% branch-coverage claim is made.

## Evidence obtained

- `environment_profile_spec.spl`: 9/9 examples passed.
- VirtIO input operation spec: 21/21 examples passed.
- ARM64 VirtIO input backend spec: 6/6 examples passed.
- Bounded DEVICE_CFG/shared-memory discovery spec: 17/17 examples passed,
  including device-lifetime receipt caching and reset invalidation.
- Existing capset spec after bounded-count/payload hardening: 38/38 examples
  passed. Its first run exposed three seed-incompatible optional-presence
  assertions; those assertions were corrected and the second run passed.
- Normalized GPU/Web differential trace and environment-profile spec: 11/11
  examples passed; this is test-contract evidence, not a live Mesa/QEMU run.
- Focused input log:
  `build/test-artifacts/simpleos_qemu_primitive_verify/input-unit.log`.
- A real defect was fixed: `EV_REL/REL_WHEEL` was accumulated but discarded
  when `SYN_REPORT` emitted `MouseEvent`. The event now carries the signed
  wheel value and clears it after the report.

## Live attempts and exact blockers

| Attempt | Phase reached | Result |
|---|---|---|
| Canonical host-GPU wrapper | compiler preflight | FAIL: selected `bin/simple` is identified as a Rust-built bootstrap seed |
| Diagnostic ARM64 host-GPU run | daemon native link | FAIL: undefined `rt_tls13_sha256` and `rt_sleep_nanos`; no guest/device execution |
| Canonical ARM64 QMP input run | image attestation | FAIL: canonical desktop disk/manifest absent; no boot or capture |
| Canonical x86 OVMF fullscreen run | kernel/source build | FAIL: `wm-simple-web-build-source-changed`; cache preserved; serial log 0 bytes |

The failures establish neither guest boot nor failure of the guest primitive
implementation. They prevent live evidence for event delivery, WM mutation,
DrawIR execution, Vulkan identity, device-origin readback, and correlated
capture.

## Branch/acceptance ledger

| Surface | Covered evidence | Remaining live or measured gap |
|---|---|---|
| QEMU input decode | PS/2 specs cover sync recovery, overflow/drop, sign handling; VirtIO specs cover valid aggregate, invalid type/device, pending-slot rejection, signed wheel gated by `SYN_REPORT` | real QEMU injection bytes to guest receipt |
| Button transitions | focused PS/2 and VirtIO unit transitions | QMP press/release correlated with guest WM state |
| Modifier sequences | Ctrl and Alt press/release focused backend spec | QMP keyboard sequence and canonical guest handler receipt |
| Guest event/WM handling | unit/backend acceptance only | booted guest, canonical handler state change, no synthetic dispatch |
| DrawIR accept/reject | existing codec/validation specs cover valid roundtrip plus malformed, oversize, corrupted, and resource rejection | booted guest `DrawIrComposition` execution receipt |
| Vulkan admission | bounded DEVICE_CFG/shmem/capset receipts plus protocol fallback/rejection specs | real guest device identity, submit/fence, device-origin readback, confirmed no CPU fallback |
| Capture change/no-change | contract shape exists | event/frame-correlated capture with checksum and targeted pixel change, plus no-change control |

This is a defensible branch ledger, not measured aggregate coverage. A numeric
percentage requires instrumentation on the exact selected guest build and is
therefore still missing.

## Architecture and implemented discovery slice

The pure-Simple chain is frozen in
`doc/04_architecture/simpleos_venus_gpu_stack.md`:

`GpuAccelerationProvider` -> `VirtioGpuDiscoveryProvider` -> `VenusSession`
-> command/fence/readback -> existing `VulkanCompositorBackend`.

The implemented discovery slice adds DEVICE_CFG/shared-memory PCI capability
constants, validates capability lengths/BAR containment/address overflow,
bounds PCI visits to 48, config-generation reads to three attempts, capsets to
64, and capset payloads to 4072 bytes, and emits a typed receipt. Even a
complete candidate receipt carries `vulkan_executed=false`,
`device_readback=false`, and `fallback_used=false`; its reason explicitly says
the candidate is unclassified.

The differential-conformance addendum freezes a generic normalized trace
schema, test-only comparator/environment profiles, and a future compiled
Mesa/Vulkan SFFI oracle. VUDA was absent from the tree/history and does not
match the provider/VirtIO/Venus ownership chain, so it is not migrated or
vendored.

Discovery alone remains `Ready`. Only real command submission, known fence
completion, device-origin readback, and same-frame capture correlation can
produce a Vulkan live Pass.
