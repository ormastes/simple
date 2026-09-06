# rv32 NVMe fw: hand-assembled `_start` stub uses hard-float flags, mismatching the compiler's soft-float object

- **Date:** 2026-07-20
- **Status:** fix in flight (stub flags aligned to `rv32imac`/`ilp32`)
- **Severity:** medium (blocks the firmware link outright; latent since 2026-07-07)
- **Area:** `examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs`

## Symptom

```
ld.lld: error: build/test-artifacts/nvme_fw_rv32.o:
  cannot link object files with different floating-point ABI from
  build/test-artifacts/nvme_fw_rv32_start.o
```

`riscv64-unknown-elf-readelf -A` on the two objects meant to form one image:

| object | `Tag_RISCV_arch` | float |
|--------|------------------|-------|
| `nvme_fw_rv32.o` (compiler-emitted firmware) | `rv32i2p1_m2p0_a2p1_c2p0` | soft |
| `nvme_fw_rv32_start.o` (hand-assembled stub) | `rv32i..m..a..f2p2_d2p2_c..zicsr..` | hard |

## Which side is wrong: the stub

The compiler's soft-float emission is correct **by design**, and the stub is the
outlier:

- `src/compiler/70.backend/target_presets.spl:99-114` (`preset_riscv32_baremetal`)
  sets `arch: "riscv32imac"`, `abi: "ilp32"`, **`float_support: false`** —
  a deliberate MCU-class no-FPU target ("common: ESP32-C3, GD32VF103").
- `src/compiler/70.backend/backend/riscv_target.spl:92-107` derives march/ABI
  from those capability flags → `rv32imac`/`ilp32`, matching the emitted object
  exactly.
- `src/os/kernel/arch/riscv32/boot.spl:28` documents "rv32imac has the A
  extension"; nothing in the rv32 boot path touches `mstatus`/FS bits or any
  float register.

The stub alone was assembled `-march=rv32imafdc -mabi=ilp32d`.

## Origin (latent since 2026-07-07)

Through 2026-07-05 the fw build had only the OS-boot path and reused
`boot.spl`'s own proven `_start` — one object, so no cross-object ABI
constraint existed. Commit **`b1e9cafaf4c`** ("chore: sync remaining bootstrap
and nvme updates") introduced "direct mode" with a separate hand-written asm
stub carrying `-march=rv32imafdc -mabi=ilp32d`. That looks like copy/paste drift
from `examples/09_embedded/simpleos_nvme_fw/baremetal_rv32/build.shs`, a plain-C
build where those flags are legitimate **because it never links a
Simple-compiled object**.

The same commit also never linked libgcc, so the mismatch stayed dormant: it
only fires once the firmware actually references 64-bit `/` or `%`
(`__divdi3`/`__moddi3`), which is what happens now that the emit-object defects
(`19d868da3ace`, `de6c12922b64`) let the build reach the linker at all.

## Fix

Align the stub to what the compiler actually emits — `-march=rv32imac
-mabi=ilp32` — and select the ABI-matching libgcc for the soft-arithmetic
helpers. Do **not** merely relax `-mabi=ilp32d`→`ilp32` while keeping
`-march=...fdc`: that quiets the linker but leaves the arch attributes
disagreeing.

**`ld.lld`'s float-ABI check is a safety net, not a false positive.** The FPU is
never enabled on this platform (`mstatus.FS` is never set), so an object that
claims F/D support would let future float code through to fault on real silicon
with no diagnosis path. Keep the check able to fire.

Verified benign for the code as it stands: both stub variants contain zero F/D
instructions (pure integer/CSR/UART polling), so the flag change is
metadata-only and produces identical machine code.

## Follow-up (separate, lower urgency)

`_rv32_queue_next(index, depth)` — `(index + 1) % depth`,
`logic_queue_phase_core.spl:38` — is ring-buffer wraparound over an NVMe queue
depth (test uses 64; spec max ≤65535). The 64-bit division is almost certainly
an unintended consequence of Simple's default-int-is-i64 policy. Retyping it to
i32 would express the intent, remove one of the two libgcc dependencies, and
replace a software long-division call with a single native rv32 `REM`.

`_rv32_pt_next_temp` (`logic_power_thermal_core.spl:13`) is exercised with `ops`
up to ~2×10¹⁷, so its i64 division looks genuinely intended — confirm with the
thermal-model owner before touching it.

## Related

- `doc/08_tracking/bug/seed_emit_object_superlinear_hang_large_module_2026-07-20.md`
  (the SMP variant of this firmware still cannot be built at all)
