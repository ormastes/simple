# The `scripts/` reorg updated product source but left 34 test specs on pre-reorg paths — and the specs that "verify the script exists" were vacuous enough not to notice (2026-08-04)

**Status:** PARTIALLY FIXED — the `test/system/**` instances are repointed (see
below). 27 files in other tiers are untouched, and the vacuity finding is
unaddressed.
**Found:** 2026-08-04
**Class:** stale reference after a directory reorg + vacuous assertions that
concealed it.

## Symptom

13 scripts were moved into `scripts/{check,os,qemu,rtl,fpga,setup}/`
subdirectories. **Product source was updated; tests were not.**

```
scripts/check-riscv64-fpga-simpleos-preflight.shs -> scripts/check/check-riscv64-fpga-simpleos-preflight.shs
scripts/check-riscv-rtl-linux-smoke.shs           -> scripts/check/check-riscv-rtl-linux-smoke.shs
scripts/check-simpleos-arm64-wm-qemu-readiness.shs-> scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs
scripts/check-heavy-work-preflight.shs            -> scripts/check/check-heavy-work-preflight.shs
scripts/check-repo-hygiene.shs                    -> scripts/check/check-repo-hygiene.shs
scripts/check-live-kms-security-workflow.shs      -> scripts/check/check-live-kms-security-workflow.shs
scripts/install-mold.shs                          -> scripts/setup/install-mold.shs
scripts/jtag-ftdi-unbind.shs                      -> scripts/fpga/jtag-ftdi-unbind.shs
scripts/make_os_disk.shs                          -> scripts/os/make_os_disk.shs
scripts/qemu_rv{32,64}_http_test.shs              -> scripts/qemu/...
scripts/rtl_riscv{32,64}_linux_generated.shs      -> scripts/rtl/...
scripts/run_simpleos_{physical_nvme_perf,ra4m1,stm32u585}.shs -> scripts/os/...
```

Proof the product side is clean — every in-tree invocation already uses the new
path, e.g. `src/os/_QemuRunner/scenario_disks.spl:322,325,593,742` all call
`scripts/os/make_os_disk.shs`. **34 test spec files across 5 tiers still name
the old paths.**

## Root cause (what is PROVEN)

Two compounding defects.

**1. The reorg was not propagated to `test/`.** A spec that does
`read_file("scripts/check-heavy-work-preflight.shs")` on a moved script gets an
empty string, and every `contains` assertion in the file fails at once. All 20
strings asserted by `test/system/infra/heavy_work_preflight_spec.spl` were
verified individually to be present, unchanged, in
`scripts/check/check-heavy-work-preflight.shs` — nothing about the script's
content drifted, only its path.

**2. The specs that exist specifically to guard these scripts are vacuous, so
the move was invisible.** `test/system/hardware/riscv64_fpga/preflight_spec.spl:9-11`:

```
    it "preflight script exists":
        val path = "scripts/check-riscv64-fpga-simpleos-preflight.shs"
        val exists = path == "scripts/check-riscv64-fpga-simpleos-preflight.shs"
        expect(exists).to_equal(true)
```

`exists` compares a literal to itself — always true. The filesystem is never
touched. `jtag_unbind_spec.spl:8-22` is the same shape (`name.to_contain("jtag")`
on a string literal), and the file also contains `expect(true).to_equal(true)`.
These specs are **green right now while the script they claim to guard has
moved** — which is the proof of vacuity, not merely a suspicion.

**3. Diagnostics hide it.** 139 spec files across `test/system` and
`test/03_system` use `fn read_text(p) -> text: rt_file_read_text(p) ?? ""`. A
missing path is indistinguishable from an empty file, so a relocated script
surfaces as N opaque `expected false to equal true` lines rather than one
"file not found".

## Fixed in this lane (assertions unchanged, each verified individually)

- `test/system/infra/heavy_work_preflight_spec.spl` — 9 refs repointed to
  `scripts/check/`. All 20 asserted substrings confirmed present at the new path
  before the edit.
- `test/system/code_quality/live_kms_security_workflow_spec.spl` — `HYGIENE`
  constant repointed; the asserted invocation string updated to
  `scripts/check/check-live-kms-security-workflow.shs`, which is what
  `scripts/check/check-repo-hygiene.shs` actually contains today (verified).
- `test/system/compiler/rtl_mdsoc_byte_equal_spec.spl` — 2 "script exists"
  examples repointed to `scripts/rtl/`. The script-*running* examples sit behind
  a `pending()` baseline gate and were not affected.
- `test/system/os/port/alt_rootfs_disk_boot_spec.spl:74` — the `/bin/sh`
  invocation repointed to `scripts/os/make_os_disk.shs`, matching product source.

## Why the rest is not fixed now

- **27 files in other tiers** (`test/unit/os/*` ×8, `test/unit/hardware/*`,
  `test/01_unit/hardware/fpga_linux/*`, `test/integration/`,
  `test/03_system/{compiler,feature,hardware}/*`) are outside this lane's scope
  and are owned by the unit/integration lanes. The mapping table above is
  complete; the edit is mechanical once each asserted string is re-verified at
  the new path — do not sed blindly, see the next point.
- **`test/system/simpleos_riscv_network_gate_spec.spl` was deliberately left
  alone.** Its RV32 references would repoint cleanly (all 5 asserted strings
  present in `scripts/qemu/qemu_rv32_http_test.shs`), but 4 of the 10 strings it
  asserts of the RV64 script — `Build it first with an LLVM-enabled compiler`,
  `--source build/os/generated`, `--backend llvm`,
  `--target riscv64gc-unknown-none` — are **genuinely absent** from
  `scripts/qemu/qemu_rv64_http_test.shs`. That is real content drift, not a path
  problem, and repointing would half-fix the file while masking it.
- **`doc/07_guide/security/live_kms_security_gates.md` does not exist**, so the
  "operator guide" example in the live-KMS spec still fails for a real reason
  (missing doc), separate from the path fix.
- **The vacuous specs were not rewritten.** Turning
  `val exists = path == "<same literal>"` into a real `rt_file_exists` check
  would strengthen a currently-**passing** test; that is outside a
  make-failing-tests-pass lane and should not be done unilaterally in a tree with
  live parallel sessions. It should be done — the whole family is a false green.


## 2026-11-13 addendum — lane p3-io (work/p3-io-20261113): remaining test-tier repoints landed

The previously-deferred `test/` tiers were repointed in an isolated worktree
(off the shared dirty tree). Each asserted string was re-verified at the new
path before editing (no blind sed); the new script paths were confirmed present
on disk first. Status: **PARTIALLY FIXED → further reduced**; the vacuity
finding is still open by design.

- `test/system/code_quality/live_kms_security_workflow_spec.spl:121,131` —
  guide + hygiene `contains` assertions repointed to
  `scripts/check/check-live-kms-security-workflow.shs` (both underlying files
  already use the new spelling; spec was a false-RED). Now 7/7.
- `test/01_unit/os/memory/mold_linker_spec.spl` — removed the stale duplicate
  `it "scripts/install-mold.shs exists"` block (89-92); the new-path block
  (84-87) already covered `scripts/setup/install-mold.shs`. Now 14/14.
- `test/02_integration/http_baremetal_spec.spl:89,95` — repointed to
  `scripts/qemu/qemu_rv64_http_test.shs`. The two repointed examples now pass.
  Three other examples still fail on **genuine content drift** in
  `qemu_rv64_http_test.shs` (HTTP-only / packet RX-TX markers), not a path
  problem — left RED rather than masked, per this record's own rule.
- `test/03_system/compiler/rtl_mdsoc_byte_equal_spec.spl:31,110` — repointed to
  `scripts/rtl/rtl_riscv32_linux_generated.shs` (docstring + live call).
- `test/system/os/port/dbfs_disk_boot_spec.spl:153` and
  `test/system/simpleos_x86_32_boot_probe_live_spec.spl:118` — `make_os_disk.shs`
  invocations repointed to `scripts/os/make_os_disk.shs`.
- `test/system/simpleos_riscv_network_gate_spec.spl:276` — the RV32 deferred
  contract repointed to `scripts/qemu/qemu_rv32_http_test.shs` (clean, per this
  record). The RV64 references in the same file were already repointed; their
  residual content-drift failures are unchanged and out of scope here.
- `test/system/gui/arm64_wm_qemu_contract_spec.spl` — readiness script
  repointed to `scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs`
  (helper + guide assertion), and `_guide_path()` corrected to the real
  `doc/07_guide/platform/simpleos/simpleos_arm64_wm_qemu.md` (was missing the
  `simpleos/` subdir). Readiness probe still needs live QEMU hardware.
- `test/system/hardware/riscv64_fpga/preflight_spec.spl:12-13` and
  `test/system/hardware/riscv64_fpga/jtag_unbind_spec.spl:12` — path strings
  repointed (still vacuous; strengthening deliberately deferred as below).
- **Product fix:** `scripts/check/check-riscv64-fpga-simpleos-preflight.shs:96`
  advertised the pre-reorg `sh scripts/jtag-ftdi-unbind.shs`; corrected to
  `scripts/fpga/jtag-ftdi-unbind.shs`. The `test/03_system/.../jtag_unbind_spec.spl`
  assertion was strengthened to pin the corrected command (12/12).

Still open: `test/01_unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.spl`
reads `scripts/mlk_s02_100t_generated_linux.shs`, which **does not exist anywhere
in the tree** (not a reorg path issue — the wrapper is an un-generated/missing
fixture), so it cannot be repaired by repointing; needs the wrapper generated or
the spec's expectation re-scoped. The whole vacuous-spec family (literal ==
literal, `to_start_with` on a literal) remains a tracked false-green follow-up.

---

## Lane disposition 2026-11-13 (live-p3-l4, work/live-p3-l4-20261113, base f790f7f266e)

Concurs with the p3-io same-day addendum: path repoints across the deferred tiers landed (live_kms 7/7, mold_linker 14/14, http_baremetal's two repointed examples, rtl_mdsoc, dbfs/x86_32 make_os_disk, riscv_network_gate RV32 contract, arm64_wm_qemu, preflight/jtag_unbind with the product-side preflight script fix). The remaining open item — `test/01_unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.spl` reads `scripts/mlk_s02_100t_generated_linux.shs`, which does not exist anywhere in the tree (an un-generated/missing fixture, not a reorg path) — cannot be repaired by repointing; needs the wrapper generated or the spec re-scoped by the owner. The vacuous-spec family (literal == literal) remains a tracked false-green follow-up by design. No in-lane change. Owner: fpga/hardware fixture lane for the missing wrapper.
