# SimpleOS RV64 WM Live Framebuffer Gate Missing

- status: resolved-for-freestanding-wm-gate
- gate: `scripts/check/check-simpleos-host-configuration-matrix.shs`
- failing field: `simpleos_host_configuration_qemu_riscv64_wm_live_status=missing`
- latest probe: `timeout 20s qemu-system-riscv64 -machine virt -cpu rv64 -m 256M -nographic -bios default -no-reboot -kernel build/os/simpleos_riscv64_smf_fs.elf`
- latest result: current RV64 SMF FS serial smoke exits `status=0` and proves SMF GUI launch markers; QMP/framebuffer capture is still missing

The SimpleOS hardening matrix now separates RV64 network evidence from live WM
framebuffer evidence. Current evidence proves RV64 SSH/web/DB QEMU networking
and x86_64 SimpleOS WM QMP framebuffer capture, but not an RV64 SimpleOS WM
framebuffer capture.

Before the WM framebuffer gate can close, the RV64 native-build path must emit
a boot ELF whose entry symbols are sane, then the RV64 QEMU boot path must
advance past the banner loop into `riscv_noalloc_log_init`, service probes, and
`Display service ready: 320x240 framebuffer`.

Fresh `bin/simple os build --arch=riscv64` now produces
`build/os/simpleos_riscv64_smf_fs.elf` for the smoke/SMF FS lane with sane
entry symbols and a real QEMU success exit. Direct serial QEMU smoke returns
`status=0` and reaches `SIMPLEOS_RISCV_SMF_FS_PASS`, but this is not live
framebuffer evidence. The HTTP/display gate still defaults to
`build/os/simpleos_riscv64.elf`, so the display-entry boot ELF and capture path
remain the blocker.

`bin/simple os build --scenario=riscv64-smoke` now reaches the correct full
`src/os/kernel/arch/riscv64/boot.spl` native-build command for
`build/os/simpleos_riscv64.elf`, but the current probe hit a 240s outer timeout
before producing the ELF. The next blocker is therefore full RV64 `boot.spl`
native-build completion, not scenario routing.

`bin/simple os build --scenario=riscv64-display-smoke` is now the smaller
framebuffer bring-up target. It routes to
`examples/09_embedded/simple_os/arch/riscv64/display_entry.spl`, calls the
RV64 display runtime directly, and idles for QMP capture through the C runtime.
Current evidence: the display-smoke native-build now uses the narrowed
freestanding profile, emits `build/os/simpleos_riscv64_display_smoke.elf`,
boots to `SIMPLEOS_RISCV_DISPLAY_SMOKE_READY`, and QMP `screendump` captured a
nonblack 320x240 PPM at `build/os/rv64_display_smoke_evidence/screendump.ppm`.
The canonical wrapper
`scripts/check/check-rv64-display-smoke-qmp-evidence.shs` now also requires
the RV64 freestanding WM lifecycle serial markers and five deterministic QMP
anchor pixels. The host matrix reports
`simpleos_host_configuration_qemu_riscv64_wm_live_status=pass`.

Acceptance for closing:
- RV64 QEMU scenario boots a SimpleOS WM/display entry. PASS:
  `riscv64-display-smoke`.
- QMP or equivalent capture proves a nonblank framebuffer. PASS:
  `rv64_display_smoke_qmp_nonblack=76800`.
- Capture validates WM anchors comparable to the current MDI gate. PASS:
  `rv64_display_smoke_qmp_wm_anchor_matches=5`.
- `check-simpleos-host-configuration-matrix.shs` reports
  `qemu_riscv64_wm_live: pass`. PASS.
