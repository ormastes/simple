# riscv

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-RISCV-HAL-PROD-WIRING-2026-05-02"></a>FR-RISCV-HAL-PROD-WIRING-2026-05-02 | FR-RISCV-HAL-PROD-WIRING-2026-05-02: Wire Real Production Bodies for HalSmp/HalCache | **Status: IMPLEMENTED (2026-05-10)** — AC-1 and AC-2 production bodies wired. AC-3 (PortableNumericCapabilities write-back) remains a follow-up; AC-1/AC-2 gaps are closed. **AC-1 (HalSmp):** `hal_smp_ipi_send` and `hal_smp_ipi_broadcast` no | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-RISCV-TP-INIT-2026-05-02"></a>FR-RISCV-TP-INIT-2026-05-02 | FR-RISCV-TP-INIT-2026-05-02: Wire tp Register at Baremetal Boot for Per-CPU Base | **Status:** Implemented (2026-05-10) ## Why AC-4 of `riscv_smp_cache_hal_phase1` requires that each hart writes its per-CPU base address into the `tp` (thread pointer / x4) register before entering the kernel entry point.  The production he | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
