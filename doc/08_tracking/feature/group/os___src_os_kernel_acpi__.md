# os__(src/os/kernel/acpi/)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SIMPLEOS-ACPI-001"></a>FR-SIMPLEOS-ACPI-001 | ACPI table walker (RSDP → RSDT/XSDT → FADT + HPET) | SimpleOS needs real HPET MMIO base and PMTMR I/O port from ACPI tables so that TSC calibration can use sub-0.1% reference sources instead of PIT-ch2. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
