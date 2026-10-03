# Named QEMU lane projection

**Manual draft; current execution and SPipe generation TEST_BLOCKED.**
Source: `test/01_unit/os/qemu_named_nvme_plan_v1_spec.spl`.

Resolve catalog-owned named lanes, project controller/drive/namespace wiring,
and compare the sealed command with the established named-scenario command.
Both sides now read explicit guest memory and CPU values from the same owner.
Retain negative cases for unsupported shapes and invalid namespace wiring.

This document records intended executable coverage only. Named-scenario
production dispatch has not been migrated by the default-CLI slice. No real
QEMU boot, device operation or guest execution was performed. Use the exact
resume plan `doc/03_plan/sys_test/simpleos_sealed_cli_dispatch.md` and replace
this draft with reviewed complete/zero-stub SPipe output after admission.
