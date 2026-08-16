# System-test plan: SimpleOS filesystem toolchain and servers

1. `step("Boot SimpleOS with the server image")` and retain image/build hashes.
2. `step("Send a real guest service request")`: HTTP health/document responses.
3. Run the DB image: create table, insert `codex-41`, select, assert `codex-41`.
4. `step("Launch the tool from the mounted filesystem")`: Clang and Simple
   version/provenance, with no `spawn:preloaded` marker.
5. `step("Compile and run hello world in the guest")`: C and Simple outputs,
   mounted output ELFs, ring-3 output, and exit status.
6. Negative cases: fake/tiny payload, corrupt ELF, wrong target, short range
   read, missing file, stale image, malformed query, timeout.

All scenarios fail closed; no `skip`, readiness-only marker, or host compile is
accepted as requirement evidence.
## Restart12 deployment SSpec addendum (2026-08-14)

The exact executable target is
`test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl`; its
Markdown operator manual is
`doc/06_spec/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.md`.
The executable and operator manual are implemented with the frozen
steps/checkers and REQ-SOS-TD-001..004 traceability. They fail closed through
the canonical production wrapper path. Execution, pure-Simple docgen, and the
all-seven-score `sspec-maintain` review remain blocked on the Stage-4 runner and
live B-DESKTOP prerequisites. Zero stubs and zero executable specs under
`doc/06_spec` remain required by
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.
