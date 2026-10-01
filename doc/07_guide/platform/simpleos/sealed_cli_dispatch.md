# Inspect and run the default SimpleOS QEMU lane

The source implementation routes default non-debug `simple os run --arch=...`
through the same catalog, host settings, image hash and sealed plan used by
`--show-plan` and `--print-command`. The process provider receives the sealed
executable and argv directly. Printed POSIX quoting or Windows display text
is never executed as a shell command.

This change is **not yet admitted in a shipped binary**. Self-hosted execution
and live QEMU qualification are blocked; see the
[resume plan](../../../03_plan/sys_test/simpleos_sealed_cli_dispatch.md).

Once a rebuilt binary is admitted, inspect the existing built image with
`simple os run --arch=x86_64 --show-plan`, then use
`simple os run --arch=x86_64` to build and run. Inspection does not build or
launch. A changed image is hashed and planned again at run time; inspection
does not reserve an immutable release candidate.

The default lane preserves artifact admission, a 30-second bounded run,
serial/stderr reporting and target-specific exit handling. Missing settings,
media or executable identity, rejected plans and invalid seals fail closed.
TCG remains the current parity-plan execution domain; this does not qualify
native acceleration or performance. Host-provided QEMU overrides must resolve
to the same executable admitted by the inspection policy.

`SIMPLEOS_QEMU_MEM` and `SIMPLEOS_QEMU_CPUS` retain explicit guest resource
choices in both inspection and execution; absent a CPU override, the existing
ten-core default remains. Memory accepts MiB values with optional `M`, or GiB
with `G`; the plan bounds memory to 16..1048576 MiB and CPUs to 1..4096.
These choices do not add target code-generation ISA features.

Four named CLI scenarios also select sealed dispatch:
`x86_64-q35-pure-nvme-perf`, `x86_32-initrd-fat32-smf`,
`riscv64-virtio-fat32-smf`, and `riscv32-virtio-fat32-smf`. Their existing
media preparation and filesystem admission run before plan preparation.
Inspection and execution use the same named-plan owner, with the existing
scenario timeout and exit classification. A preparation or dispatch refusal
never falls back to legacy execution. This is source integration only; in
particular the x86_32 executable-policy refusal remains fail closed.

Other named scenarios and GUI/debug launches retain their existing runner paths.
Interactive shell and bootstrap remain unavailable for execution; their
inspection surfaces are not guest execution evidence. No release promotion
or whole-platform completion follows from this scoped cutover.

OS builds now resolve explicit `SIMPLE_BINARY`, then its `SIMPLE_BIN` alias,
through canonical pure-Simple provenance admission. Invalid explicit identity
fails closed. With no override, canonical release-runtime discovery owns the
choice; installed bootstrap seeds are not implicit tooling candidates. LLVM
capability still requires the existing real compile-and-execute canary.

The live CLI-route acceptance spec requires existing real kernels/media and
QEMU plus `SIMPLE_QEMU_CLI_ACCEPTANCE_BIN` pointing to a canonical full Stage4
candidate. It invokes the actual CLI and records host process results, then
checks captured guest serial output separately. Its draft manual is
`doc/06_spec/03_system/os/feature/qemu_sealed_cli_route_acceptance_spec.md`.
Neither that spec nor its Linux/Windows lanes has executed yet.
