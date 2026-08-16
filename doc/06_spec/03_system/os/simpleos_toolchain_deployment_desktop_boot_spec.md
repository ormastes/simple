# SimpleOS toolchain deployment and desktop boot

## Purpose

Prove that one admitted x86_64 SimpleOS deployment image boots through the
production OVMF/GRUB desktop path and uses its embedded Simple toolchain to
compile, link, and execute exact `Hello World` inside that same guest.

## Preconditions

- An admitted pure-Simple Stage 4 host CLI produced the target payload.
- `/SYS/SIMPLETOOL.SDN` and the external image-admission receipt validate.
- The image contains the canonical Simple aliases, genuine guest-static
  `ld.lld`, runtime inputs, linker script, and `/HELLO.SPL`.
- OVMF CODE, writable per-run VARS, GRUB EFI, QEMU, framebuffer capture, and
  SSH evidence are available.

Unavailable prerequisites are BLOCKED failures. There is no opt-in skip or
non-execution green path.

## Procedure

### Prepare the toolchain deployment image

Run `prepare_toolchain_deployment_fixture`, which executes
`scripts/check/check-simpleos-toolchain-desktop-boot.shs`. Then
`require_toolchain_deployment_manifest` validates the embedded component
manifest and closed-image admission receipt, including all canonical paths and
record hashes.

### Boot the SimpleOS production desktop

`require_simpleos_desktop_boot_receipt` requires the same-run receipt to bind
the admitted image/kernel to OVMF, per-run VARS, GRUB, exact QEMU argv,
`gui_entry_desktop.spl`, desktop/readiness/scanout markers, and framebuffer
evidence.

### Compile and run Hello World inside the guest

The production wrapper must record these guest commands in order:

```sh
/usr/bin/simple --version
/usr/bin/simple compile --emit-object /HELLO.SPL -o /HELLO.O
/usr/bin/ld.lld -flavor gnu --no-mmap-output-file -T /sysrt/simpleos.ld -nostdlib -static --gc-sections -o /HELLO.ELF /usr/lib/CRT0.O /usr/lib/SIMAIN.O /HELLO.O --start-group /usr/lib/SIMPRT.A /usr/lib/SOSLIB.A --end-group
/HELLO.ELF
```

`require_guest_hello_receipt` requires every rc to be zero, `/HELLO.ELF` to be
static ET_EXEC with no `PT_INTERP`, stdout to equal `Hello World`, stderr to be
empty, and the output to come from the mounted filesystem.

## Expected evidence

- `build/os/evidence/SIMPLETOOL.SDN`
- `build/os/evidence/simpleos-toolchain-image-admission-v1.sdn`
- `build/os/evidence/simpleos-toolchain-desktop-guest-v1.sdn`
- Same-run serial, SSH, framebuffer/readback, command, output, and ELF evidence

All records end in `record_sha256` over sorted canonical fields excluding that
field.

## Failure handling

The scenario fails on wrapper failure, missing/stale records, wrong schema or
status, absent component identity, missing desktop/framebuffer marker, altered
guest command, nonzero rc, wrong ELF identity, output mismatch, or absent
record hash. Rust seed, host compilation, `-kernel`, `isa-debug-exit`, marker
apps, fixed SSH responses, and historical artifacts are rejected.

## Requirement traceability

| Requirement | Executable owner | Evidence |
|---|---|---|
| REQ-SOS-TD-001 | prepare step | admitted producer and target payload identity |
| REQ-004 / REQ-SOS-TD-002 | manifest checker | embedded manifest and image receipt |
| REQ-SOS-TD-003 / NFR-005 | desktop checker | OVMF/GRUB/QEMU/desktop/framebuffer receipt |
| REQ-005 / REQ-007 | guest checker | exact commands, ELF, output, and rc |
| REQ-SOS-TD-004 | all helpers | frozen names, steps, and fail-closed behavior |

## Operator result

PASS is valid only when the executable scenario completes all three visible
steps. A failure naming `blocked:` is an honest incomplete production result,
not a skip.
