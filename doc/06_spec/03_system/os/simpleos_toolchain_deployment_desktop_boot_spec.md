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

Current source status (2026-08-16): the production wrapper and shared receipt
validator exist. Their 16-case hermetic self-test passes with
`platform_acceptance_claimed=false`; production mode uses the canonical
Stage-4 provenance verifier rather than path or marker-based admission.
Default live mode remains blocked because the canonical desktop owner has no
same-run network/SSHD guest-command hook, so the system scenario has no runtime
PASS.

**TEST_BLOCKED (2026-08-16):** no current-source, canonically admitted
pure-Simple CLI is available in this worktree or the registered worktrees.
Runtime execution, SPipe docgen, and `sspec-maintain scan` were therefore not
run. This Markdown is the reviewed mirrored manual for the future-executable
spec; it is not generated-runtime evidence and cannot promote the live gate.

## Procedure

### Validate the receipt contract without claiming platform acceptance

Run the production wrapper with `--self-test`. The scenario requires exit zero,
empty stderr, the exact PASS prefix, all 16 validator cases, and
`platform_acceptance_claimed=false`. This is positive host-fixture evidence
only; it does not claim a booted desktop or guest execution.

### Reject extra receipt self-test arguments

Run `--self-test unexpected`. The scenario requires usage exit 2, empty stdout,
and the canonical usage message. Accepting extra arguments would make the
evidence mode ambiguous and is an error.

### Reject production execution without an admitted runtime

Run production mode after explicitly removing `SIMPLE_BIN`,
`SIMPLEOS_TOOLCHAIN_IMAGE`, and `SIMPLEOS_STAGE4_ADMISSION_RECEIPT` from the
child environment. The scenario requires exit 1, empty stdout, and
`blocked:simple-bin-not-set`; a skip or non-execution PASS is forbidden.

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

| Requirement | Executable scenario/checker | Evidence |
|---|---|---|
| REQ-SOS-TD-001 | missing-runtime rejection; prepare step | fail-closed admission plus admitted producer and target payload identity |
| REQ-004 / REQ-SOS-TD-002 | receipt self-test; manifest checker | 16-case host-fixture contract plus embedded manifest and image receipt |
| REQ-SOS-TD-003 / NFR-005 | missing-runtime rejection; desktop checker | no unqualified production PASS; OVMF/GRUB/QEMU/desktop/framebuffer receipt when qualified |
| REQ-005 / REQ-007 | guest checker | exact commands, ELF, output, and rc |
| REQ-SOS-TD-004 | self-test boundary scenarios; all helpers | strict CLI surface, frozen names, visible steps, and fail-closed behavior |

## Static quality scorecard

- Four executable scenarios: one positive host-fixture path, one CLI edge, one
  admission error, and one full live-guest path.
- Every scenario has concrete built-in matcher assertions.
- The live scenario still calls the production owner and validates durable
  receipts; no source-string or test-only live oracle was added.
- Runtime, docgen, and all-seven-score maintenance status: `TEST_BLOCKED` until
  a canonically admitted pure-Simple CLI is available.

## Operator result

PASS is valid only when the executable scenario completes all three visible
steps. A failure naming `blocked:` is an honest incomplete production result,
not a skip.
