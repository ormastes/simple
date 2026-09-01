<!-- codex-design -->
# System-test contract: real filesystem program execution

## Acceptance target

Prove that x86_32, ARM32, RISC-V 32, and RISC-V 64 each read a target ELF from the mounted guest filesystem, execute its target instructions in a scheduler-owned user task, capture its stdout, observe exit code `37`, and reap that exact task generation. This contract covers REQ-SQ-006, REQ-SQ-007, REQ-SQ-009, REQ-SQ-011, REQ-SQ-017 and NFR-SQ-003/005/007/009.

Planned executable spec: `test/03_system/os/qemu/sys_qemu_real_fs_program_exec_spec.spl`. Planned manual: `doc/06_spec/03_system/os/qemu/sys_qemu_real_fs_program_exec_spec.md`. Both remain implementation work; this design task creates no executable scaffold and no synthetic PASS.

## Frozen scenario vocabulary

- `step("Stage the target ELF and retain its image readback identity")`
- `step("Boot one bounded guest execution lane")`
- `step("Observe target stdout and reaped exit status")`
- `step("Reject substituted bytes and synthetic lifecycle evidence")`

Planned setup helper: `prepare_real_fs_exec_case(arch, nonce)`. Planned checker: `check_real_fs_exec_receipt(arch, nonce, expected_hash, serial, receipt)`. Until backed by independent artifacts, the checker must fail with `fail("UNRESOLVED ORACLE: real filesystem program execution")`.

## Positive matrix

For each `arch` in `x86_32`, `arm32`, `riscv32`, and `riscv64`, choose a fresh 16–128 character nonce and require all of:

- retained source/compiler/ELF/image identities and post-image readback hash;
- guest filesystem identity plus exact path `/sys/apps/fs_exec_probe.elf`;
- guest-computed ELF hash equal to the retained readback hash;
- correct ELF class, little-endian encoding, machine, nonzero entry, and at least one executable load segment;
- positive scheduler task ID plus nonzero generation, user-mode-start event, exit event, and reap event in strict sequence;
- exact stdout `SIMPLEOS_FS_EXEC_OK arch=<arch> nonce=<nonce>\n` and its independently computed SHA-256;
- `exit_kind=exited`, `exit_rc=37`, no fault, no timeout, no truncation;
- final `FS_PROGRAM_EXEC_RESULT status=pass` line agreeing with every retained field.

The host test has a 180-second per-guest timeout and a 900-second outer worker bound. Missing prerequisites remain BLOCKED and cannot be counted as PASS.

## Negative controls

Each control must fail before a PASS receipt can be emitted:

1. Flip one payload byte after the retained ELF hash: `payload-hash-mismatch`.
2. Stage an ELF for another machine: `elf-machine-mismatch`.
3. Corrupt a program-header range or create W+X overlap: `elf-mapping-invalid`.
4. Reuse a prior nonce or task generation: `stale-execution-identity`.
5. Supply only an ELF parse marker or a positive PID without start/exit/reap: `lifecycle-incomplete`.
6. Inject the expected stdout from the kernel/probe rather than the authenticated child write event: `stdout-producer-mismatch`.
7. Return zero or omit the exit event: `exit-code-mismatch` or `lifecycle-incomplete`.
8. Exceed the stdout bound, fault, or exceed the deadline: `stdout-overflow`, `user-fault`, or `execution-timeout`.
9. Route through a current compatibility/synthetic spawn function: static ownership gate fails with `forbidden-synthetic-exec-path`.

## Independent oracle and evidence

Before boot, a host ELF inspector and SHA-256 tool record target metadata and bytes independently of the guest implementation. After boot, the checker parses the structured serial lifecycle, recomputes the stdout hash, and compares it with both the exact expected text and final receipt. The image readback artifact, serial transcript, exact QEMU argv, nonce, source identity, and checker result are retained together.

Source grep is only a negative ownership gate; it cannot prove execution. Existing `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, hard-coded PID, or `spawn:prepared` markers are explicitly insufficient.

## Requirement traceability

| Requirement | Scenario evidence |
|---|---|
| REQ-SQ-006 | guest filesystem identity, canonical path, readback hash |
| REQ-SQ-007 | authenticated stdout plus exit/reap lifecycle |
| REQ-SQ-009 | one shared spec/checker over four ISA rows |
| REQ-SQ-011/017 | nonce, exact hashes, argv, source identity, fail-closed receipt |
| NFR-SQ-003/005 | explicit blocked/failed reasons and bounded deadlines |
| NFR-SQ-007 | independent ELF/hash/stdout oracle plus nine sabotage controls |
| NFR-SQ-009 | versioned deterministic request/result and receipt schema |

## Ownership

Implementation owner: SimpleOS loader/process integration lane. Evidence owner: SOSIX QEMU matrix lane. Merge owner: SOSIX parallel-QEMU coordinator. Final reviewer: best available normal/highest-capability reviewer. Sidecar lanes: N/A for this narrow boundary design.

## Current gate status (2026-08-12)

| Guest | Static/simulator gate | Live QEMU gate | Status |
|---|---|---|---|
| ARM64 | `arm64_user_exit_return_contract_spec.spl`: **PASS 10/10** | not run after real mounted-payload change | **PARTIAL — live pending** |
| RV64 | mounted-byte nonce admission, canonical VFS wiring, supervisor return and exact-child reap restored; source/static and C syntax pass | not run | **PARTIAL — production/live pending** |
| x86_32 | real i386 ELF32 payload gate **PASS**; focused ownership spec timed out at the existing 120-second daemon-worker bound before examples executed | not run; CPL3 owner absent | **PARTIAL — live blocked, spec timeout** |
| ARM32 | authenticated user-transition/vector/SVC-return, mounted staging, exact-child reap, canonical entry, and FAT listing source/static gates pass | not run | **PARTIAL — production/live pending** |
| RV32 | pure ELF32 builder/simulator and exact mounted-byte gate diagnostic **PASS 4/4**; gate returns `-95` because saved-frame entry is absent | not run | **PARTIAL — live blocked** |

RV64 production-runtime confirmation command (the bootstrap-seed diagnostic is already green and must not be relabeled production evidence):

```bash
SIMPLE_LIB=src bin/simple test test/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.spl --mode=interpreter
```

ARM64 and RV64 live commands must be selected from the canonical matrix wrapper in a fresh bounded session; this plan records no live PASS until their transcripts contain the mounted identity, exact nonce stdout, exit `37`, and reap evidence. Existing `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, positive PID, or kernel-printed substitute output cannot satisfy this contract.

x86_32 resumes only after an architecture owner installs GDT/TSS CPL3 state, maps the selected ELF32 PT_LOADs and user stack, enters with `iret`, authenticates bounded syscall-60 user memory, and returns/reaps syscall-0 status without a fixed-PID shortcut. RV32 resumes only after the analogous Sv32 saved-frame entry/trap-return owner replaces `rv32-sv32-live-entry-not-installed`. ARM32's source owners are now implemented; it resumes with a production compiler build and one bounded QEMU run proving the mounted identity, target stdout, exit 37, supervisor return, and reap. Static payload/simulator gates remain development evidence, never live PASS.
