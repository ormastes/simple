<!-- codex-design -->
# Compiler-filesystem live QEMU guest adapter plan

## Scope and acceptance boundary

Wire only the existing `x86_64-compiler-filesystem`,
`arm64-compiler-filesystem`, and `riscv64-compiler-filesystem` scenarios. A live
PASS must originate in the guest after it reads the attached filesystem and
executes the observed processes. Host image inspection, a fixture runner,
presence probes, construction receipts, and boot markers remain non-evidence.
No bootstrap step belongs to this plan.

The final authority chain is singular:

`QEMU fw_cfg + mounted VFS + scheduler observations -> one guest observation ->
compiler_filesystem_guest_workflow_v2 -> serial protocol -> existing host
receipt parser`.

No architecture adapter may format a protocol PASS, and the host must not hash
guest files or synthesize process observations.

## Required compatibility-preserving validator change

The current `SimpleOsCfsGuestEvidenceV2` stores every executable alias as
`[u8]`; it therefore cannot validate a real compiler under a 64 KiB memory
bound. Extend
`src/os/port/init/compiler_filesystem_guest_workflow_v2.spl` with a canonical
`SimpleOsCfsGuestObservationV2` whose file records contain path, exact byte
count, and SHA-256 produced from the execute-open/read snapshot. Retain
`simpleos_cfs_validate_guest_evidence_v2` as a small-fixture compatibility
wrapper that hashes its byte arrays once and delegates to the new
`simpleos_cfs_validate_guest_observation_v2`. The canonical validator must not
re-read or re-hash bytes.

Add `simpleos_cfs_validate_and_project_guest_observation_v2(observation,
sink) -> SimpleOsCfsGuestWorkflowResultV2` for production. It validates fully
before writing, then projects the same fields through the bounded synchronous
sink without retaining rendered lines. The compatibility API continues to
return its existing `[text]` for unit callers and must be golden-byte-identical
to the sink projection.

Exact stdout needed for `--version` and hello matching stays bounded in the
observation (64 KiB per stream, with a required `truncated == false`). Source
and artifact records carry digest and size; source hello text may additionally
be compared while streaming. This preserves the existing serial protocol and
host parser API.

## Minimal implementation topology

1. Add `src/os/port/init/compiler_filesystem_guest_adapter_v2.spl` as the sole
   workflow owner. It accepts validated metadata plus three capabilities:
   snapshot-open/read, authenticated process launch/reap, and serial sink. It
   performs the fixed ordered role reads, `/HELLO.SPL` read, four exact launches,
   and `/TMP/HELLO` reread; then calls
   `simpleos_cfs_validate_and_project_guest_observation_v2` once. The sink is
   untouched unless validation succeeds.
2. First add the missing backend-neutral snapshot primitive to
   `src/lib/nogc_async_mut/fs_driver/mount_table.spl`:
   `open_snapshot(path: text) -> Result<ExecuteOpenBinding, FsError>` and
   `snapshot_read_into(binding: ExecuteOpenBinding, offset: u64,
   scratch: [u8]) -> Result<i64, FsError>`. The binding has the existing
   mount/file handle, size, mount/namespace/content generations and backend
   name, but does not require execute permission. `snapshot_read_into` rejects
   a stale generation and fills caller storage without creating a `text` or a
   second array. Add matching exhaustive dispatch in
   `mount_driver_dispatch.spl` and implement parity for `Fat32`, `DbFs`, and
   `Nvfs`; a backend without stable handles returns `Unsupported`, never a
   path-based fallback. `close(binding.file_handle)` releases the snapshot.
   The existing text-returning `MountTable.pread` is not sufficient.
3. Add `src/os/services/vfs/compiler_filesystem_observation_v2.spl`. It owns
   exactly one 65,536-byte scratch buffer, opens one stable snapshot per path,
   streams monotonically into one incremental SHA-256 state, checks observed
   count against `binding.size`, then closes before opening the next path.
   Alias equality is digest+size equality. Never call
   `g_vfs_read_file_bytes` for executable/source/artifact evidence.
4. Extend, rather than duplicate,
   `src/os/kernel/loader/guest_toolchain_execution_authority.spl` and
   `guest_toolchain_execution_contract.spl`. Add an immutable
   `GuestToolchainCommandV2(program: text, argv: [text], input_sha256: text,
   output_path: text)` and issue/consume APIs whose signatures are identical
   across architectures:
   `guest_toolchain_command_issue_v2(owner, expected, scheduler_token) ->
   Result<GuestToolchainCommandTokenV2, GuestToolchainHelloAuthorityErrorV1>`
   and `guest_toolchain_command_consume_once_v2(owner, token) ->
   Result<ProcessExecutionResultV2, ...>`.

   The four immutable commands are exactly:
   `/usr/bin/simple ["--version"]`,
   `/usr/bin/simple ["/HELLO.SPL"]`,
   `/usr/bin/simple ["compile", "--native", "/HELLO.SPL", "-o",
   "/TMP/HELLO"]`, and `/TMP/HELLO []`. `ProcessExecutionResultV2` adds exact
   argv, stderr/stdout truncation bits, execute-open mount/file generations,
   and output identity. The expected command is never accepted as the actual
   command. Extend `fs_exec_adopt_authenticated_with_launch_v1` and its
   scheduler-owned prepared/observation record so the owner copies the actual
   executable path and immutable argv at adoption time, before the child is
   runnable. Reap seals that same record; the evidence token exposes it only
   through one-time consumption. `guest_toolchain_command_issue_v2` compares
   the expected command to this owner-captured actual path+argv. No adapter,
   architecture bridge, or caller-supplied post-run value can populate or
   replace the actual command.

   The cross-arch loader signature is
   `*_fs_exec_spawn_authenticated_observed_v2(scheduler, table, authorities,
   token, consumer, entry_point, caller, path, argv, envp, recipe,
   expected_command) -> Result<SchedulerExecutionEvidenceTokenV1, i64>` for
   x86_64, ARM64, and RV64. All three bind bounded capture before handoff, exit
   and reap the exact child once, and return the scheduler token. Here
   `expected_command` is used only for the final owner-observation comparison;
   adoption records `path` and `argv` independently. Path-only and RV64 legacy
   capture functions are forbidden here.
5. Admit the newly compiled `/TMP/HELLO` as a derived artifact, not as trusted
   merely because compilation exited zero. The compiler child receives only
   `FileRead("/HELLO.SPL")`, `FileCreate("/TMP/HELLO")`, and
   `FileWrite("/TMP/HELLO")` in addition to execute/read authority for the
   admitted compiler. `/TMP` must resolve to the same writable, non-`noexec`
   mounted filesystem recorded by the compile observation. After child exit,
   `fsync`, close, reopen through `open_snapshot`, stream/hash once, and require
   unchanged mount/file/content generations. Extend
   `guest_toolchain_execution_authority.spl` with
   `guest_toolchain_derived_artifact_issue_v2(owner, compile_token,
   snapshot_binding, digest, size) ->
   Result<GuestToolchainDerivedExecutableBundleV2, ...>`; only this loader-owned
   transform may authorize `FileExec("/TMP/HELLO")`.
   It binds admitted compiler digest, exact argv, source digest, output path,
   writable mount identity/generation, artifact digest/size, and one-use nonce.
   The opaque bundle retains, under one loader owner, the live
   `ExecutableAuthorityRegistryV1`, its `ExecutableAuthorityTokenV1`, the
   `ExecutableLoadConsumerV1`, parsed `entry_point`, and validated load recipe,
   all derived from that same still-open stable snapshot. Its only consumer is
   `guest_toolchain_derived_artifact_launch_once_v2(bundle, scheduler, argv,
   envp) -> Result<SchedulerExecutionEvidenceTokenV1, i64>`, which requires
   `argv == ["/TMP/HELLO"]`, consumes the token once through
   `fs_exec_adopt_authenticated_with_launch_v1`, and closes the snapshot and
   releases the retained registry on every terminal edge. The bundle cannot be
   decomposed or copied. No unsigned general-purpose trust root or
   `ExecuteTrust.Trusted` shortcut is introduced.
6. Add three thin boot entries:
   `examples/09_embedded/simple_os/arch/x86_64/compiler_filesystem_entry.spl`,
   `examples/09_embedded/simple_os/arch/arm64/compiler_filesystem_entry.spl`,
   and
   `examples/09_embedded/simple_os/arch/riscv64/compiler_filesystem_entry.spl`.
   Each initializes the production block/VFS mount, calls only its existing
   architecture-local metadata source, constructs the common adapter with the
   production VFS/loader/serial owners, runs it once, and exits QEMU nonzero on
   every failure. Architecture differences end at metadata, boot, and user-mode
   handoff.
7. Introduce exact constructors and leave the existing acceptance targets
   untouched:
   `get_x86_64_compiler_filesystem_target()` in `runner_targets.spl`, and
   `get_arm64_compiler_filesystem_target()` plus
   `get_riscv64_compiler_filesystem_target()` in `scenario_disks.spl`.
   `scenario_x86_64_compiler_filesystem`,
   `scenario_arm64_compiler_filesystem`, and
   `scenario_riscv64_compiler_filesystem` in `scenario_catalog.spl` call those
   exact constructors. Their tuples are respectively:
   x86_64 entry `arch/x86_64/compiler_filesystem_entry.spl`, linker
   `arch/x86_64/linker.ld`, kernel triple `x86_64-unknown-none`, output
   `build/os/simpleos_x86_64_compiler_filesystem.elf`;
   ARM64 entry `arch/arm64/compiler_filesystem_entry.spl`, linker
   `arch/arm64/fs_exec_linker.ld`, triple `aarch64-unknown-none`, output
   `build/os/simpleos_arm64_compiler_filesystem.elf`; RV64 entry
   `arch/riscv64/compiler_filesystem_entry.spl`, linker
   `arch/riscv64/linker.ld`, triple `riscv64-unknown-none`, output
   `build/os/simpleos_riscv64_compiler_filesystem.elf`. QEMU machine/CPU,
   firmware, memory, and disk attachment are copied from each current fs-exec
   target. Guest executable manifests use the separate canonical userland
   triples `x86_64-unknown-simpleos`, `aarch64-unknown-simpleos`, and
   `riscv64gc-unknown-simpleos`.
8. In `src/os/_QemuRunner/scenario_exec.spl`, replace the print-and-false gate
   with a structural predicate over the selected `OsTarget`: exact entry,
   linker, output, one `cfsexecns1` disk, and the four fw_cfg arguments must all
   match. In the checker, readiness is not a mutable constant or source grep:
   invoke `bin/simple os scenario-contract --scenario=<name>` and require its
   machine-readable target-closure result `compiler_filesystem_adapter_v2=1`.
   That result is produced by build graph reachability of the adapter export;
   a missing runtime call still fails the serial parser and cannot publish.
   In `scripts/check/check-simpleos-compiler-filesystem-qemu.shs`, replace
   `GUEST_WORKFLOW_READY=0` with that structural command result, then keep the
   existing QEMU invocation and receipt publication unchanged. The serial
   log remains the one observation projected through the existing parser,
   manifest, and receipt gates.

## Complexity, allocation, and locality constraints

- One ordered pass per file: `O(total observed bytes)` time and bounded owned
  storage; no alias rereads for hashing.
- Reuse one chunk buffer and one SHA state serially. Hoist role paths and exact
  argv plans outside byte loops. No per-byte text concatenation or virtual
  dispatch inside chunk hashing.
- The one memory acceptance gate, used by design, implementation, unit tests,
  and QEMU diagnostics, is **guest-owned evidence capacity <= 147,456 bytes
  (144 KiB)**. The worst simultaneous phase is bounded by 65,536 stdout +
  65,536 stderr + 4,096 fixed observation/path records + 256 incremental hash
  state + 4,096 serial streaming chunk + 2,048 owner/token metadata = 141,568
  bytes, leaving 5,888 bytes of allocator/alignment margin. The 65,536-byte
  file-read scratch is released before process capture begins and therefore is
  not additive. Runs are sequential. Only version stdout may be retained at
  65,536 bytes; its stderr is released before the next run. Interpret and final
  hello capture at most expected-length+1 bytes, while compile captures one
  byte per stream to prove emptiness, so retained version output never overlaps
  another pair of 65,536-byte streams. Non-required outputs are reduced and
  released immediately. Every snapshot, scheduler token, stream buffer, and
  sink chunk has one owner and is closed/consumed/cleared on success and every
  error edge.
- Protocol projection is byte-compatible v2: the validator returns exactly the
  existing 20 lines, in the existing order and field order, with no added PASS
  fields. Production projection uses a synchronous bounded serial sink: it
  streams hex directly from retained bytes through the one 4,096-byte sink
  chunk and never constructs a full hex `text`, a 20-line array, or a second
  serial buffer. The existing line-returning validator remains fixture-only;
  production and fixture outputs have byte-for-byte golden parity. Optional
  diagnostics use the reserved prefix
  `SIMPLEOS_COMPILER_FS_DIAG_V2 `, occur only after the PASS line, never contain
  `status=`, `PASS`, `FAIL`, or `SKIP`, and are ignored by the v2 receipt parser.
  Timing and `peak_evidence_bytes` are diagnostic-only and cannot satisfy an
  acceptance gate.

## Tests and release evidence

- Extend
  `test/01_unit/os/port/compiler_filesystem_guest_workflow_v2_spec.spl` for
  digest-record validation, size mismatch, truncation, wrong argv/order,
  alias mismatch, and compatibility-wrapper parity. Include a synthetic file
  larger than 64 KiB through the streaming reader test without retaining it.
- Add
  `test/01_unit/os/services/vfs/compiler_filesystem_observation_v2_spec.spl`
  with short reads, exact 64 KiB boundary, multi-chunk reads, overflow,
  snapshot-generation change, read error, and close-on-failure cases.
- Add
  `test/02_integration/os/guest_toolchain_command_authority_v2_spec.spl`
  proving exact four-command order, authenticated token consumption once,
  adoption-time actual path/argv immutability, expected-vs-actual mismatch,
  output truncation rejection, failed child rejection, derived bundle
  non-copyability/one-time launch, owner release on every error, and artifact
  reread after compile.
- Update
  `test/02_integration/simpleos_compiler_filesystem_qemu_contract_test.shs` to
  require the three dedicated entries and adapter calls, and to retain the
  fixture evidence class as `contract-pass`, never `live-qemu`.
- Add three real QEMU SPipe scenarios under
  `test/03_system/os/compiler_filesystem_qemu_spec.spl`. Each runs the existing
  checker for one architecture and requires `status=pass`,
  `evidence_class=live-qemu`, exact canonical arch, image/nonce binding, exact
  hello digest/output, and a published receipt. Failure/timeout must leave no
  receipt. These are separate acceptance rows; success on one architecture
  cannot cover another.
- Measure the same real image before/after adapter integration: guest workflow
  elapsed ticks, host wall time, QEMU peak RSS, and guest peak evidence-buffer
  capacity. A test-owned capacity counter increments on every evidence/sink
  allocation and decrements on release; boundary and forced-failure tests assert
  its high-water mark is `<= 147456` and final value is zero. No whole
  compiler-sized allocation is permitted. Run the Simple optimizer once on touched
  `.spl` hot paths when the admitted self-hosted runtime is available; absence
  of that runtime is reported, not replaced by the Rust seed.

## Implementation stop conditions

Keep the production readiness gate closed if any target lacks authenticated
stdout/exit evidence, stable VFS snapshot streaming, artifact creation through
the guest filesystem, or a target-matched executable compiler. Never substitute
the existing ARM/RV presence probes, fake runner, host `sha256sum`, or protocol
text emitted outside `compiler_filesystem_guest_workflow_v2`.
