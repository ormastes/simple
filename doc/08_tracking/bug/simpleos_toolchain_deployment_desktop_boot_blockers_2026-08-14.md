# SimpleOS Toolchain Deployment/Desktop Boot Blockers

Status: OPEN

Owner plan:
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.

## Active blockers

| ID | Owner location | Exact gap | Unblock condition |
|---|---|---|---|
| B-HOST-CLI | `src/compiler/50.mir/mir_lowering_types.spl:414`; detail: `stage3_post_file_copy_exit139_2026-08-14.md` | GDB proves `maybe_copy_array_value` crashes in aggregate-argument `remember_local_hir_type`; scalar-ID metadata-copy repair is focused-green, but Stage 3/4 remain unadmitted | Resume the retained Stage 3 cache once with the material repair; on admission run Stage 4 plus essential-tools smoke |
| B-TARGET-SIMPLE | `scripts/os/simpleos-native-build.shs:1` | No fresh target payload built by an admitted pure-Simple Stage 4 CLI | Strict build produces target-native static ELF and provenance receipt with fallback disabled |
| B-GUEST-LLD | `src/os/port/llvm/build.spl:1` | No genuine guest-static x86_64 SimpleOS `ld.lld` in this worktree | Pinned-fork build produces a validated static target ELF and dependency/hash receipts |
| B-IMAGE | `src/os/installer/image_builder.spl:1` | No versioned embedded component manifest plus external image admission receipt | Image builder emits both non-self-referential records and validates every canonical alias byte-for-byte |
| B-DESKTOP-LIVE | `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:1` | No same-run production desktop and in-guest Simple compile/run receipt | One OVMF/GRUB run binds desktop, scanout/framebuffer, toolchain, output, rc, kernel, and image evidence |
| B-SPEC | `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl:1` | Frozen fail-closed scenario/manual now call the canonical production wrapper and validate all three receipts; pure-Simple execution/docgen and `sspec-maintain` evidence remain unavailable until Stage 4 and B-DESKTOP unblock | Run the executable scenario, docgen, and one all-seven-score maintenance scan with the admitted Stage-4 runner; no source-only PASS |
| B-PHYSICAL | `doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md:38` | Board not acquired/identified and physical NIC driver/live transcript absent | Named board plus stable by-id media path, reviewed image write, boot/download path, and fresh serial or SSH transcript |

## Historical/superseded attempt ledger

These hashes describe earlier attempts. Their original mutable
`build/bootstrap/logs/...` paths were later overwritten by newer cycles, so the
old bytes are no longer retained at those paths and cannot be re-hashed as
current evidence. They remain chronology only; the latest authority is the
separately hashed section below.

- Attempt 1: strict bootstrap produced admitted Stage 2 SHA-256
  `c7dfde4387f172af527bb37eb3740c1aed9eeeaa20648c0f653e3a6897003c7c`,
  then failed at B-HOST-CLI. Its mutable Stage 3 log path was subsequently
  overwritten and is no longer retained as immutable evidence.
- Attempt 2: nested-guard source SHA-256
  `3c300aaa0e6f5094647dcea2f3aedc129150845647a254acbf816e67a558239e`
  used the planned `--full-cli` command and failed closed before compilation
  because the compiler source made the existing seed/backfill stale.
- Attempt 3: the materially changed `--full-bootstrap --full-cli` command
  rebuilt the Rust authority tuple, produced admitted Stage 2 SHA-256
  `9c8757a5a31d5605b8765267789e0a2d1a882523ec84c523b740ed8ed3c55d10`,
  passed the former multiline parse frontier, then exited 139 later in Stage 3.
  Historical Stage 3 log SHA-256 (bytes no longer retained at the mutable path):
  `2dceab3fd116533537826b09b49cc64acfb2bfaaad6f9e5bd4036d5dd10af263`.
- All three feature attempts are exhausted. Status is WARN; no additional
  fix/retry is permitted in this lane. The Rust-seed interpreter diagnostic for
  `typed_storage_view_producer_spec.spl` passed 5/5, but is not self-host
  admission evidence.

### Historical/superseded primary-repair lane

The exit-143 observations below predate the latest exit-139 reproduction and
must not drive the current resume command.

- Repair attempt 1 reached Stage 2 compilation and exposed missing canonical
  formal-verification HIR contract definitions. Concurrent `origin/main` now
  owns those definitions and propagation; this rebase retained that owner.
- Repair attempt 2 passed Stage 2 and advanced Stage 3 beyond the former
  impossible method receiver. The aggregate command was externally terminated
  with exit 143; no compiler error or backtrace was emitted.
- Repair attempt 3 resumed only Stage 3 from the admitted `build/bootstrap`
  output and was again externally terminated with exit 143. No Stage 3 or
  Stage 4 admission artifact exists. The fresh lane therefore stops WARN under
  the shared three-cycle cap.

### Current authoritative bounded compiler-repair evidence

- Attempt 1 exposed the missing typed parser verification-contract owner during
  Stage 2.
- Attempt 2 passed Stage 2 and its sanity gate, then Stage 3 failed on fourteen
  inferred folded-constant type recoveries.
- Attempt 3 changed folded-constant typing to recover from the original HIR
  expression. Stage 2 and sanity passed and none of the fourteen errors
  recurred. Stage 3 later exited 139 at the distinct `runtime_error`
  static-owner receiver frontier.
- Current Stage 2 SHA-256:
  `f879f1bd1116cb8ac8fe04fdeff278a5dbc01821b993ace5bce3b16b96167218`.
  Stage 2 log SHA-256:
  `1dfe959161d18cc16146825d69f9b5f64240c6917e67ab28718ddd339252bf8f`.
  Stage 3 log SHA-256:
  `bfa17aa9b5ea1b4d7f58eb4b92049a808ee15586384d02fdba47bd06de841a19`.
- These latest results supersede the earlier exit-143 resume suggestion. The
  global three-cycle cap is exhausted; no unchanged command may rerun here.
- A later symbolized diagnostic captured SIGSEGV in
  `MirLowering.remember_local_hir_type`, called from
  `maybe_copy_array_value`; retained GDB log SHA-256 is
  `25f6fb3c1cf8585ed0bfee4c589386e2cc89dff8c60e74d9eab652719d6064ab`.
  The owner-local scalar-ID repair at
  `src/compiler/50.mir/mir_lowering_types.spl` is source-bound and focused
  native-green for append/update/missing-source plus both aligned scalar state
  arrays. Stage 3/4 are still unadmitted. The next permitted action is one
  materially changed cache-preserving Stage 3 resume after the dedicated
  Stage-4 owner releases canonical bootstrap resources.
