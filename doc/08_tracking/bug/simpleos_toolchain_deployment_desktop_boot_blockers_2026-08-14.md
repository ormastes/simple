# SimpleOS Toolchain Deployment/Desktop Boot Blockers

Status: OPEN

Owner plan:
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.

## Active blockers

| ID | Owner location | Exact gap | Unblock condition |
|---|---|---|---|
| B-HOST-CLI | `doc/08_tracking/bug/stage3_selfhost_post_hir_segfault_2026-08-14.md:66` | The native enum/static-receiver defect is repaired and Stage 2 is green, but two Stage 3 executions were externally terminated with exit 143 before producing an admission artifact | Run one cache-preserving Stage 3 completion under a sufficiently long supervisor, continue Stage 4 from that admitted artifact without rebuilding green Stage 3, and pass essential-tools smoke |
| B-TARGET-SIMPLE | `scripts/os/simpleos-native-build.shs:1` | No fresh target payload built by an admitted pure-Simple Stage 4 CLI | Strict build produces target-native static ELF and provenance receipt with fallback disabled |
| B-GUEST-LLD | `src/os/port/llvm/build.spl:1` | No genuine guest-static x86_64 SimpleOS `ld.lld` in this worktree | Pinned-fork build produces a validated static target ELF and dependency/hash receipts |
| B-IMAGE | `src/os/installer/image_builder.spl:1` | No versioned embedded component manifest plus external image admission receipt | Image builder emits both non-self-referential records and validates every canonical alias byte-for-byte |
| B-DESKTOP-LIVE | `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:1` | No same-run production desktop and in-guest Simple compile/run receipt | One OVMF/GRUB run binds desktop, scanout/framebuffer, toolchain, output, rc, kernel, and image evidence |
| B-SPEC | `test/03_system/os/simpleos_guest_toolchain_live_spec.spl:1` | Existing live scenario permits non-execution green and uses a noncanonical boot/tool flow | Replacement frozen scenario/manual fails closed and passes its one-time quality/traceability gates |
| B-PHYSICAL | `doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md:38` | Board not acquired/identified and physical NIC driver/live transcript absent | Named board plus stable by-id media path, reviewed image write, boot/download path, and fresh serial or SSH transcript |

## Attempt ledger

- Attempt 1: strict bootstrap produced admitted Stage 2 SHA-256
  `c7dfde4387f172af527bb37eb3740c1aed9eeeaa20648c0f653e3a6897003c7c`,
  then failed at B-HOST-CLI. Retained log:
  `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.
- Attempt 2: nested-guard source SHA-256
  `3c300aaa0e6f5094647dcea2f3aedc129150845647a254acbf816e67a558239e`
  used the planned `--full-cli` command and failed closed before compilation
  because the compiler source made the existing seed/backfill stale.
- Attempt 3: the materially changed `--full-bootstrap --full-cli` command
  rebuilt the Rust authority tuple, produced admitted Stage 2 SHA-256
  `9c8757a5a31d5605b8765267789e0a2d1a882523ec84c523b740ed8ed3c55d10`,
  passed the former multiline parse frontier, then exited 139 later in Stage 3.
  Retained Stage 3 log SHA-256:
  `2dceab3fd116533537826b09b49cc64acfb2bfaaad6f9e5bd4036d5dd10af263`.
- All three feature attempts are exhausted. Status is WARN; no additional
  fix/retry is permitted in this lane. The Rust-seed interpreter diagnostic for
  `typed_storage_view_producer_spec.spl` passed 5/5, but is not self-host
  admission evidence.

### Fresh primary-repair lane

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
