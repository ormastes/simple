# SimpleOS Toolchain Deployment/Desktop Boot Blockers

Status: OPEN

Owner plan:
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.

## Active blockers

| ID | Owner location | Exact gap | Unblock condition |
|---|---|---|---|
| B-HOST-CLI | `src/compiler/mir_opt/mir_opt/typed_storage_view_producer.spl:132` | Admitted Stage 2 rejects the multiline condition during strict Stage 3 | A materially changed source fix passes Stage 3 admission, produces Stage 4, and the exact Stage 4 binary passes essential-tools smoke |
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
- Feature attempts 2 and 3 are the only retries remaining globally. They may
  be used only after a materially changed fix. First-time downstream work is
  ordinary execution; any downstream fix-and-retry consumes the same shared
  remaining budget. No blocker receives an independent retry cap.
