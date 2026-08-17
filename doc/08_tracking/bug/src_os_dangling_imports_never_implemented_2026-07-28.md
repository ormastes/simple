# `src/os/**`: 46 imported modules/symbols that were never implemented

**Status:** OPEN (out-of-scope — no implementation invented, per triage brief)
**Found:** 2026-07-28 (dangling-reference triage, `src/os/**` + `src/unit/**` scope)
**Re-verified:** 2026-08-10 — reran
`sh scripts/check/check-dangling-references.shs --path src/os --path src/unit`
(now reports 35 dangling references, some new/unrelated to this doc's 46, e.g.
`WM_STATUS_*` — filed separately per the note above) and cross-checked a sample
of this doc's original 46 entries with the same definition-anchored-grep method
used in the original triage. Result: roughly a third of the original entries
were resolved by other sessions since filing (either a real implementation
landed — e.g. `bn_one`/`bn_from_i64` now defined in
`src/lib/common/math/bignum/bignat.spl`, so the `ecdsa_p521.spl` bignat imports
now resolve — or the referencing code was refactored away from the missing
symbol, e.g. `TcpStateMachine` is no longer imported anywhere under
`_TcpConnection/`). Confirmed STILL dangling by both the checker and a fresh
anchored grep: `FeP256`/`fe_p256`, `md5`, `display_protocol` (+ its 4 symbols),
`line_wrap`/`line_unwrap`, `FbCompositorBackend`, `spring_progress`,
`FirmwareSha256`/`parse_sha256_hex_words`, `current_architecture`,
`tree_readdir`, `FileExplorer` — i.e. the crypto and compositor gaps called out
in "Suggested triage order" below are still entirely unimplemented. No fix
attempted here: each remaining entry still requires writing a real
implementation (crypto field arithmetic, MD5, PEM line wrapping, compositor
drawing primitives, boot-time arch probe, VFS readdir, file-explorer type),
which is explicitly out of scope for this pass ("do NOT invent an
implementation").
**Area:** `src/os/crypto/`, `src/os/compositor/`, `src/os/services/`, `src/os/apps/`,
`src/os/kernel/`
**Severity:** medium-high — each entry is an import that resolves to nothing.
Several sit on security-relevant code paths (SCRAM-SHA-1 auth, ECDSA P-521,
ECDH P-256, PEM).

Detected by `sh scripts/check/check-dangling-references.shs --path src/os --path src/unit`.
The WM protocol cluster is filed separately in
`wm_protocol_status_event_symbols_never_implemented_2026-07-28.md`.

## Classification method

For every entry below:

1. The referenced module file was searched for across the whole tree by full
   path **and** by basename (`git ls-files`), including `std.*` → `src/lib/`
   resolution.
2. Where the module file exists, the symbol was searched for with a
   definition-anchored pattern
   (`^\s*(pub )?(struct|class|enum|trait|fn|me|val|var|const|type)\s+NAME\b`)
   across all of `src/**/*.spl`, plus an alias-re-export pattern (`as NAME}`).
3. History was checked with `git log --diff-filter=AD` on the module basename
   and `git log -S` scoped to the owning file.

**Every entry below came back with zero definitions in the working tree and zero
definition-shaped occurrences in history.** None is a rename, a move, or a
wrongly-deleted file. The only history hits were the three known
jj-conflict-tree churn commits (`37cda4befdc`, `857e26b0cbc`, `752425d3fcc`),
which add and delete whole `.jjconflict-side-N/` trees wholesale and are not
evidence of a real definition.

## MODULE — module named by a `use` that no file provides (5)

| Referencing site | Missing module | Notes |
|---|---|---|
| `src/os/crypto/ecdh_p256.spl:46` | `std.common.math.field.fe_p256` | also missing symbol `FeP256` |
| `src/os/crypto/p256.spl:21` | `std.common.math.field.fe_p256` | also missing symbol `FeP256` |
| `src/os/crypto/ecdsa_p521.spl:35` | `std.math.bignum.bignat` | also missing `bn_one`, `bn_from_i64`, `div_mod`, `get_bit`, `from_bytes_be` |
| `src/os/crypto/pbkdf1.spl:15` | `std.crypto.md5` | no MD5 implementation anywhere in `src/` |
| `src/os/services/display/display_service.spl:15` | `common.display_protocol.display_protocol` | also missing `DisplayMode`, `SurfaceDesc`, `surface_desc`, `PIXEL_FORMAT_BGRA8` |

No file named `fe_p256.spl`, `bignat.spl`, `md5.spl`, or `display_protocol.spl`
has ever existed under `src/` — `git log --diff-filter=AD -- '*/<name>.spl'`
returns empty for all four.

## SYMBOL — module exists, symbol declared nowhere (41)

### Crypto (security-relevant)

| Referencing site | Missing symbol | Module status |
|---|---|---|
| `src/os/crypto/scram_sha1.spl:4` | `pbkdf2_sha1_bytes` | `src/lib/crypto/pbkdf2.spl` re-exports only `pbkdf2_sha256_bytes`, `pbkdf2_sha384_bytes`, `pbkdf2_sha512_bytes`. **SCRAM-SHA-1 authentication has no KDF.** |
| `src/os/crypto/scram_common.spl:7` | `pbkdf2_sha1_bytes` | same |
| `src/os/crypto/pem.spl:22` | `line_wrap`, `line_unwrap` | `src/lib/common/base_encoding/utilities.spl` exists, declares neither. PEM cannot wrap/unwrap base64 at 64 cols. |

### Compositor / graphics

| Referencing site | Missing symbol | Module status |
|---|---|---|
| `src/os/compositor/mod.spl:25`, `engine2d_display.spl:22`, `fb_backend.spl:20` | `FbCompositorBackend` | `display_backend.spl` (69 lines) declares only `GpuCompositorBackend`. The nearby `fb_backend.spl` has `FramebufferBackend`, a *different* UI-backend shape, not a `CompositorBackend` impl — this is not a rename. |
| `src/os/compositor/mod.spl:20` | `draw_window_frame`, `draw_glass_window_frame`, `draw_glass_window_frame_enhanced` | `decorations.spl` (66 lines) is geometry helpers only — no drawing functions at all. |
| `src/os/compositor/mod.spl:31` | `draw_text_bold`, `draw_text_2x`, `draw_text_vector` | `text_render.spl` (30 lines) has only `draw_text_at`, `draw_text_scaled`, `text_width`, `text_width_2x`. |
| `src/os/compositor/animation_controller.spl:7` | `spring_progress` | `src/lib/common/animation/spring.spl` exists, no such fn. |
| `src/os/compositor/engine2d_render_evidence.spl:17` | `FirmwareSha256`, `parse_sha256_hex_words` | `src/os/drivers/framebuffer/ramfb.spl` exists, declares neither. |
| `src/os/compositor/wm_spm_client.spl:19` | `mark_destroyed` | `src/lib/common/win_fs/window_record.spl` exists, no such fn. |

`FbCompositorBackend` appears in five design docs
(`doc/04_architecture/os/shared_wm_stack.md`,
`doc/02_requirements/platform/platform/cross_platform_wm.md`, and three others)
and in `examples/09_embedded/simple_os/arch/x86_64/boot/glass_render.c`, but was
never implemented in Simple. The docs are aspirational.

### Netstack

| Referencing site | Missing symbol | Module status |
|---|---|---|
| `src/os/services/netstack/_TcpConnection/connection_struct.spl:34` | `TcpStateMachine` | `tcp_state_machine.spl` (158 lines) declares `TcpState`, `SocketEntry`, `AcceptQueue`, `TcpStateSocketTable` — no `TcpStateMachine`. |
| `src/os/services/netstack/_TcpConnection/data_and_segments.spl:34` | `TcpStateMachine` | same |
| `src/os/services/netstack/_TcpConnection/state_helpers.spl:34` | `TcpStateMachine` | same |
| `src/os/services/netstack/_TcpConnection/state_machine.spl:34` | `TcpStateMachine` | same |

### Kernel / VFS

| Referencing site | Missing symbol | Module status |
|---|---|---|
| `src/os/kernel/boot/boot_fs.spl:11` | `current_architecture` | `src/os/kernel/arch/arch_context.spl` exists, no such fn. Boot-path architecture probe is unresolved. |
| `src/os/kernel/fs/win_vfs/win_vfs_driver.spl:19` | `tree_readdir` | `src/lib/common/win_fs/fs_encoder.spl` exists, no such fn. |
| `src/os/kernel/fs/win_vfs/win_vfs_driver.spl:18` | `window_state_name` | `src/lib/common/win_fs/window_record.spl` exists, no such fn. |

### Apps / desktop

| Referencing site | Missing symbol | Module status |
|---|---|---|
| `src/os/desktop/shell.spl:28` | `AppId` | `src/lib/common/window_protocol/geometry.spl` exists, no such type. |
| `src/os/desktop/shell_ui_builders.spl:23` | `FileExplorer` | `file_explorer.spl` is a 12-line facade re-exporting `_FileExplorer.{model,app,view}`; none of the three declares `FileExplorer` (they have `ExplorerEntry`, `FileExplorerState`). |
| `src/os/apps/installer_gui/mod.spl:9` | `InstallerStep` | `installer_gui.spl` exists, no such type. |
| `src/os/apps/installer_gui/mod.spl:11` | `UpgradeState` | `upgrade_gui.spl` exists, no such type. |
| `src/os/apps/smux/mod.spl:3` | `MuxAttachResult` | `contract.spl` exists, no such type. |
| `src/os/tls13/mod.spl:8` | `parse_tls_test_server_config` | `test_server_config.spl` exists, no such fn. |

## Why these are not fixed here

None is mechanically repointable — there is no existing target to repoint to.
Each requires writing the missing implementation, which the triage brief
explicitly excludes ("do NOT invent an implementation"). Several would change
on-hardware behaviour (kernel boot arch probe, TCP state machine, compositor
backends) or security behaviour (SCRAM-SHA-1 KDF, P-256/P-521 field arithmetic),
where a guessed implementation is worse than a recorded gap.

## Suggested triage order

1. **Crypto gaps** — `pbkdf2_sha1_bytes`, `fe_p256`/`FeP256`, `bignat`, `md5`.
   These sit under `src/os/crypto/` and their absence means the ECDSA/ECDH/SCRAM
   entry points cannot be built at all.
2. **Kernel boot** — `current_architecture` in `boot_fs.spl`.
3. **Netstack** — `TcpStateMachine` (4 importers in `_TcpConnection/`).
4. **Compositor** — decide whether `FbCompositorBackend` and the `draw_*`
   families are still wanted, or whether the importing `mod.spl` re-export lines
   should be deleted as dead.

## CONFIRMED OPEN 2026-08-17 — but it is a DEAD-MODULE defect, not a live boot breakage

The chain is closed end to end:

- `src/os/kernel/boot/boot_fs.spl:11` imports
  `os.kernel.arch.arch_context.{Architecture, current_architecture}`
- it **calls** it at `:392` and `:427` (`val arch = current_architecture()`) —
  live call sites, not a dead import
- `src/os/kernel/arch/arch_context.spl` defines the `Architecture` enum (`:6`)
  and a METHOD `ArchContext.arch()` (`:24`), but **no free function
  `current_architecture` anywhere**; a tree-wide count across `src/os` and
  `src/lib` returns zero

**Why this has never broken a build, which the original report does not say:**
`boot_fs.spl` has **no importer at all**. Every other reference in `src/os` is
either a prose comment or points at the *different* module `boot_fs_mount.spl`.
The file is dead code — which is exactly why an unresolvable import with two live
call sites has sat here undetected. `syscall_file.spl:259-261` already records
the sibling observation that `boot_fs_mount_fat32_from_device` has no caller in
the live boot sequence either, so this is a cluster rather than a one-off.

**Deliberately not fixed.** Both available moves are wrong: implementing
`current_architecture()` means inventing a global/per-CPU arch accessor that
cannot be verified without booting the kernel — a blind guess — and deleting a
dead module is out of proportion and needs an owner's decision.

**Recommendation: retitle.** The row is real, but as filed it reads as a live
missing-symbol defect. It is a dead-module cluster, and the correct question is
whether `boot_fs.spl` should be revived or removed.

Corrections to the original symbol list: `FeP256` (1 definition) and `md5` (2)
DO exist. Only `display_protocol` and `current_architecture` have zero.
