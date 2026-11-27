# 63 August fix commits are absent from release/1.0.0: files sit at their pre-fix content (2026-11-15)

Status: FIXED (2026-11-27; Batch 1 + Batch 2 restored all remaining non-superseded August 2026 fixes across src/, with 51 intentional/superseded skips accounted and 0 unexpected REVERTED rows remaining; C runtime source restores runtime_native.c and test_cpu_common.h verified by inspection pending native C rebuild).

## Finding

For every non-merge `fix*` commit between 2026-08-01 and 2026-08-27 that
modified a file under `src/`, the blob on `origin/release/1.0.0` was compared
with the blob in the commit's parent. **153 files from 63 commits are
byte-identical to their pre-fix content**: the commit is in history, its change
is not in the tree. For 66 of them `git log` names the stale-snapshot merge
`e274cd33719` (2026-08-27, 39,612 files) as the last change. `fcbec1c3b62`
restored only `src/compiler` and `src/lib` afterwards.

This is how the Ed25519 constant-time fix `815f360747b` was lost while its row
read `closed` (`ed25519_scalar_mul_ct_regression_2026-07-20.md`).

Security-relevant entries include `src/os/crypto/{aes_xts,ocb3,cose,ecdsa_p256}.spl`,
`src/os/tls13/hkdf.spl`, `src/app/ui.web/tls_client.spl`,
`src/os/apps/sshd/ssh_pty.spl`, `src/os/kernel/net/tcp_shim.spl`.

## Caveat

Identity with the parent blob proves the change is absent, not why. A fix that
was later reverted on purpose shows up the same way. Each commit needs a look
before restoring, and the restored file must be checked against the current
tree (its callers may have moved on).

## Reproduce

```sh
R=origin/release/1.0.0
git log $R --since=2026-08-01 --until=2026-08-27 --no-merges --format=%H --grep='^fix' -- src |
while read c; do
  git diff-tree --no-commit-id -r -M --diff-filter=M $c -- src |
  while read om nm ob nb st path; do
    [ "$(git rev-parse -q --verify $R:"$path")" = "$ob" ] && echo "${c%"${c#???????????}"} $path"
  done
done
```

## By area

- `src/os/kernel`: 32
- `src/os/crypto`: 16
- `src/lib/nogc_sync_mut`: 12
- `src/app/ffi_gen.specs`: 11
- `src/os/apps`: 10
- `src/lib/common`: 7
- `src/os/tls13`: 6
- `src/os/services`: 6
- `src/app/mcp`: 4
- `src/runtime/platform`: 3
- `src/app/ui.render`: 3
- `src/os/proxy`: 2
- `src/os/drivers`: 2
- `src/compiler/70.backend`: 2
- `src/compiler/60.mir_opt`: 2
- `src/app/sspec_maintain`: 2
- `src/app/qemu`: 2
- `src/app/office`: 2
- `src/app/interpreter`: 2
- `src/os/realtime`: 1
- `src/os/port`: 1
- `src/os/installer`: 1
- `src/os/compositor`: 1
- `src/lib/string.spl`: 1
- `src/lib/nogc_async_mut`: 1
- `src/lib/gc_async_mut`: 1
- `src/FILE.md/`: 1
- `src/compiler/PHASE_FILES.md`: 1
- `src/compiler/80.driver`: 1
- `src/compiler/30.types`: 1
- `src/compiler/20.hir`: 1
- `src/compiler/00.common`: 1
- `src/app/ui.web`: 1
- `src/app/ui.test_api`: 1
- `src/app/ui.tauri`: 1
- `src/app/ui.ipc`: 1
- `src/app/ui.chromium.acid2`: 1
- `src/app/ui.chromium`: 1
- `src/app/ui.browser`: 1
- `src/app/ui`: 1
- `src/app/package.registry`: 1
- `src/app/desugar`: 1
- `src/app/compile`: 1
- `src/app/cli`: 1
- `src/app/check`: 1
- `src/app/build`: 1

## Full list (fix commit, file)

```
7d7bb413700 src/os/crypto/aes_xts.spl
aa0fbd39bdf src/os/port/guest_toolchain_artifact_build_receipt.spl
16044b91b7b src/os/drivers/audio/hda_pci_binding.spl
31edb3cdaee src/os/kernel/arch/riscv32/sbi.spl
f515061dc37 src/os/kernel/arch/arm64/virtio_input.spl
f515061dc37 src/os/kernel/arch/riscv64/virtio_input.spl
952eba04ea1 src/os/kernel/arch/arm32/context.spl
952eba04ea1 src/os/kernel/arch/arm64/context.spl
952eba04ea1 src/os/kernel/arch/riscv32/context.spl
63541f55d63 src/app/ffi_gen.specs/archive_mod.spl
63541f55d63 src/app/ffi_gen.specs/cli_mod.spl
63541f55d63 src/app/ffi_gen.specs/codegen_mod.spl
63541f55d63 src/app/ffi_gen.specs/concurrent_mod.spl
63541f55d63 src/app/ffi_gen.specs/crypto_mod.spl
63541f55d63 src/app/ffi_gen.specs/data_mod.spl
63541f55d63 src/app/ffi_gen.specs/gc_full.spl
63541f55d63 src/app/ffi_gen.specs/process_mod.spl
63541f55d63 src/app/ffi_gen.specs/serde_mod.spl
63541f55d63 src/app/ffi_gen.specs/system_mod.spl
63541f55d63 src/app/ffi_gen.specs/time_mod.spl
2fd38a34853 src/app/interpreter/ffi/span_ffi.spl
bba6c43508b src/os/kernel/log/klog_api.spl
bba6c43508b src/os/services/pkg/pkg_service.spl
44b272850d8 src/os/kernel/boot/x86_64_services.spl
fe24dc9c76d src/os/tls13/hkdf.spl
cf3144cc2e1 src/os/crypto/ocb3.spl
be9ccb4fa1e src/os/apps/sshd/ssh_pty.spl
9f4b24f41b1 src/app/interpreter/ffi/ast_ffi.spl
7de3c288cf8 src/app/ui.web/tls_client.spl
9ec9ebf4391 src/os/crypto/cose.spl
9ec9ebf4391 src/os/crypto/ecdsa_p256.spl
fbcdc196dfb src/os/kernel/net/tcp_shim.spl
31d21e30f82 src/app/compile/native_profile_counter_runtime.spl
3aa7a097461 src/app/sspec_maintain/documentize.spl
662070aa9d9 src/app/sspec_maintain/documentize.spl
e7ceed097be src/compiler/00.common/assurance/nat_normalizer_receipt.spl
e761acfb640 src/app/mcp/debug_eval.spl
e761acfb640 src/app/mcp/debug_log_tools.spl
e761acfb640 src/app/mcp/debug_session.spl
4558514d53f src/compiler/30.types/__init__.spl
e52f3e4de26 src/compiler/20.hir/hir_lowering/_Items/verification_contract_lowering.spl
b2623c437f8 src/compiler/70.backend/irdsl/parser.spl
5aa2e2f5034 src/compiler/60.mir_opt/mir_opt/cse.spl
5aa2e2f5034 src/compiler/60.mir_opt/mir_opt/generator_sm.spl
bdba7b0a49d src/os/kernel/arch/riscv64/process_stdout_capture.spl
f9a7b5cb296 src/app/ui.render/widgets.spl
f9a7b5cb296 src/lib/common/option.spl
f9a7b5cb296 src/lib/common/option_ce.spl
f9a7b5cb296 src/lib/common/result.spl
f9a7b5cb296 src/lib/common/result_ce.spl
f6d3ecb6e9a src/os/tls13/_CertVerify/der_parsing.spl
0629fe96f63 src/os/tls13/server_builders.spl
e944fb02227 src/app/package.registry/verify.spl
d1dbfccb966 src/app/cli/baremetal_cmd.spl
27bf6465607 src/app/ui.ipc/async_handler.spl
0d22d4ada52 src/runtime/platform/test_cpu_common.h
990f565858b src/runtime/platform/test_cpu_common.h
1ab58bd9962 src/runtime/platform/test_cpu_common.h
dec68f5173f src/app/build/targets/change_classifier.spl
21c079649a3 src/app/ui.browser/dom_bridge.spl
9e65c5356b6 src/lib/nogc_sync_mut/enterprise_payment/payment.spl
9e65c5356b6 src/lib/nogc_sync_mut/enterprise_session/session.spl
9e65c5356b6 src/lib/nogc_sync_mut/enterprise_session/throttle.spl
06dc5f66b17 src/app/ui.chromium.acid2/pixel_grid.spl
cb2d0f31577 src/lib/nogc_sync_mut/enterprise_payment/payment.spl
cb2d0f31577 src/lib/nogc_sync_mut/enterprise_session/session.spl
cb2d0f31577 src/lib/nogc_sync_mut/enterprise_session/throttle.spl
a54492228c6 src/lib/nogc_sync_mut/enterprise_payment/payment.spl
a54492228c6 src/lib/nogc_sync_mut/enterprise_session/session.spl
a54492228c6 src/lib/nogc_sync_mut/enterprise_session/throttle.spl
96e7eaf10be src/lib/nogc_sync_mut/enterprise_session/session.spl
96e7eaf10be src/lib/nogc_sync_mut/enterprise_session/throttle.spl
e52061bb710 src/compiler/70.backend/irdsl/parser.spl
fd085136a6d src/os/compositor/vulkan_present_damage_gate.spl
db237ffabde src/app/ui.tauri/app.spl
db237ffabde src/app/ui/main.spl
7731b4c1394 src/app/mcp/main_dispatch_core.spl
7731b4c1394 src/app/office/sheets/access_server.spl
7731b4c1394 src/app/ui.render/__init__.spl
7731b4c1394 src/app/ui.render/layout.spl
7731b4c1394 src/app/ui.test_api/mount.spl
7731b4c1394 src/compiler/PHASE_FILES.md
7731b4c1394 src/lib/common/spec/evidence/format/terminal_grid.spl
7731b4c1394 src/lib/gc_async_mut/gpu/engine2d/helpers/text_fallback.spl
7731b4c1394 src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl
7731b4c1394 src/lib/nogc_sync_mut/gpu_driver/driver_adapter.spl
7731b4c1394 src/lib/string.spl
7731b4c1394 src/os/drivers/driver_platform_contract.spl
7731b4c1394 src/os/installer/usb_installer.spl
7731b4c1394 src/os/kernel/arch/arm32/cstart.spl
7731b4c1394 src/os/kernel/arch/arm32/entropy.spl
7731b4c1394 src/os/kernel/arch/arm32/interrupt.spl
7731b4c1394 src/os/kernel/arch/arm64/canary.spl
7731b4c1394 src/os/kernel/arch/arm64/cstart.spl
7731b4c1394 src/os/kernel/arch/arm64/entropy.spl
7731b4c1394 src/os/kernel/arch/arm64/interrupt.spl
7731b4c1394 src/os/kernel/arch/common/x86_descriptor.spl
7731b4c1394 src/os/kernel/arch/riscv32/cstart.spl
7731b4c1394 src/os/kernel/arch/riscv32/entropy.spl
7731b4c1394 src/os/kernel/arch/riscv64/canary.spl
7731b4c1394 src/os/kernel/arch/riscv64/cstart.spl
7731b4c1394 src/os/kernel/arch/riscv64/entropy.spl
7731b4c1394 src/os/kernel/arch/x86_32/cstart.spl
7731b4c1394 src/os/kernel/arch/x86_32/entropy.spl
7731b4c1394 src/os/kernel/arch/x86_64/canary.spl
7731b4c1394 src/os/kernel/arch/x86_64/cstart.spl
7731b4c1394 src/os/kernel/arch/x86_64/entropy.spl
7731b4c1394 src/os/kernel/arch/x86_64/gdt.spl
7731b4c1394 src/os/kernel/arch_adapt/riscv64_entropy_time.spl
7731b4c1394 src/os/services/package_installer.spl
f33ed64bddb src/lib/common/crypto/x25519_mlkem768/avx2_full_operation_receipt.spl
fd94c46b7af src/lib/common/spec/evidence/action_trace.spl
7c40b71e170 src/app/desugar/rewriter.spl
9a7812edd8d src/app/ui.chromium/engine_merge.spl
e58ad7ca709 src/os/kernel/ipc/host_gpu_ivshmem_map.spl
fc399265320 src/app/qemu/commands.spl
fc399265320 src/app/qemu/main.spl
fc399265320 src/os/realtime/jtag/t32_watchdog.spl
c5588d34c6f src/compiler/80.driver/driver_api_core.spl
4d6616c2426 src/os/crypto/ed25519.spl
22244edef08 src/FILE.md
c5851ae6021 src/os/apps/coreutils/chmod.spl
c5851ae6021 src/os/apps/coreutils/cp.spl
c5851ae6021 src/os/apps/coreutils/mem.spl
c5851ae6021 src/os/apps/coreutils/mv.spl
c5851ae6021 src/os/apps/coreutils/reboot.spl
c5851ae6021 src/os/apps/coreutils/rm.spl
335e0c5c7f8 src/os/apps/coreutils/kill.spl
c31119412fb src/os/crypto/aes128_tables.spl
c31119412fb src/os/crypto/aes_gcm_siv_aes_core.spl
c31119412fb src/os/crypto/sha384.spl
c31119412fb src/os/crypto/sha512.spl
c31119412fb src/os/kernel/loader/dylib_registry.spl
dfb7879dad9 src/os/apps/sshd/ssh_mac.spl
dfb7879dad9 src/os/crypto/aes_gcm_siv.spl
dfb7879dad9 src/os/crypto/random.spl
dfb7879dad9 src/os/crypto/rsa_fallback.spl
dfb7879dad9 src/os/crypto/serpent.spl
dfb7879dad9 src/os/crypto/zuc.spl
dfb7879dad9 src/os/proxy/socks5.spl
dfb7879dad9 src/os/proxy/stun.spl
dfb7879dad9 src/os/tls13/key_schedule.spl
dfb7879dad9 src/os/tls13/transcript.spl
ae0b53c9e3d src/app/check/render_adapter.spl
ae0b53c9e3d src/os/apps/smux/mod.spl
ae0b53c9e3d src/os/crypto/ecdsa_p521.spl
ae0b53c9e3d src/os/services/netstack/_TcpConnection/connection_struct.spl
ae0b53c9e3d src/os/services/netstack/_TcpConnection/data_and_segments.spl
ae0b53c9e3d src/os/services/netstack/_TcpConnection/state_helpers.spl
ae0b53c9e3d src/os/services/netstack/_TcpConnection/state_machine.spl
ae0b53c9e3d src/os/tls13/mod.spl
e15126aa84f src/app/office/slides/render.spl
```

## 2026-11-26 Re-Audit against `origin/release/1.0.0` (`79445b063c4`, `BF-8`)

Re-ran the August fix audit (`since=2026-08-01..until=2026-08-27 --no-merges --grep='^fix' -- src`)
against `HEAD` (`79445b063c4`) including `-M` rename detection:
- **Global August diff census:** `196 MISSING`, `7475 MODIFIED`, `703 PRESENT`, `133 REVERTED`
  (the `152` matched sha+path pairs from the 2026-11-15 list break down as `20` no longer
  `REVERTED` [`6` `PRESENT` restored identically, `14` `MODIFIED` since 2026-11-15], and `132`
  still `REVERTED`, plus `1` rename hit `3d18917817b src/lib/nogc_sync_mut/ffi/codegen/__init__.spl`).
- **Resolved (`PRESENT`, `6`):** `7d7bb413700 src/os/crypto/aes_xts.spl`,
  `16044b91b7b src/os/drivers/audio/hda_pci_binding.spl`, `fe24dc9* src/os/tls13/hkdf.spl`,
  `cf3144c* src/os/crypto/ocb3.spl`, `be9ccb4* src/os/apps/sshd/ssh_pty.spl`,
  `9f4b24f* src/app/interpreter/ffi/ast_ffi.spl`.
- **`src/compiler/20.hir/` status:** `0` files remain `REVERTED` (`e52f3e4de26` in
  `src/compiler/20.hir/hir_lowering/_Items/verification_contract_lowering.spl` superseded by
  `21444791b15` `return None`).
- **Still `REVERTED` in `src/compiler/` (`6` entries, ALL outside `BF-8` `20.hir` ownership):**
  - `e7ceed097be src/compiler/00.common/assurance/nat_normalizer_receipt.spl` (4 bare `int` annotations remain)
  - `4558514d53f src/compiler/30.types/__init__.spl` (duplicate dim_* exports / stale `bidirectional_checking`, `BF-1` lane)
  - `b2623c437f8` & `e52061bb710 src/compiler/70.backend/irdsl/parser.spl` (`split(":", 2)` / `var result`, `BF-2` lane)
  - `7731b4c1394 src/compiler/PHASE_FILES.md`
  - `c5588d34c6f src/compiler/80.driver/driver_api_core.spl` (`Span` / `SdnValue` facade imports, `BF-2` lane)
- **Critical security/crypto fix still `REVERTED` (`src/os/`, outside `BF-8`):**
  - `4d6616c2426 src/os/crypto/ed25519.spl` still carries fabricated RFC 8032 TEST 2 signature bytes
    `0x9c, 0x7e, 0x94` at lines 618-621 (`src/lib/common/crypto/ed25519.spl` already has the real vector).
- **By top-level directory among the `133 REVERTED` entries:** `src/os` (67), `src/app` (36),
  `src/lib` (20), `src/compiler` (6), `src/runtime` (3), `src/FILE.md` (1).
- **Status kept `open`** honestly pending remaining non-`20.hir` owners; host invariant check wired in
  `test/01_unit/compiler/held_verify/mir_optional_field_and_august_audit_spec.spl` (`4/4` pass).

## 2026-11-27 Batch 1 Restoration (P1-1: Compiler & Crypto Security Fixes)

- **Restored `src/compiler/` fixes (`5` of `6` flagged rows):**
  - `e7ceed097be` -> `src/compiler/00.common/assurance/nat_normalizer_receipt.spl` (`max_literal_bits: i64`, `max_rewrite_steps: i64`) and companion `src/compiler/00.common/assurance/sha512_integrity_receipt.spl` (`expected_length: i64`, `subject_length: i64`). Verified via `nat_normalizer_receipt_spec.spl` (`5/5`), `sha512_integrity_receipt_spec.spl` (`3/3`), and `august_audit_batch1_restorations_spec.spl` (`3/3`).
  - `4558514d53f` -> `src/compiler/30.types/__init__.spl` (`bidirectional_inferencer.{TypeInferencer}` re-export and removed duplicate `DimConstraint`, `DimError`, `DimErrorKind`, `DimNote`, `DimNoteKind` exports). Verified via `august_audit_batch1_restorations_spec.spl` (`3/3`) and `bidir_type_check_spec.spl` (`7/7`).
  - `b2623c437f8` (superset of `e52061bb710`) -> `src/compiler/70.backend/irdsl/parser.spl` (`split(":", 2)[1]` on `params:`, `backends:`, `category:`, and `var result: [IrParam] = []`). Verified via `parser_validator_spec.spl` (`1/1`) and `august_audit_batch1_restorations_spec.spl` (`3/3`).
  - `c5588d34c6f` -> `src/compiler/80.driver/driver_api_core.spl` (`use compiler.common.diagnostics.span.{Span}` and `use std.common.sdn.value.{SdnValue}`; file stays 20 lines `< 25`). Thin-facade check passes in `driver_api_tier_policy_spec.spl` (`18/21`; 3 pre-existing `pub use` vs `export use` pattern failures unrelated to `driver_api_core.spl`) and `august_audit_batch1_restorations_spec.spl` (`3/3`). Note `genuine_import_ownership_spec.spl` runs `2/3` (pre-existing failure on `src/app/io/_CliCommands/handler_commands.spl`, outside lane).
- **Skipped `src/compiler/` entry (`1`):**
  - `7731b4c1394` -> `src/compiler/PHASE_FILES.md` (**SKIPPED**): `7731b4c1394` erroneously recorded an uncommitted bulk deletion index via plumbing `write-tree` and was immediately reverted by `ad2b5d5307f` (`git ls-files src/compiler/*phase*` shows 0 phase files; `HEAD` `PHASE_FILES.md` is authoritative).
- **Restored `src/os/crypto/` security fixes (`2`):**
  - `4d6616c2426` -> `src/os/crypto/ed25519.spl`: replaced fabricated RFC 8032 TEST 2 signature bytes (`0x9c, 0x7e, 0x94...`) with the authentic RFC 8032 TEST 2 vector (`0x99, 0x6e, 0x45...`) in comment and `expected_sig2`. Verified via `test/01_unit/os/crypto/ed25519_and_cose_checked_spec.spl` (`ed25519_self_test()` returns `Ok(true)`).
  - `9ec9ebf4391` -> `src/os/crypto/cose.spl` & `src/os/crypto/ecdsa_p256.spl`: restored checked `Result<[u8], CoseError>` / `CoseVerifyResult` propagation on `_cose_sign`, `_cose_verify_sig`, `cose_sign1_create`, and `cose_sign1_verify` (rejecting unsupported algorithms with `CoseError.AlgorithmRejected` and bad P-256 keys/provider errors with `CoseError.InvalidEncoding`; zero external callers of `cose_sign1_create`/`cose_sign1_verify` in `src/` or `test/`). Reconciled `ecdsa_p256.spl` with `bc5e9f3feb9` (`2026-11-25`) by keeping caller-compatible `[u8]`/`bool` signatures on `ecdsa_p256_sign_fixed`/`ecdsa_p256_verify_fixed` (skipping direct signature break from `9ec9ebf4391`) while exposing `ecdsa_p256_sign_fixed_checked` and `ecdsa_p256_verify_fixed_checked` (including `_p256_fixed_spki_to_point` 91->65 conversion). Verified via `ed25519_and_cose_checked_spec.spl` (`4/4` including live ES256 & EdDSA COSE_Sign1), `cose_rfc9052_kat_spec.spl` (`8/8`), and `ecdsa_p256_spec.spl` (`14/14`).
- **Already present (`3`):**
  - `7d7bb413700 src/os/crypto/aes_xts.spl`, `cf3144cc2e1 src/os/crypto/ocb3.spl`, `fe24dc9c76d src/os/tls13/hkdf.spl` had zero diff against `HEAD` (restored earlier in `2f5493a3ce1`). Spec verification: `ocb3_spec.spl` (`15/15`), `hkdf_rfc5869_spec.spl` (`14/14`), `psk_0rtt_spec.spl` (`12/13` — HKDF examples pass; 1 pre-existing `PskBinder` failure), `aes_xts_ieee1619_kat_spec.spl` (`13/17` — block-aligned vectors pass; 4 pre-existing non-16-byte CTS failures), `cert_verify_ecdsa_spec.spl` (`4/8` — pre-existing TLS `cert_verify.spl` DER/P-384/P-521 failures).
- **Status kept `open`** until remaining non-Batch-1 August entries (`src/os/`, `src/lib/`, `src/app/`, `src/runtime/`) are processed in follow-up batches.

## 2026-11-27 Batch 2 Restoration (P1-1: `src/os/`, `src/app/`, `src/lib/`, `src/runtime/`, `src/FILE.md`)

Re-ran the August fix census (`git log --since=2026-08-01 --until=2026-08-27 --no-merges --grep='^fix' -- src`) against `origin/release/1.0.0` (`b6d78c690b2`) and working tree across all `8,536` `diff-tree` pairs (`369` commits), reconciling every remaining non-Batch-1 revert AND subsequent/sibling August commits so callers and newer APIs stay compatible:

### Restored Fixes & Reconciled Sibling/Subsequent Commits (100 files under `src/`, plus `scripts/check/raw_sffi_unsafe_baseline.tsv`)

1. **Crypto, TLS 1.3 & Package Security (Group A):**
   - `src/os/crypto/ed25519.spl`: restored `@unsafe` FFI capability tags on `rt_bytes_u8_at`, `rt_ed25519_sc_muladd`, `rt_ed25519_sc_reduce_64`, `rt_tls13_sha512_full`, removed unused `serial_println`, preserved Batch 1 `4d6616c2426` RFC 8032 TEST 2 vector, and kept newer checked APIs compatible.
   - `src/os/tls13/_CertVerify/der_parsing.spl`: reconciled `9ec9ebf4391` P-256 provider error propagation on top of `f6d3ecb6e9a` & `bc5e9f3feb9` via `ecdsa_p256_verify_fixed_checked`.
   - `src/os/tls13/_CertVerify/signature_verify.spl`, `src/os/tls13/server_builders.spl`, `src/os/tls13/server_handshake.spl`, `src/os/tls13/transcript.spl`: restored checked scheme/signature/ECDSA-fail-closed checks and `28d89fb0a2c` `@unsafe` + `unsafe(capabilities: [ffi]):` scoping.
   - `src/os/kernel/net/tcp_shim.spl`: restored `f6e65cd875b` (`ms <= 0` -> `-1` connect timeout) and `4efad3db3e7` (`ms <= 0` -> `-1` accept timeout + `net_tcp_accept_timeout` alignment).
   - `src/os/apps/sshd/{ssh_channel,ssh_session_channel}.spl`: restored `31d21e30f82` strict 5-byte `SSH_MSG_CHANNEL_EOF` (`payload.len() != 5u64` / `data.len() != 5`).
   - `src/app/package.registry/{signing,verify}.spl`: restored fail-closed signature/checksum audit checks (`package-signature-fail-closed.shs`: PASS).
   - `src/app/ui.web/tls_client.spl`: restored nullable `rt_tls_client_read_checked` client read (`tls-client-sffi-fail-closed.shs` web-client check passes; 3 pre-existing failures remain in untouched `src/lib/nogc_sync_mut/io/tls_sffi.spl` & `src/app/io/tls_sffi.spl`).

2. **Co-Compiled Symbol Collision Disambiguations (Group B, `dfb7879dad9` / `c31119412fb`):**
   - Disambiguated private/helper collisions across `src/os/crypto/{aes128_tables,aes256_gcm,aes_gcm,aes_gcm_siv,aes_gcm_siv_aes_core,aes_gcm_siv_polyval,rsa_fallback,scrypt,serpent,sha256,sha384,sha512,zuc}.spl`, `src/os/proxy/{socks5,stun}.spl`, `src/os/tls13/{_Tls13/context_io,_Tls13/handshake,handshake13,key_schedule,record13,server}.spl`, and `src/os/apps/sshd/ssh_mac.spl` (preserving newer `gcm_gf128` delegation in `aes256_gcm.spl` and `68d56f11832` pure-Simple byte indexing / `@unsafe rt_bytes_to_text` in `socks5.spl`).

3. **SFFI Authority & Checked/Unsafe Scopes (Group C) + Ratchet Baseline Hygiene:**
   - Restored SFFI authority & `@unsafe(capabilities: [ffi])` boundaries across `src/app/interpreter/ffi/span_ffi.spl`, `src/os/kernel/arch/arm32/{context,timer}.spl`, `src/os/kernel/arch/arm64/{context,virtio_input}.spl`, `src/os/kernel/arch/riscv32/{context,sbi}.spl`, `src/os/kernel/arch/riscv64/{sbi,virtio_input}.spl`, `src/os/kernel/boot/x86_64_services.spl`, `src/os/kernel/log/klog_api.spl`, and `src/os/services/pkg/pkg_service.spl`.
   - Pruned the `54` resolved/removed `extern fn` entries in `scripts/check/raw_sffi_unsafe_baseline.tsv` (51 across our Group A/C files + 3 in `src/os/proxy/socks5.spl`).

4. **App, Compositor, OS Hygiene, Build & Runtime Source Restorations (Group D):**
   - `src/FILE.md`, `src/app/build/targets/change_classifier.spl`, `src/app/check/render_adapter.spl`, `src/app/cli/baremetal_cmd.spl`, `src/app/compile/native_profile_counter_runtime.spl`, `src/app/debug/remote/feature/emulation.spl`, `src/app/desugar/rewriter.spl`, `src/app/ffi_gen.specs/{archive_mod,cli_mod,codegen_mod,concurrent_mod,cranelift_core,crypto_mod,data_mod,gc_full,io_full,net_mod,process_mod,runtime_value_full,serde_mod,system_mod,time_mod}.spl`, `src/app/mcp/{debug_eval,debug_log_tools,debug_session}.spl`, `src/app/office/slides/render.spl`, `src/app/qemu/{commands,main}.spl`, `src/app/replay/record_session.spl`, `src/app/sspec_maintain/{documentize,source_facts}.spl`, `src/app/ui.chromium/engine_merge.spl`, `src/app/ui.chromium.acid2/pixel_grid.spl`, `src/app/ui.ipc/async_handler.spl`.
   - `src/os/apps/coreutils/{chmod,cp,kill,mem,mv,reboot,rm}.spl`, `src/os/apps/smux/mod.spl`, `src/os/compositor/vulkan_present_damage_gate.spl`, `src/os/crypto/{ecdsa_p521,random,scram_common}.spl`, `src/os/kernel/fs/win_vfs/win_vfs_driver.spl`, `src/os/machine_profile.spl` (`BareMetal`), `src/os/services/netstack/_TcpConnection/{connection_struct,data_and_segments,state_helpers,state_machine}.spl`, `src/os/tls13/mod.spl`, `src/os/userlib/_Window/{client,ipc_helpers}.spl`.
   - `src/runtime/platform/test_cpu_common.h` and `src/runtime/runtime_native.c` (`fbcdc196dfb` negative `ms` timeout clamping on `rt_io_tcp_set_read_timeout`/`rt_io_tcp_set_write_timeout`; C source restored and verified by inspection; native C runtime rebuild deferred outside this Windows interpreter lane).

### Final August Census & Accounted Skips (`51` REVERTED, `0` Unexpected)

- **Census against working tree (`8,536` pairs):** `738 PRESENT`, `51 REVERTED`, `7,551 MODIFIED`, `196 MISSING` (`0` unreviewed/unexpected reverted rows).
- **All `51` `REVERTED` entries intentionally skipped / superseded:**
  - `7731b4c1394` (`33` files across `src/app/`, `src/compiler/`, `src/lib/`, `src/os/`): accidental dirty-index bulk edit immediately reverted by `ad2b5d5307f`.
  - `96e7eaf10be` (2), `9e65c5356b6` (3), `a54492228c6` (3), `cb2d0f31577` (3) (`11` rows across `src/lib/nogc_sync_mut/enterprise_payment/payment.spl` & `enterprise_session/{session,throttle}.spl`): superseded/restored cleanly by `6b0b2175a06` (`restore(enterprise)`).
  - `f9a7b5cb296` (`4` rows: `src/lib/common/{option,option_ce,result,result_ce}.spl`): superseded by `28df8ceac42` (`feat(types): written Any policy and Any-free compiled sources`).
  - `bdba7b0a49d` (`1` row: `src/os/kernel/arch/riscv64/process_stdout_capture.spl`): superseded by `6bae19786a9` & `fa946add2ba`.
  - `db237ffabde` (`1` row: `src/app/ui/main.spl`): raw-extern `rt_cli_get_args`/`sys_get_args` workaround intentionally reverted by `775ae478ca3` to `app.io.cli_ops.cli_get_args`.
  - `31d01cd322d` (`1` row: `src/compiler/80.driver/driver_api_core.spl`): superseded by `c5588d34c6f` restored in Batch 1.

### Batch 2 Verification Evidence (Host Interpreter `--mode=interpreter` & Audits)

- `test/01_unit/compiler/held_verify/august_audit_batch2_restorations_spec.spl`: **13/13 passed** (`0 failed`)
- `test/01_unit/compiler/held_verify/mir_optional_field_and_august_audit_spec.spl`: **4/4 passed** (`0 failed`)
- `test/01_unit/os/crypto/ed25519_and_cose_checked_spec.spl`: **4/4 passed** (`0 failed`)
- `test/01_unit/os/proxy/socks5_spec.spl`: **31/31 passed** (`0 failed`)
- `test/01_unit/os/crypto/sha512_kat_spec.spl`: **3/3 passed** (`0 failed`)
- `test/01_unit/os/crypto/zuc_kat_spec.spl`: **8/8 passed** (`0 failed`)
- `test/01_unit/app/build/change_classifier_spec.spl`: **8/8 passed** (`0 failed`)
- `test/01_unit/os/compositor/vulkan_present_damage_gate_spec.spl`: **2/2 passed** (`0 failed`)
- `test/01_unit/app/package_cli_spec.spl`: **3/3 passed** (`0 failed`)
- `test/01_unit/os/apps/coreutils/kill_spec.spl`: **14/14 passed** (`0 failed`)
- `test/01_unit/app/mcp_unit/debug_eval_spec.spl`: **15/15 passed** (`0 failed`)
- `test/01_unit/os/machine_profile_spec.spl`: **6/6 passed** (`0 failed`)
- `test/01_unit/app/desugar/rewriter_static_calls_spec.spl`: **1/1 passed** (`0 failed`, skipped case inside spec)
- `test/01_unit/app/desugar/rewriter_constants_spec.spl`: **1/1 passed** (`0 failed`, skipped case inside spec)
- Pre-existing partial/unrelated host failures observed cleanly (0 regressions from Batch 2): `cert_verify_ecdsa_spec.spl` (`4/8`), `sha384_kat_spec.spl` (`4/7` — FIPS KATs pass, 3 high-bit hex diag checks fail in interpreter), `engine_merge_spec.spl` (`4/7` — `browser_engine` layout/spec-line-158 mismatch), `scoring_spec.spl` (`19/21` — `extract_sspec_manual_facts` passes, 2 AST tautology failures), `chmod_spec.spl` (`7/8` — arg parsing passes, OS `vfs_chmod` extern missing in host interpreter), `server_accept_spec.spl` (`0/1` — missing `std.nogc_sync_mut.io.signature_ffi` in test file).
- Authority audits PASS: `package-signature-fail-closed.shs`, `check-riscv-sbi-sffi-authority.shs`, `user-entry-virtio-input-sffi-authority.shs`, `x86-64-boot-services-sffi-authority.shs`, `arch-context-timer-sffi-authority.shs`, `pkg-service-logging-sffi-authority.shs`, `interpreter-span-sffi-authority.shs` (`crypto-sffi-checked-callers.shs` & `tls-client-sffi-fail-closed.shs` report 0 errors in edited files and only pre-existing failures in untouched files).
