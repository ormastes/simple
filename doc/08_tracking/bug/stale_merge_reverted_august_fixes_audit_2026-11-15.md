# 63 August fix commits are absent from release/1.0.0: files sit at their pre-fix content (2026-11-15)

Status: OPEN. One file restored (Ed25519, PR #9464); 152 files unreviewed.

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
