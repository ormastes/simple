# Phase-2 Cross-Compile Progress: lint + test runner (2026-11-23)

Goal: cross-compile Simple's lint and the test runner with the phase-2 builder
for every OS/CPU, with both the native linker (lld) and the Pure Simple linker.
Toolchain: clang + lld, llvm-mingw UCRT on Windows. No GCC, libgcc or MSVC.
Base matrix: `cross_compile_linker_matrix_2026-11-17.md`.

Legend: ✅ done · 🔧 WIP branch pushed · ⏳ not started · ❌ blocked

## Native linker (lld)

| OS | x86_64 | i686 | arm64 | arm32 | riscv64 | riscv32 |
|----|--------|------|-------|-------|---------|---------|
| Linux | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Windows | ✅ | 🔧 hello ✅; lint/test runner blocked (PR2) | ✅ | — | — | — |
| SimpleOS kernel (0 undefined) | ❌ source defects | ✅ #10905 | ✅ #10923 | ✅ #10882 | 🔧 8 → ~1 left | ✅ #10905 |

## Pure Simple linker

| OS | x86_64 | i686 | arm64 | arm32 | riscv64 | riscv32 |
|----|--------|------|-------|-------|---------|---------|
| Linux | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Windows | ✅ | 🔧 hello links + runs; lint/test runner ⏳ | ✅ | — | — | — |
| SimpleOS kernel | ✅ | ✅ (#10841 i386 boot link) | 🔧 gate WIP (#10912 aarch64 support) | ⏳ | ⏳ | ⏳ |

## Landed this round (release/1.0.0)

- #10853 `rt_interp_call` argv is `const uint64_t*`
- #10882 arm32 kernel shims → 0 undefined
- #10886 shared `arch/common/rt_value.spl`
- #10895, #10911 i686 Windows pointer-as-i64 codegen fix (hello prints)
- #10899 arm64 `rt_string_free`
- #10905 shared scalar shims; riscv32 + i686 → 0 undefined
- #10912 aarch64 in the Pure Simple kernel linker (`elf_boot_link.spl`)
- #10923 arm64 `rt_unwrap_or_value` → 0 undefined
- #10939 (`cc26757109c`) `@abi("system")` = stdcall on i686 Windows

## WIP branches on origin (unverified, continue from these)

| Branch | Content | Next step |
|--------|---------|-----------|
| `work/ssos-x64-rv64-link` | riscv64/x86_64 kernel link gates, soft-float `__fixdfdi`/`__floatdidf` (`arch/common/soft_float_conv64.spl`), PMM page export, `os_entry` keepalive imports, x86_64 bug doc | Run riscv64 gate with the LLVM seed, `--link-only`, `SIMPLE_NO_STUB_FALLBACK=1` → 0; check `rt_pci_is_virtio_gpu` export; x86_64 gate must report ERROR; Opus review; PR |
| `work/a64-simple-link-gate-20261123` | `check-simpleos-arm64-simple-link.shs`, `elf/boot_link_cli.spl`, aarch64 fixtures; `boot_link_cli_spec` 7/7 pass | Run gate for the real undefined count; fix leftovers; Opus review; PR |

## Remaining

1. **Windows i686 PR2:** target-width pointer slots in `windows_process_owner_abi.spl`
   and `windows_image_owner` (currently x86_64-only). After that, cross-link lint and
   the test runner with lld and the Pure Simple linker, and run them.
2. **Windows i686 todos:** the seed picks MSVC clang for i686; differences between the
   PE writer and lld.
3. **SimpleOS riscv64:** finish the gate (branch above).
4. **SimpleOS x86_64:** missing `x86_64_auth_trust_config` and `os.drivers.framebuffer.fb_font`,
   HIR errors, `--entry-closure` does not narrow the build. Bug doc is on the WIP branch.
5. **SimpleOS Pure Simple linker:** arm64 gate (branch above); `elf_boot_link` support for
   arm32, riscv64 and riscv32.
6. **Linux / FreeBSD lint + test-runner phase-2 runs** on WSL for every CPU (32/64-bit),
   and the SimpleOS 32/64-bit userland runs.
7. **Fable common-rt/HAL plan:** hal_iface, hal_impl per arch, then the families.
8. **Infra:** C: free space (keep ≥15 GB; about 19 GB at the cut); WSL `ext4.vhdx` needs an
   admin `diskpart compact`.

LLVM seed used by the gates: `C:/dev/wt/rtval-target-ut/release/simple.exe` (built from e0fc6622375).
