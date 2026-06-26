# Multiarch QEMU Systest Skill

**Self-sufficient.** Build, boot, and classify the SimpleOS fs-exec systest lanes
(6 bare-metal QEMU + 1 hosted darwin). Any LLM can run this independently.

Full reference: `doc/07_guide/os/multiarch_qemu_systest_guide.md`. Contract:
`src/os/qemu_systest_contract.spl`. Build matrix:
`src/os/port/simpleos_multiplatform_build_part2.spl`.

## Usage

```
/multiarch_systest              # fresh boot-sweep all lanes, classify, report
/multiarch_systest <arch>       # one lane: build (if needed) + boot + classify
/multiarch_systest --build      # rebuild kernels first, then sweep
```

## Lanes

riscv32, riscv64, arm32, arm64, x86_32, x86_64 (bare-metal QEMU) + aarch64-darwin
(hosted macOS process; `missing-media` RED on Linux, GREEN on Apple Silicon).

## Procedure

1. **Build** (only if `--build` or the ELF is missing) — see the guide's recipe.
   - riscv32 **requires** the LLVM driver: `cd src/compiler_rust && LLVM_SYS_180_PREFIX=/usr/lib/llvm-18 cargo build --package driver --features llvm`.
   - Judge unresolved by `nm`, not link success. Build nice'd/background; retry under load.
2. **Boot** each lane with its `<arch>_qemu_args()` from the contract, serial →
   `build/os/systest/<arch>.serial.log`, per-lane `timeout`. Do NOT trust the test
   runner's cache for a "final" sweep — boot directly.
3. **Classify** with `grep -aqF "<marker>"` (binary-safe — `ugrep`/`grep` skips
   NUL-containing logs without `-a`; riscv logs have NULs). All markers present and
   no `missing-media`/fallback ⇒ GREEN.

## Hard rules

- Missing kernel/image ⇒ `missing-media:<path>` = diagnosed RED. **Never** `skip()`,
  weaken a marker assertion, or print markers unconditionally — each marker must
  assert a real capability on the live success path.
- After any source/dedup change to a lane, **rebuild + reboot + re-verify** that
  lane; **revert** any change that drops a marker. For a lane that genuinely cannot
  be rebuilt in your env, verify a refactor **statically** (linker INCLUDE-expansion
  == original; C TU diff == header-guards/forward-decls only). Watch the boot-dir
  glob: any `.c` in `arch/<arch>/boot/` is auto-compiled — a stray wrapper or
  wrong-arch symlink silently bloats the kernel and breaks boot.
- Parallel sessions clobber uncommitted edits within ~1 min: commit per verified
  step and confirm the green-making source is on **origin** (`git diff origin/main`),
  not just the working tree.

## Known status (2026-06-14)

**6/6 QEMU lanes GREEN** (riscv32, riscv64, arm32, arm64, x86_32, x86_64) + darwin
honest-RED on Linux (GREEN on Apple Silicon). riscv64 + arm64 are now
source-reproducible (fixed 2026-06-14: accidental boot-dir `.c` files pulled
oversized/wrong-arch runtimes into the minimal kernel via the linker's boot-dir
glob; bug `riscv64_cranelift_smf_fs_boot_regression_2026-06-14` closed). rv32 now
auto-selects the LLVM backend (cranelift has no rv32 codegen).
