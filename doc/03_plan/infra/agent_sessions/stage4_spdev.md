# Lane: Stage 4 / `$sp_dev`

Goal: complete the pure-Simple x86_64 Stage 4 bootstrap, verify the exact fresh
CLI, and deploy it only after the bounded essential-tools smoke passes.

## Current state (2026-08-02)

- Stage 3 incremental refresh passes and normally reuses 724/727 cached units.
- Stage 4 reaches HIR lowering without the former `vulkan_backend.spl` parser
  ambiguity or phase-3 segmentation fault.
- The native `Dict.len() == -1` compatibility bug is handled by counting typed
  HIR dictionary keys.
- Fatal HIR errors stop before failed-module retention, preventing the former
  20-minute / 15.8-GiB post-HIR runaway.
- The latest bounded continuation fixed and pushed the cache-stat owner,
  shell/process owner family, and async random-access file owner through
  `180e4179c1a9`. Its three Stage 4 cycles advanced the HIR frontier from 395
  to 424 modules and proved each preceding blocker cleared.
- The invalid MIR convenience re-export is removed and Stage 3 was rebuilt
  from its admitted Stage 2 compiler: 724 compiled, 0 failed; identity,
  unsupported-command, frontend admission, and hash-stability gates passed at
  SHA-256 `adc4da69b802113f17980b88b783fe7ae6cfc1830ea93b6a660b51c68a2aba91`.
  The final Stage 4 cycle still reproduced the same three aliases at
  `target_family.spl` after 423 HIR declarations. This proves directory-package
  sibling registration is leaking each sibling's named imports into unrelated
  children; the compiler resolver itself is now the blocker.
- No fresh Stage 4 CLI has passed sanity or the essential-tools smoke, and no
  artifact has been deployed.

## Required next run

1. Fetch/rebase current `main` and preserve the existing Stage 3/native cache.
2. Fix `resolve_package_sibling_symbols` so directory siblings contribute their
   own public declarations and explicit exports, but not unrelated named
   imports. Preserve normal explicit/glob import behavior and add a behavioral
   mini-package regression.
3. Refresh Stage 3 incrementally because compiler sources changed.
4. Run one full-resource Stage 4 cycle with the progress/RSS watcher.
5. On a distinct failure, claim it in the bug DB, fix pure-Simple first, add
   exact and adjacent regression coverage, push, and retry within the
   three-cycle session cap.
6. On success, run sanity and
   `scripts/check/check-bootstrap-essential-tools-smoke.shs` against the exact
   fresh Stage 4 binary. Require test-runner, lint, duplicate-check, and
   aggregate PASS markers.
7. Deploy only that verified binary, record its path and hash, and update this
   document with the retained logs and evidence.

### Manual Stage 3 refresh invariant

Do not build `src/app/cli/main.spl` directly with a bootstrap-stage compiler and
call that result Stage 3. Stage 3 is the bootstrap compiler entry
`src/app/cli/bootstrap_main.spl`, built with `SIMPLE_NO_STUB_FALLBACK=1` and the
canonical runtime/provenance authority. A manual refresh is admitted only when
all of these checks pass:

- the build log contains no `Generating [1-9][0-9]* stub functions`,
  `FAILED FILES`, or `Build failed:` marker;
- `--version` prints exactly `simple-bootstrap 1.0.0-beta`;
- `run scripts/check/cert/redeploy_gate/fixtures/p2_add.spl` exits 1 and reports
  `unknown command 'run'`;
- the canonical candidate frontend admission passes without changing the
  candidate hash.

`Build complete: ... 0 failed` and executable-file existence are insufficient
admission evidence. A stub-bearing full-CLI debug artifact can satisfy both,
yet silently fall through for `run`/`-c` and then produce an empty Stage 4 MIR.

## Exact fresh-candidate verification and deployment

The smoke accepts the candidate as its sole positional argument:

```bash
sh scripts/check/check-bootstrap-essential-tools-smoke.shs /absolute/path/to/stage4/simple
```

The bootstrap-equivalent form is
`SIMPLE_BINARY=/absolute/path/to/stage4/simple sh scripts/check/check-bootstrap-essential-tools-smoke.shs`.
Do not pass both forms with different paths. Require all four markers:
`essential_test_runner_smoke=true`, `essential_lint_smoke=true`,
`essential_duplicate_checker_smoke=true`, and
`bootstrap_essential_tools_smoke=true`. The script also rejects Rust-seed and
debug identities before running tool probes.

The canonical build/deploy command is
`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-cli --deploy`; it runs
candidate sanity, redeploy gate, essential-tools smoke, and provenance checks
before installation. Deployment copies the previous release binary to
`bin/release/<platform>/simple.pre_deploy`, installs the candidate, and restores
that backup automatically if the post-swap `-c 'print(1+1)'` smoke fails. On a
later manual rollback, restore that `.pre_deploy` file only if it still exists
and passes the same smoke; the successful deploy path intentionally deletes it.

## Performance evidence

- Stage 4 remains effectively single-core during frontend/HIR work.
- Recent fail-fast runs reach about 6.5--6.8 GiB RSS at 150 seconds.
- Whole-compiler cache identity can force 727/0 rebuilds; relaxing it remains
  unsafe until canonical complete MIR fingerprints and ordered direct
  dependency-interface hashes exist.
- Accepted optimizations remove redundant path canonicalization, deduplicate
  physical Phase-1 queue work, skip irrelevant facade-hint splits, and compact
  proven-unused retained implementation metadata.

## Post-x86 CPU/platform acceptance matrix

Run these only after the x86_64 Linux Stage 4 candidate passes its exact-binary
smoke. Merge owner is the primary Codex integration agent; final reviewer is a
normal/highest-capability Codex. Native bootstrap PASS requires the named host;
cross-object or QEMU rows are not substitutes unless explicitly stated.

| Acceptance ID | Platform / availability here | Canonical resume command | Prerequisites and retained artifacts |
|---|---|---|---|
| `ST4-PLAT-A64-LINUX` | AArch64 Linux; native host unavailable | `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=llvm --mode=dynload --full-bootstrap --full-cli --jobs=2` on AArch64 Linux | LLVM 18, C toolchain, Rust bootstrap prerequisites. Retain `build/bootstrap/stage3/aarch64-unknown-linux-gnu/simple`, `build/bootstrap/full/aarch64-unknown-linux-gnu/simple`, logs, hashes, and essential-tools markers. Current x86 Linux may run cross architecture gates, but not claim native bootstrap PASS. |
| `ST4-PLAT-MAC` | macOS x86_64/AArch64; host unavailable | `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=llvm --mode=dynload --full-bootstrap --full-cli --jobs=2` on macOS | Xcode CLI tools, Homebrew LLVM 18, coreutils and freetype. Retain matching `stage3/<triple>/simple`, `full/<triple>/simple`, logs, hashes, and smoke markers. |
| `ST4-PLAT-WIN` | Windows x86_64; host unavailable | `bash scripts/bootstrap/bootstrap-windows.sh --msvc --backend=llvm --mode=dynload --full-bootstrap --no-mcp --jobs=2` in Git Bash/MSYS2 | MSVC-compatible LLVM 18, Rust, Git Bash/MSYS2, `cygpath`; set linker flavor through the wrapper. Retain `build/bootstrap/stage3/x86_64-pc-windows-msvc/simple.exe` and logs. Full-CLI/deploy is currently restricted to Linux/macOS, so do not add it. |
| `ST4-PLAT-FREEBSD` | FreeBSD x86_64; safely runnable from this Linux host through QEMU | `sh scripts/check/check-freebsd-bootstrap-qemu.shs --full --download` | `qemu-system-x86_64`, qemu-utils, genisoimage, SSH key/client, rsync, xz; wrapper provisions FreeBSD 14.4 and guest LLVM/Rust dependencies. Retain `build/freebsd/bootstrap-logs/`, VM evidence, and guest `build/bootstrap/stage3/x86_64-unknown-freebsd/simple`. Never invoke the FreeBSD seed script directly on Linux. |
| `ST4-PLAT-SIMPLEOS-X64` | SimpleOS x86_64; safely host-driven from this Linux host | `sh scripts/bootstrap/bootstrap-from-scratch.sh --target=simpleos-x86_64 --output=build/bootstrap --jobs=2` | A verified host `bin/simple`, SimpleOS cross toolchain/QEMU prerequisites. Retain staged guest artifacts under `build/bootstrap` plus the emitted manifest/logs; this is a target lane, not a hosted full CLI. |
| `ST4-PLAT-SIMPLEOS-A64` | SimpleOS AArch64; safely buildable/QEMU-checkable from Linux after x86 acceptance | `sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` | Verified native compiler, LLVM backend, QEMU AArch64, frozen-source admission. Retain `build/os/fat32-arm64-desktop.img`, attestation manifest, logs, and follow with `check-simpleos-arm64-qmp-input-evidence.shs` when live input evidence is required. |
| `ST4-CPU-RISCV64` | Hosted RISC-V64 bootstrap host unavailable; cross/QEMU gates available here | `sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` | `riscv64-linux-gnu-gcc`, `qemu-riscv64`, RISC-V sysroot. Retain matrix evidence; this proves scoped cross execution/SIMD contracts, not a full hosted Stage 4 bootstrap. |
| `ST4-CPU-RISCV32` | Hosted target unsupported | Use the repository architecture gate for `riscv32-unknown-none-elf`; do not request `riscv32-unknown-linux-gnu` | RISC-V cross compiler/readelf. Retain ELF32/RISC-V attribute evidence. Bare-metal object acceptance only. |

Current host inventory (2026-08-02): Linux x86_64 with QEMU x86_64/AArch64/
RISC-V64 and AArch64/RISC-V64/MinGW cross compilers available. Therefore the
FreeBSD QEMU, SimpleOS host-driven, and scoped AArch64/RISC-V cross rows are safe
after x86 PASS; native Linux AArch64, macOS, Windows, and hosted RISC-V remain
external-host handoffs.

## Ownership

The parallel lane split, merge owner, and final reviewer are recorded in
`doc/03_plan/agent_tasks/stage4_spdev.md`.
