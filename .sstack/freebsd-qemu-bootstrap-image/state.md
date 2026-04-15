# SStack: freebsd-qemu-bootstrap-image

## Phase 1: Dev (Intake)
- **Type:** feature
- **Goal:** Update FreeBSD QEMU image with full dev tooling (aligned with Linux/Windows install scripts), save reusable configured image, update docs, run bootstrap
- **Status:** complete

### Acceptance Criteria
- AC-1: FreeBSD `install-dev-tools.sh` section updated with `delta` (git-delta) to match Windows script
- AC-2: FreeBSD QEMU VM booted with KVM, all dev tools installed
- AC-3: Configured QEMU image saved as reusable snapshot
- AC-4: Bootstrap completes successfully on FreeBSD QEMU
- AC-5: Documentation updated (install-dev-tools.sh, qemu_manager.spl, guide docs)

### Package Alignment (Windows PS1 → FreeBSD pkg)
| Windows (winget) | Linux (apt) | FreeBSD (pkg) | Status |
|---|---|---|---|
| Git.Git | git | git | already |
| BurntSushi.ripgrep | ripgrep | ripgrep | already |
| sharkdp.fd | fd-find | fd-find | already |
| jqlang.jq | jq | jq | already |
| mikefarah.yq | yq | yq | already |
| sharkdp.bat | bat | bat | already |
| eza-community.eza | eza | eza | already |
| dandavison.delta | — | git-delta | **MISSING** |
| junegunn.fzf | fzf | fzf | already |
| Python.Python.3.12 | python3 | python3 | already |
| Kitware.CMake | cmake | cmake | already |
| Ninja-build.Ninja | ninja-build | ninja | already |
| LLVM.LLVM | clang lld | llvm lld | already |
| 7zip.7zip | p7zip-full | p7zip | already |
| GnuWin32.Make | make | gmake | already |
| — | strace | — | N/A on FreeBSD (use dtrace/truss) |
| — | — | truss | FreeBSD native |

## Phase 2: Research — pending
## Phase 3: Arch — pending
## Phase 4: Spec — pending
## Phase 5: Implement — complete

### Bootstrap Results (FreeBSD 14.4, Cranelift backend)
- **Stage 1 (Rust seed):** 4m59s, 24MB ELF binary
- **Stage 2 (seed → bootstrap_main):** 5.7s, 275 compiled, 9006 KB
- **Stage 3 (self-host verify):** 5.6s, 275 compiled, 9006 KB
- **Hash match:** `aa15d7de...857c0c5c` (deterministic)
- **Stage 4 (full CLI main.spl):** 6.7s, 334 compiled, 23762 KB
- **Binary:** `bin/release/x86_64-unknown-freebsd-elf/simple` (23MB)
- **Version:** Simple v0.9.5

### Files Modified
- `scripts/install-dev-tools.sh` — Fixed FreeBSD package names, added git-delta
- `src/app/vm/qemu_manager.spl` — Updated image path to 14.4 configured
- `~/vms/freebsd/start-freebsd-daemon.sh` — Updated to 14.4 image, 4G RAM
- `~/vms/freebsd/start-freebsd.sh` — Updated to 14.4 image
- `bin/release/x86_64-unknown-freebsd-elf/simple` — New bootstrap binary

## Phase 6: Refactor — skipped (operational task)
## Phase 7: Verify — complete (hashes match, version confirmed)
## Phase 8: Ship — pending
