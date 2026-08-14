# SimpleOS Toolchain Self-Host Bootstrap — Parallel Lane Plan

Status: ACTIVE / WARN (restart12 implementation blocked after three cycles;
plan acceptance reviewed 2026-08-14)
Scope: 4 goals — (G1) Simple compiler/interpreter/loader on SimpleOS,
(G2) clang-for-SimpleOS recheck + in-guest hello-world smoke,
(G3) in-QEMU clang bootstrap + ormastes llvm-project fork,
(G4) Simple self-bootstrap on SimpleOS.
Written to be implementable lane-by-lane by a Sonnet-class agent working alone.
Companion tldr: `toolchain_selfhost_bootstrap_plan_tldr.md`.

## 0. Ground truth (verified 2026-08-06, do not re-derive)

Arch decision: **x86_64 primary** (only arch with proven OVMF-pflash real-firmware
proxy, working in-guest clang `-cc1` ladder, KVM accel, and a designated board plan
`hw_qemu/clang_board_bringup_x86_64_uefi.md`). **riscv64 secondary** (OpenSBI proxy
is automatic, but the on-hand ML Carrier board has 64 MiB RAM — cannot host clang;
Simple-payload lane only). **aarch64 deferred** — filed blockers:
`doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`
(no EFI-stub/PE header, seed arm64 miscompile, single-sector virtio-blk).
Board-runnable status per `.claude/rules/board-runnable.md`: x86_64 board path is
**explicitly blocked** on (a) mini-PC not purchased (P0.3) and (b) physical NIC
driver gap (only virtio-net exists). These stay filed, visible, and non-silent;
every lane below is QEMU-with-real-firmware until they clear.

| Fact | State | Where |
|---|---|---|
| In-guest Simple interpreter hello (x86_64 OVMF, arbitrary program) | PROVEN at `fe9fbd8c2285` via `simpleos_tool` payload; artifacts absent today | `scripts/os/ssh_simple_hello_uefi.shs` (L4b) |
| In-guest clang `-cc1` compile → byte-exact `.o` → exit 7 | PROVEN at `7cf0b6aec3a`; cross clang/lld binaries absent today | `scripts/os/scp_retrieve_over_ssh_uefi.shs` |
| `bin/release/{x86_64,riscv64}-unknown-simpleos/` | EMPTY (no aarch64 dir) | filesystem |
| `build/os/llvm/cross-x86_64-unknown-simpleos/` | CMakeCache only — **no bin/, no build.ninja** | filesystem |
| `build/os/clang_static/` | ABSENT | filesystem |
| LLVM fork | EXISTS: `github.com/ormastes/llvm-project` branch `simpleos`, checkout `/home/ormastes/llvm-project` (Clang 20, ~9 SimpleOS commits) | `src/os/port/llvm/build.spl:70` |
| Fork pin | RESOLVED 2026-08-06 (lane F1): fork tip and pin both `596122063`. The 30 uncommitted freestanding-ification files that existed only on local disk are now committed and pushed. | `src/os/port/llvm/build.spl:71` |
| Sysroot | EXISTS: `build/os/sysroot/` (crt0.o, libsimpleos_c.a, libc++.a, ~35 headers, `simpleos.ld` ENTRY `_start` @0x40000000, static-only) | `src/os/port/llvm/sysroot.shs` |
| lld in-guest link ladder | AUTHORED, NEVER EXECUTED (rungs 3–6, `PREPARED-POSTPONED`) | `scripts/os/ssh_lld_link_uefi.shs`, `doc/03_plan/os/in_guest_lld_link_ladder.md` |
| Guest FS | FAT32 **root-directory-only, 8.3 names** (LFN parsed, no subdir traversal) | `src/os/kernel/fs/fat32.spl` |
| fork/exec | In kernel dispatch (Fork 57 / Exec 59), **absent on the ring-3 FS-exec clang path** — `-cc1` only, no driver, no make/ninja | `src/os/kernel/ipc/syscall_process.spl`, selfhost plan |
| SMF loader | Code-complete (envelope-first), **zero in-guest usage = unproven** | `src/os/kernel/loader/smf.spl`, `host_os_completeness_plan.md:77` |
| Memory layout (load-bearing) | kernel 128 MB link base, `.bss` `[0x08000000,~0x16400000)`; ring-3 link `0x40000000`; mmap `0x50000000`; clang lanes need `QEMU_MEM=2G`+ | `linker_128mb.ld`, `src/os/kernel/ipc/syscall.spl` |

Open defects that gate lanes (fix-or-route-around, never mask):
- **D1** `deployed_selfhost_env_set_miscompile_segv_2026-07-14.md` — deployed
  `bin/release/simple` SEGVs on `native-build`; cross-build scripts default to it.
  Route-around: build payloads with `src/compiler_rust/target/bootstrap/simple`
  (`SIMPLE_BUILD_COMPILER=` override) until a healthy redeploy lands.
- **D2** #99 seed-cranelift enum miscompile — blocks in-guest U-mode Simple RUN of
  the *full CLI* on all arches (focused `simpleos_tool` payload dodges it).
- **D3** freestanding landmine family: module-global array initializers never run,
  `rt_string_join` fault, `text_index_of` nil — see
  `simpleos_freestanding_nil_array_init_optimizer_guard_fold.md` and
  `doc/07_guide/os/baremetal_simple_codegen_landmines.md`. Guest-run Simple code
  uses index loops, not `[s:e]`+`join` (proven lesson).
- **D4 (doc bug, fix in G2)** `doc/07_guide/os/simpleos_llvm_toolchain.md` claims
  prebuilt cross clang-20/lld exist — stale; contradicted by filesystem.

## 1. Dependency graph

```sdn
graph: {
  C1_llvm_cross_build: []            # long pole — start first
  S1_simple_payload:   []            # parallel with C1
  F1_fork_pin_sync:    []            # parallel, tiny
  C2_doc_fix:          []            # parallel, tiny
  S2_install_image:    [S1_simple_payload]
  S3_smf_loader_proof: [S2_install_image]
  S4_riscv64_staging:  [S1_simple_payload]
  C3_cc1_ladder_rerun: [C1_llvm_cross_build]
  C4_lld_link_ladder:  [C1_llvm_cross_build, C3_cc1_ladder_rerun]
  C5_smoke_matrix:     [C4_lld_link_ladder]
  B1_selfcompile_witness: [C3_cc1_ladder_rerun]
  B2_fs_subdir:        []            # parallel infra
  B3_forkexec_path:    []            # parallel infra
  B4_full_selfbuild:   [B1_selfcompile_witness, B2_fs_subdir, B3_forkexec_path, C4_lld_link_ladder]
  P1_simple_emit_obj:  [S2_install_image, C4_lld_link_ladder]
  P2_simple_selfhost:  [P1_simple_emit_obj]
}
```

Maximum parallelism at t0: **C1 + S1 + F1 + C2 + B2 + B3** (six independent lanes).

## 2. G1 — Simple compiler/interpreter/loader on SimpleOS

### Lane S1 — rebuild the cross Simple payload (x86_64)
- Builder: `SIMPLE_BUILD_COMPILER=src/compiler_rust/target/bootstrap/simple` (D1
  route-around; the deployed self-hosted binary SEGVs on native-build).
- Run: `sh scripts/os/simpleos-native-build.shs` (env `SIMPLE_BOOTSTRAP=1
  SIMPLE_NO_STUB_FALLBACK=1`, `native-build --target x86_64-unknown-simpleos`).
- Accept: `bin/release/x86_64-unknown-simpleos/simple` exists, static ET_EXEC,
  entry `0x40000000`, readelf gate in the script passes, ~4 MB.
- Sonnet notes: do NOT "fix" the build by switching to the deployed binary; if the
  bootstrap seed also fails, file the exact error against D1 and stop the lane.

### Lane S2 — install-image contract + live in-guest gate
- Build image: `sh scripts/os/build_simpleos_install_image.shs` (`disk` profile,
  x86_64) — must embed `/usr/bin/simple(.smf)`, `/bin/simple(.smf)`,
  `/sys/apps/simple{,_compiler,_interpreter,_loader}(.smf)`, `/SYS/SIMPLETOOL.SDN`
  per `simpleos_baremetal_board_support.md:75-112`. Payload = S1 artifact only —
  host `bin/simple` or marker apps are NOT pass evidence.
- Live gate: `sh scripts/os/ssh_simple_hello_uefi.shs` (OVMF pflash, never
  `-kernel`) through rung L4b: `ssh root@guest /usr/bin/simple /hello.spl` prints
  the hello line, rc=0; retain the full serial+SSH transcript under
  `build/os/transcripts/`.
- Accept: fresh L4b PASS transcript + image manifest listing all seven paths.
  Classification if only staging passes: `staging-proven`, not PASS (SPipe rule).

### Lane S3 — SMF loader in-guest proof (first real user of `smf.spl`)
- Package one tiny app (`/sys/apps/simple_loader.smf` self-test) as SMF, boot,
  exec via FS-exec, assert output. This converts the loader from
  "production-ready in code, zero usage" to proven.
- Accept: transcript showing SMF-envelope path taken (kernel log marker), app
  output correct. Add an SSpec system spec under `test/03_system/os/qemu/`
  following `qemu_systest_contract.spl` (fail-closed, never `skip()`).

### Lane S4 — riscv64 staging (secondary arch)
- `sh scripts/os/simpleos-native-build-riscv64.shs` with the same D1 builder
  override; readelf gate (EM_RISCV). In-guest run rides OpenSBI `-kernel`
  (satisfies firmware-proxy rule). Known gap: guest network runtime absent
  (`HOSTED_NETWORK_UNAVAILABLE`) — serial-console evidence instead of SSH.
- aarch64: DO NOT start; keep the filed EFI-stub/virtio-blk blockers linked here.

## 3. G2 — clang recheck + in-guest hello smoke

### Lane C1 — rebuild cross LLVM/clang/lld (LONG POLE, start immediately)

> **C1 is not done when ninja exits.** Stage 2 (`cross`) compiles all of
> clang/LLVM as `x86_64-unknown-simpleos` *objects*, but its `bin/clang-20`
> links as a **Linux dynamic ELF** (interp `/lib64/ld-linux-x86-64.so.2`) and
> CANNOT run on SimpleOS. Producing a guest-runnable clang needs one of:
> (a) the **FS-exec path** — an ordinary on-disk static
> `x86_64-unknown-simpleos` ELF at `/usr/bin/clang`, which is the intended
> design (FR-SOS-020+); or (b) `src/os/port/llvm/clang_static.shs`, a
> static-relink of the same objects that is **explicitly DEPRECATED** for
> desktop SimpleOS and kept only as a legacy fallback. Prefer (a); if (b) is
> used to unblock, label the evidence as legacy-fallback, not the design path.
> Stage 3 (`compiler-rt`) is also required — it stages target builtins into
> `build/os/sysroot/lib/clang/<ver>/lib/<triple>/`.
>
> **Concurrency hazard:** the cross build links against
> `build/os/sysroot/lib/`, and `sysroot.shs:266` rewrites `libm.a`. Never
> regenerate the sysroot while a cross build is linking — stage to a scratch
> sysroot and swap, or wait for ninja to exit.
- Pre-step: Lane F1 pin bump (below) so we build fork tip, not `3b33ba807`.
- Run: `bin/simple run src/os/port/llvm/build.spl` (host needs cmake/ninja/clang/
  python3/git; source tree `/home/ormastes/llvm-project`). Outputs:
  `build/os/llvm/cross-x86_64-unknown-simpleos/bin/{clang-20,ld.lld}` and the
  static guest binaries `build/os/clang_static/bin/{clang_static,lld_static}` +
  `build/os/.bake_include_toolchain`.
- Accept: binaries exist; `clang_static` is a static ET_EXEC ELF (~122 MB class);
  `file`/readelf receipts retained. Multi-hour build — run detached with a log,
  never inside a foreground timeout.

### Lane C2 — fix the stale toolchain guide (D4)
- Edit `doc/07_guide/os/simpleos_llvm_toolchain.md`: replace "already built"
  §Locations claims with build-required status + the C1 command; keep the
  verified-hello section but mark it commit-pinned historical until C3 re-passes.

### Lane C3 — re-run the `-cc1` compile ladder (fresh evidence)
- `SKIP_STAGE=0 SKIP_KERNEL=0 sh scripts/os/scp_retrieve_over_ssh_uefi.shs`
  (OVMF pflash, GRUB-EFI, kernel `linker_128mb.ld`, `QEMU_MEM=2G`+, KVM).
- Accept: in-guest `clang -cc1 -triple x86_64-unknown-simpleos -emit-obj` on
  `/hello.c`, `getfile` byte-exact ET_REL, host link, guest-run exit 7; full
  ladder serial transcript retained (evidence bar: transcript, never a claim).

### Lane C4 — in-guest LINK ladder (the actual "hello world on SimpleOS terminal")
- Execute the prepared-but-never-run rungs 3–6 of
  `scripts/os/ssh_lld_link_uefi.shs` per `in_guest_lld_link_ladder.md`:
  stage `lld_static` + sysroot libs (crt0.o, libsimpleos_c.a, simpleos.ld) into
  the image; in-guest `ld.lld` links `/hello.o` → `/hello`; FS-exec runs it;
  stdout observed in the SimpleOS shell.
- FAT32 constraint: all staged files 8.3 names in root (e.g. `HELLO.O`,
  `LLD.ELF`, `LIBC.A`); the no-fork constraint is satisfied because lld is
  invoked as a direct absolute-path FS-exec, not via the clang driver
  (`CLANG_SIMPLEOS_EMBED_LLD` short-circuit exists in the fork for later).
- Accept: transcript of compile (in-guest) → link (in-guest) → run (in-guest)
  printing hello on the SimpleOS terminal. This is the G2 exit criterion.

### Lane C5 — smoke matrix (after C4)
- Rows: (1) two-TU C program linked in-guest; (2) C++ hello against `libc++.a`;
  (3) static-archive link; (4) `-O0` vs `-O2` byte-compare against host cross
  compile of the same `.i`. Each row = one SSpec system spec + retained
  transcript; unavailable rows stay visible as `blocked`, never `skip()`.

## 4. G3 — fork + in-QEMU clang bootstrap

### Lane F1 — fork hygiene (tiny, do first)
- Bump `LLVM_REVISION` in `src/os/port/llvm/build.spl:71` to fork tip
  `92fa40246`; verify `git -C /home/ormastes/llvm-project fetch origin simpleos`
  is clean and local commits are pushed to `github.com/ormastes/llvm-project`
  branch `simpleos` (SSH key per memory `reference_ssh_key_for_jj`).
- Parity check: each `src/os/port/llvm/patches/00NN-*.patch.md` maps to a fork
  commit; list any patch-doc drift as findings. Accept: pin == tip, push
  verified with `git ls-remote`, parity table committed.

### Lane B1 — self-compile WITNESS (first honest bootstrap step)
- Goal: in-guest `clang_static -cc1` compiles ONE real clang/LLVM source TU.
- Method that fits FAT32-root/8.3 + no-fork: on host, preprocess a small
  LLVM TU (e.g. from `llvm/lib/Support/`) with the cross clang to a single
  self-contained `TU1.I`; stage it; in-guest `-cc1 -emit-obj -x c++ TU1.I` →
  `TU1.O`; `getfile`; byte-compare against host cross build of the same `.i`.
- Accept: byte-exact (or, if legitimately divergent, explained diff) — this is
  "clang compiling clang on SimpleOS", scoped honestly to one TU.

### Lanes B2/B3 — structural prerequisites (parallel infra, no toolchain dep)
- **B2 FS**: FAT32 subdirectory traversal + LFN create in
  `src/os/kernel/fs/fat32.spl` (read path first, write path second), or DBFS
  mount for a build volume. Without this an LLVM tree (~150k nested files)
  cannot exist in-guest. SSpec: create/read nested `A/B/C/file` in-guest.
- **B3 process**: bring Fork(57)/Exec(59) to the ring-3 FS-exec payload path so
  the clang *driver* (and later a minimal build runner) can spawn `-cc1`+lld.
  SSpec: in-guest driver-mode `clang hello.c -o hello` (driver forks cc1+lld).
- **B4 full self-build**: EXPLICITLY LONG-HORIZON. Gate: B1+B2+B3+C4 green,
  plus sizing (guest needs ≥8 GB RAM / ~20 GB disk; current lanes run 2–4 GB).
  Build system: no cmake/ninja port — generate a flat response-file build script
  on host (list of `-cc1`+lld invocations) and replay it in-guest via shell.
  Until B4 passes, all "clang bootstrap on SimpleOS" claims are scoped to B1.

## 5. G4 — Simple self-bootstrap on SimpleOS

### Lane P1 — in-guest Simple compile-to-native hello
- Route: `simpleos_tool` payload's `--emit-object` (LLVM adapter emits `.o`
  before the external-link step — `llvm_native_link.spl:2801` shells to
  `ld.lld`, which after C4 EXISTS in-guest as `lld_static`). In-guest:
  `/usr/bin/simple --emit-object /HELLO.SPL` → `/HELLO.O`; in-guest lld link
  with sysroot; FS-exec run.
- Accept: SimpleOS terminal transcript: Simple source → native binary → runs,
  all in-guest. This is "Simple compiler compiles ON SimpleOS".

### Lane P2 — Simple self-host (simple compiles simple) — staged
- Stage 1: in-guest interpreter runs a subset of the Simple compiler frontend
  over a small module (parity vs host output). Stage 2: in-guest
  `--emit-object` of a compiler module, linked in-guest. Stage 3 (full
  bootstrap) inherits B2 (FS) for the source tree and D2/D3 fixes for the full
  CLI; keep it gated and honest — payload today is interpreter+emit-object,
  never claim more.

## 6. Cross-cutting rules for every lane
- Firmware proxy always: OVMF pflash (x86_64) / OpenSBI (riscv64); never
  `-kernel` on x86_64, never `isa-debug-exit`.
- Evidence = retained serial/SSH transcript bound to the exact artifact
  (path+SHA-256); commit-pinned historical proofs do not satisfy a fresh lane.
- Each lane lands: implementation + SSpec spec (fail-closed, `step()`-based,
  mirrored via `bin/simple spipe-docgen ... --output doc/06_spec --no-index`,
  0 stubs) + guide refresh if workflow changed + LLM wiki entry refresh.
- Guest-run Simple code: index loops not slice+join (D3); freestanding
  landmine catalog applies (`baremetal_simple_codegen_landmines.md`).
- Postponement ≠ completion: blocked rows (aarch64, physical board, B4) stay
  visible with owner, prerequisite, resume command, retained artifacts.

## 7. Restart12 deployment-image + production-desktop acceptance ledger

This section is the canonical current plan for the restart12 deployment lane.
Sections 0–6 and their paths/hashes are historical context only and confer no
PASS in restart12. In particular, a Rust-seed-built payload, fixed-command SSH
fixture, QEMU `-kernel` boot, or old transcript is not acceptance evidence.

Merge owner: `/root`. Sidecar findings: `acceptance_audit` and
`guide_trace_audit`. Separate higher-capability reviewer:
`higher_model_review`, final plan verdict PASS on 2026-08-14 after checking
acceptance completeness, blocker honesty, guide coverage, manual readability,
and done/exclusion marks. This verdict accepts plan completeness only.

| AC | Status | Authoritative evidence | Blocker / exact resume | Owner | Final reviewer |
|---|---|---|---|---|---|
| AC-1 current evidence only | PASS | This ledger; current filesystem inspection; bootstrap logs below | N/A | `/root` | `higher_model_review` |
| AC-2 admitted host compiler + pure-Simple payload | BLOCKED | Stage 2 sanity passed; Stage 3 log retained | B-STAGE3; fresh lane runs the command in its bug | compiler bootstrap | `higher_model_review` |
| AC-3 two-record image admission | BLOCKED | Frozen schemas below | needs AC-2 payload and genuine guest `ld.lld` | image owner | `higher_model_review` |
| AC-4 same-run production desktop boot | BLOCKED | canonical route frozen below | B-DESKTOP-LIVE; run wrapper below after AC-3 | desktop/QEMU owner | `higher_model_review` |
| AC-5 guest compile/link/run | BLOCKED | literal guest contract below | needs AC-2–4 | guest toolchain owner | `higher_model_review` |
| AC-6 frozen SSpec interface | PASS | exact names/text below | N/A | system-test owner | `higher_model_review` |
| AC-7 executable/manual/trace gates | BLOCKED | target paths and commands below | implementation and admitted `bin/simple` absent | system-test owner | `higher_model_review` |
| AC-8 capability matrix | PASS | matrix below | rows remain independently blocked | `/root` | `higher_model_review` |
| AC-9 bounded cycles | PASS | cycle ledger below | no fourth cycle permitted | `/root` | `higher_model_review` |
| AC-10 knowledge/blocker coverage | PASS | checklist and bug paths below | execution evidence still blocked | `/root` | `higher_model_review` |
| AC-11 cooperative review | PASS | named merge/review receipt above | N/A | `/root` | `higher_model_review` |
| AC-12 detached integration | BLOCKED | exact lifecycle below | performed only after final commit | `/root` | `higher_model_review` |

### Admission and non-circular records

Host admission records exact pure-Simple compiler path, SHA-256, source commit,
runtime authority, target triple, producer command, and validator result.
`scripts/ci/build-simpleos-toolchain.shs` is not deployment evidence while it
executes the Rust seed; the seed is bootstrap-only. Payload production must set
`SIMPLE_NO_STUB_FALLBACK=1`.

Embedded `/SYS/SIMPLETOOL.SDN` is schema
`simpleos_toolchain_deployment_manifest/v1`. It records producer/validator,
target-native static-ELF checks, SHA-256 for the admitted compiler, SimpleOS
payload, genuine guest-static `ld.lld`, `/usr/lib/SIMAIN.O`, `/HELLO.SPL`, and
kernel, plus byte-identical alias inventory:
`/usr/bin/simple(.smf)`, `/bin/simple(.smf)`,
`/sys/apps/simple(.smf)`, `/sys/apps/simple_compiler(.smf)`,
`/sys/apps/simple_interpreter(.smf)`, `/sys/apps/simple_loader(.smf)`, and
`/SYS/SIMPLETOOL.SDN`. It cannot hash its containing image.

External `simpleos_toolchain_image_admission_receipt/v1` records the final
image SHA-256, embedded-manifest SHA-256, kernel SHA-256, producer/validator,
timestamp, command, and validation signatures. Thus image admission is not
self-referential.

### Frozen boot and SSpec contract

The single canonical owner route is a new
`scripts/os/check_simpleos_toolchain_desktop_boot.shs`, launching OVMF CODE plus
per-run VARS pflash and GRUB standalone EFI into canonical
`gui_entry_desktop.spl`; `-kernel` is forbidden. One run must bind kernel/image
hashes to `[desktop-gui]`, `[production-readiness]`, `[scanout-evidence]`, a
framebuffer receipt, serial log, and SSH log. It must literally execute
`/usr/bin/simple --version`, compile `/HELLO.SPL` with embedded
`/usr/bin/ld.lld` and `/usr/lib/SIMAIN.O`, execute the mounted-filesystem ELF,
and require exact `Hello World` plus rc=0.

Executable target:
`test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl`.
Manual target:
`doc/06_spec/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.md`.
Frozen helpers are `step_prepare_toolchain_deployment_image`,
`step_boot_simpleos_desktop`, `step_compile_and_run_guest_hello`,
`prepare_toolchain_deployment_fixture`,
`require_toolchain_deployment_manifest`,
`require_simpleos_desktop_boot_receipt`, and `require_guest_hello_receipt`.
Incomplete helpers call `fail(...)`. Exact visible steps are:
`Prepare the toolchain deployment image`,
`Boot the SimpleOS production desktop`, and
`Compile and run Hello World inside the guest`.

One-time post-unblock gates:

```sh
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl
test "$(find doc/06_spec -name '*_spec.spl' -print -quit)" = ''
```

### Host/capability matrix

| Capability | State | Missing prerequisite | Exact resume command | Retained artifacts | Owner |
|---|---|---|---|---|---|
| Linux x86_64 build/admission | BLOCKED | B-STAGE3 | command in `stage3_runtime_error_static_owner_receiver_corruption_2026-08-14.md` after its unblock condition | `build/bootstrap/logs/x86_64-unknown-linux-gnu/` | compiler bootstrap |
| Linux x86_64 OVMF+GRUB desktop + guest | BLOCKED | admitted payload, linker, image, wrapper | `sh scripts/os/check_simpleos_toolchain_desktop_boot.shs` | `build/os/transcripts/`, manifests/receipts | desktop/QEMU owner |
| Physical x86_64 board | BLOCKED | purchased board identity, NIC support, live serial/SSH | `sh scripts/os/check_simpleos_toolchain_physical_boot.shs --board-id <inventory-id> --image <admitted-image>` (safe wrapper must validate removable target before imaging) | board identity + serial/SSH transcript | board owner |
| aarch64/riscv64 | BLOCKED / out of this lane | architecture-specific firmware/toolchain prerequisites | commands remain in their linked architecture plans | their own build trees | architecture owners |

QEMU never satisfies the physical row. Unavailable rows remain active and are
never silently excluded or skipped.

### Global fix/verify cycle ledger and stop rule

Attempt 1 exposed the missing typed parser contract owner. Attempt 2 passed
Stage 2 and failed Stage 3 on fourteen folded-constant type recoveries. Attempt
3 passed Stage 2, proved those errors absent, and then exited 139 at the new
`runtime_error` static-owner frontier. All three feature-wide cycles are
consumed. No unchanged green criterion or identical failed command may rerun.

PASS requires fresh authoritative evidence for AC-1 through AC-12. WARN is
allowed only after at most three cycles with every unresolved item retained as
BLOCKED, a bug and exact resume condition recorded, and no deployment/desktop
done or release claim.

### Knowledge and blocker checklist

Current anchors: local/domain research and feature/NFR requirements for
`simpleos_filesystem_toolchain_servers`; architecture/detail design and sys-test
plan of the same name; this plan; the deployment SSpec/manual targets above;
`simpleos_llvm_toolchain.md`, `simpleos_x86_64_wm_qemu.md`,
`simpleos_board_bringup.md`, `qemu_system_tests.md`, and
`simpleos_baremetal_board_support.md`; feature expert
`simpleos_toolchain_selfhost/skill.md`; layer experts `llvm_toolchain_port`,
`os_kernel_exec`, and `compiler_driver`. Refresh each when its workflow or
evidence changes. Workflow skill/command docs are N/A unless their contract
changes; generated manuals are mandatory.

Current blockers are B-STAGE3
(`stage3_runtime_error_static_owner_receiver_corruption_2026-08-14.md`),
B-DESKTOP-LIVE (missing combined wrapper/receipt, owner route specified above),
and B-PHYSICAL (board-support guide physical-board prerequisites). Each remains
BLOCKED until its stated command produces hash-bound evidence.

### Exact detached-worktree integration lifecycle

Run fail-fast while holding the lock across the entire sequence:

```sh
set -eu
exec 9>/tmp/simple-main-restart12-push.lock
flock 9
git fetch origin main
git rebase origin/main
env -u GH_TOKEN -u GITHUB_TOKEN git push origin HEAD:main
git fetch origin main
git merge-base --is-ancestor HEAD origin/main
test -z "$(git status --porcelain)"
hash=$(git rev-parse HEAD)
tmp=/tmp/restart12-simpleos.done.tmp.$$
printf '%s WARN\n' "$hash" >"$tmp"
mv "$tmp" /tmp/restart12-simpleos.done
```

Never force-push and never create a branch. The receipt is absent until the
push is reachable and the tree is clean.
