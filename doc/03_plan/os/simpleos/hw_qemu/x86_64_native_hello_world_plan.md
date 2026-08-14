# SimpleOS x86_64 Toolchain Deployment Image and Desktop Boot Plan

Date: 2026-08-14

Status: ACTIVE — implementation-ready; no fresh acceptance PASS
SPipe state: `.spipe/simpleos-toolchain-deployment-desktop-boot/state.md`

## Objective

Build a strict x86_64 SimpleOS deployment image, boot it through the production
OVMF/GRUB desktop path, and prove that the image-embedded Simple toolchain
compiles and executes exact `Hello World` inside the guest.

Historical paths and hashes in this document are context only. They confer no
PASS in the restart12 worktree.

## Ownership and cooperative review

- Worktree and merge owner: Codex root lane.
- Sidecar A: acceptance, evidence, blocker, and lifecycle audit — completed and
  merged into this revision.
- Sidecar B: guide, knowledge, SSpec/manual, and traceability audit — completed
  and merged into this revision.
- Final reviewer: a separate higher-capability Codex model after merge.
- Generated-manual reviewer: the same separate higher-capability reviewer.
- Unrelated work and artifacts from other worktrees/sessions remain out of
  scope and must not be committed or used as evidence.

Review acceptance covers criterion completeness, blocker honesty, guide and
wiki coverage, generated-manual usability, and every done/exclusion mark. The
review receipt and verdict are recorded in `Review record` below.

## Fresh restart12 state

At lane start these required outputs were absent:

- `bin/release/x86_64-unknown-simpleos/simple`
- `build/os/clang_static/bin/lld_static`
- `build/os/llvm/cross-x86_64-unknown-simpleos/bin/ld.lld`
- `build/os/simpleos_ssh_ring3_uefi128_laneb.elf`
- `build/os/elfexec_simple/fat32-simple.img`
- current serial/SSH receipts

A single strict bootstrap attempt with fallback disabled produced admitted
Stage 2 at
`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`, SHA-256
`c7dfde4387f172af527bb37eb3740c1aed9eeeaa20648c0f653e3a6897003c7c`.
Stage 3 failed closed at
`src/compiler/mir_opt/mir_opt/typed_storage_view_producer.spl:132-133` because
the admitted compiler rejects that multiline `and` condition. Diagnostics are
retained at
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

Stage 2 is bootstrap-only. It is not a Stage 4 CLI, SPipe runner, deployment
payload, or acceptance evidence. The historical
`plan_synthetic_driver_registration` nil-receiver defect is documented as
source-fixed but not redeployed; do not assume it is the current blocker
without a fresh focused reproducer.

## Current blockers

1. **B-HOST-CLI:** no admitted Stage 3 and Stage 4 pure-Simple host CLI. Resume
   by fixing the recorded Stage 3 parser/source incompatibility at its owner,
   continuing the strict bootstrap, and running candidate admission plus the
   Stage 4 essential-tools smoke once.
2. **B-TARGET-SIMPLE:** no fresh strict
   `x86_64-unknown-simpleos/simple`. Resume after B-HOST-CLI with the AC-2
   command below.
3. **B-GUEST-LLD:** no genuine static x86_64 SimpleOS `ld.lld`. Resume with the
   pinned LLVM fork build; host Mach-O/Linux binaries and wrappers are invalid.
4. **B-IMAGE:** no manifest-bound kernel/deployment image containing the exact
   admitted payload, linker, runtime input, source, and canonical aliases.
5. **B-DESKTOP-LIVE:** no fresh OVMF/GRUB serial plus SSH transcript for version,
   compile, link, mounted-filesystem execution, exact output, and exit status.
6. **B-SPEC:** the existing deploy-image spec proves negative/source contracts
   only. The existing live spec uses raw runtime externs, `isa-debug-exit`, an
   opt-in false branch that can green without execution, and a Clang/Rust flow.
   Neither is full acceptance for this plan.
7. **B-PHYSICAL:** no purchased mini-PC/identity/live transcript and no physical
   NIC driver beyond virtio-net. This blocks a physical-board claim, not an
   explicitly QEMU-only result.

Every newly unresolved gap gets a `doc/08_tracking/bug/` record naming the
owner file/line and unblock condition. No blocker may be bypassed with a Rust
seed target build, host linker, marker payload, fixed-command SSH response,
QEMU `-kernel`, `isa-debug-exit`, or historical artifact.

## Frozen implementation and manual interfaces

- Deployment manifest: `simpleos_toolchain_deployment_manifest`.
- External image receipt: `simpleos_toolchain_image_admission_receipt`.
- Manual flow helpers:
  `step_prepare_toolchain_deployment_image`,
  `step_boot_simpleos_desktop`,
  `step_compile_and_run_guest_hello`.
- Setup/checkers:
  `prepare_toolchain_deployment_fixture`,
  `require_toolchain_deployment_manifest`,
  `require_simpleos_desktop_boot_receipt`,
  `require_guest_hello_receipt`.
- Any incomplete helper calls `fail(...)`; no no-op, skip, placeholder pass, or
  assertion that an opt-in is false is allowed.

The visible manual steps are frozen exactly as:

- `step("Prepare the toolchain deployment image")`
- `step("Boot the SimpleOS production desktop")`
- `step("Compile and run Hello World inside the guest")`

The embedded manifest is `/SYS/SIMPLETOOL.SDN`, schema
`simpleos-toolchain-deployment-v1`. Its producer is the install-image builder;
its validator is `require_toolchain_deployment_manifest`. It records path,
SHA-256, byte size, provenance, and applicable ELF class/machine/type, entry,
and `PT_INTERP` state for:

- admitted host compiler and its admission receipt;
- target Simple payload;
- genuine guest-static `ld.lld`;
- `/usr/lib/SIMAIN.O`;
- `/HELLO.SPL` source bytes;
- kernel.

It cannot hash its enclosing image. The external receipt is
`build/os/evidence/simpleos-toolchain-image-admission-v1.sdn`, schema
`simpleos-toolchain-image-admission-v1`, produced only after the image closes
and validated by `require_simpleos_desktop_boot_receipt`. It records producer
version, validator version, source commit, embedded-manifest SHA-256, final
image path/size/SHA-256, kernel SHA-256, OVMF CODE hash, per-run VARS hash,
GRUB EFI hash, QEMU argv hash, serial/SSH receipt paths and hashes, timestamp,
and reviewer status. Both SDN records use sorted canonical keys and end with a
`record_sha256` over the canonical record excluding that field; the external
receipt is the non-circular admission signature.

It proves byte identity for these required image identities; `.smf` sidecars
are allowed only where shown:

- `/usr/bin/simple(.smf)`
- `/bin/simple(.smf)`
- `/sys/apps/simple(.smf)`
- `/sys/apps/simple_compiler(.smf)`
- `/sys/apps/simple_interpreter(.smf)`
- `/sys/apps/simple_loader(.smf)`
- `/SYS/SIMPLETOOL.SDN`
- `/usr/bin/ld.lld`
- `/usr/lib/SIMAIN.O`
- `/HELLO.SPL`

## AC-1..AC-12 acceptance and evidence ledger

No row is fresh PASS today.

| AC | Status | Authoritative evidence | Blocker / exact resume | Owner | Final reviewer |
|---|---|---|---|---|---|
| AC-1 current truth | BLOCKED | Current paths, hashes, retained logs; historical section labeled non-PASS | Refresh ledger after each artifact is produced | root | higher-capability reviewer |
| AC-2 admitted compiler and target payload | BLOCKED | Exact compiler path/hash/admission; strict build log; target ELF/readelf/nm receipt | Finish B-HOST-CLI, then `SIMPLE_BUILD_COMPILER=<admitted-stage4> SIMPLE_NO_STUB_FALLBACK=1 sh scripts/os/simpleos-native-build.shs --target x86_64-unknown-simpleos` | root/bootstrap owner | higher-capability reviewer |
| AC-3 deployment records | BLOCKED | Embedded `simpleos_toolchain_deployment_manifest` plus external `simpleos_toolchain_image_admission_receipt`, both v1 and hash-validated | Complete payload, guest linker, kernel, and image staging | root/image owner | higher-capability reviewer |
| AC-4 production desktop boot | BLOCKED | Same-run `gui_entry_desktop.spl` receipt: QEMU argv, OVMF CODE/per-run VARS, GRUB standalone EFI, kernel/image hashes, `[desktop-gui]`, `[production-readiness]`, `[scanout-evidence]`, framebuffer proof, serial and SSH paths | Implement and run the frozen combined owner `scripts/check/check-simpleos-toolchain-desktop-boot.shs`; it builds `gui_entry_desktop.spl`, boots once, retains the guest, captures desktop evidence, runs guest toolchain commands, and then shuts down. `ssh_simple_hello_uefi.shs` alone is insufficient; forbid `run_simpleos_qemu.shs` (`-kernel`) | root/QEMU+desktop owner | higher-capability reviewer |
| AC-5 in-guest Simple compile/run | BLOCKED | Literal guest commands, stdout/stderr, output ELF hash/identity, exact `Hello World`, rc=0 | Extend live wrapper beyond its current interpreter proof | root/toolchain owner | higher-capability reviewer |
| AC-6 frozen SSpec flow | BLOCKED | `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl` with all frozen names and fail-closed helpers | Implement after wrapper/manifest contract lands | root/spec owner | higher-capability reviewer |
| AC-7 operator manual and traceability | BLOCKED | Mirror at `doc/06_spec/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.md`; AC/REQ matrix; seven `sspec-maintain` scores; zero stubs/layout bugs | Generate from executable spec and review as a manual | root/doc owner | higher-capability reviewer |
| AC-8 host/capability honesty | BLOCKED | Host matrix below with receipt or linked blocker for every row | Complete Linux QEMU row; retain physical row BLOCKED | root | higher-capability reviewer |
| AC-9 bounded convergence | BLOCKED | Cycle ledger below; no repeated green or identical failed command | Stop on convergence or third distinct failed fix/verify cycle | root | higher-capability reviewer |
| AC-10 knowledge freshness | BLOCKED | Checklist below plus blocker records with file/line/unblock condition | Update affected artifacts with implementation | root/doc owner | higher-capability reviewer |
| AC-11 cooperative review | BLOCKED | Both sidecar receipts plus separate final review receipt/verdict | Run final review after this merge | root merge owner | separate higher-capability reviewer |
| AC-12 integration lifecycle | BLOCKED | Commit, lock/fetch/rebase/push/fetch/ancestor proof, clean tree, done receipt | Execute only after plan review acceptance | root | user-authorized push lifecycle |

PASS means every AC has fresh authoritative evidence. WARN is allowed only
after no more than three distinct cycles, with each unresolved AC still marked
BLOCKED and linked to an owner, bug, resume command, and retained artifact. WARN
is not a done, verify PASS, release, or feature-completion claim.

## Host and capability matrix

| Row | State | Missing prerequisite | Resume command | Retained artifacts | Owner / reviewer |
|---|---|---|---|---|---|
| Linux x86_64 Stage 3/4 admission | BLOCKED ([B-HOST-CLI](../../../../08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md)) | Stage 3 parser/source compatibility and Stage 4 CLI | After a source fix, use the single materially changed attempt `env SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh --full-cli --no-mcp --backend=llvm --jobs=min`; it builds and admits Stage 3, then continues through Stage 4 without a separate unchanged-green Stage 3 rerun. Then run `sh scripts/check/check-bootstrap-platform-handoff-readiness.shs` with Gate 1-5 receipts | bootstrap logs, candidate/provenance/admission/handoff receipts | bootstrap owner / higher-capability reviewer |
| Linux x86_64 OVMF+GRUB production desktop + guest toolchain | BLOCKED ([B-DESKTOP-LIVE](../../../../08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md)) | payload, guest linker, two-record image admission, frozen combined wrapper | `SIMPLE_BIN=<admitted-stage4> SIMPLEOS_TOOLCHAIN_IMAGE=<admitted-image> SIMPLEOS_WM_READINESS_TIMEOUT_MS=900000 sh scripts/check/check-simpleos-toolchain-desktop-boot.shs`; the wrapper owns one `gui_entry_desktop.spl` QEMU lifetime from boot through guest receipt | embedded manifest, external receipt, QEMU argv, serial, framebuffer/readback, SSH transcript, output ELF | root / higher-capability reviewer |
| Physical x86_64 board | BLOCKED ([B-PHYSICAL](../../../../08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md)) | board acquisition/identity, physical NIC driver, boot/download route | Build/check: `sh scripts/os/build-simpleos-x86_64-board-usb.shs && sh scripts/check/check-simpleos-x86_64-board-usb-image.shs`. After recording the exact stable by-id path, require `SIMPLEOS_BOARD_DEVICE=/dev/disk/by-id/<reviewed-id>; test -b "$SIMPLEOS_BOARD_DEVICE"; sudo dd if=build/os/x86_64_board_usb/board-usb.img of="$SIMPLEOS_BOARD_DEVICE" bs=4M conv=fsync status=progress`; boot the named mini-PC and capture the selected evidence channel | board identity, image receipt, download log, serial or SSH transcript | board owner / higher-capability reviewer |

aarch64 and riscv64 are separate plans and outside this x86_64 deliverable;
they are not silently counted as PASS or as physical-board evidence.

## Bounded execution cycles

The feature has one shared maximum of three fix/verify cycles.

- **Feature attempt 1 (used):** strict bootstrap produced admitted Stage 2,
  then failed at the named Stage 3 parse frontier.
- **Feature attempts 2-3 (reserved):** only materially changed fixes may use
  these attempts, with changed command/input hash recorded in the blocker
  record. A downstream first execution is ordinary work, but any downstream
  fix-and-retry consumes one of these same two remaining attempts.
- After feature attempt 3, stop with WARN and retain every unresolved AC as
  BLOCKED. No blocker gains its own additional retry budget.

Never rerun an unchanged green criterion or an identical failed command.

## SPipe and operator-manual contract

The executable scenario belongs under `test/03_system/os/`; `doc/06_spec`
contains its Markdown mirror only. The manual presents the three frozen steps
in order and attaches typed evidence for:

1. manifest identities and image inventory;
2. exact QEMU argv, OVMF/GRUB markers, kernel/image hashes, canonical desktop
   `[desktop-gui]`/`[production-readiness]`/`[scanout-evidence]` markers,
   framebuffer proof, and SSH readiness from the same run;
3. guest commands, stdout/stderr, output ELF identity, exact output and rc=0.

Unavailable live prerequisites produce a fail-closed BLOCKED result linked to
this plan, never `skip()` or a green readiness-only scenario. Run the focused
spec once, generate its mirror, run `bin/simple sspec-maintain scan <spec>`
once and inspect all seven scores/blockers/mirror/traceability fields, then read
the mirror as an operator manual. Before handoff require:

```sh
test "$(find doc/06_spec -name '*_spec.spl' -print -quit)" = ""
```

## Knowledge and traceability checklist

Update these existing authorities rather than creating parallel contracts:

- local/domain research:
  `doc/01_research/{local,domain}/simpleos_filesystem_toolchain_servers.md`;
- selected feature/NFR requirements:
  `doc/02_requirements/{feature,nfr}/simpleos_filesystem_toolchain_servers.md`;
- architecture/design:
  `doc/04_architecture/simpleos_filesystem_toolchain_servers.md` and
  `doc/05_design/simpleos_filesystem_toolchain_servers.md`;
- system-test and agent plan:
  `doc/03_plan/sys_test/simpleos_filesystem_toolchain_servers.md` and
  `doc/03_plan/agent_tasks/simpleos_filesystem_toolchain_servers.md`;
- broader self-host plan:
  `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`;
- guides:
  `doc/07_guide/os/simpleos_llvm_toolchain.md`,
  `doc/07_guide/platform/simpleos/simpleos_x86_64_wm_qemu.md`,
  `doc/07_guide/platform/simpleos/qemu_system_tests.md`, and
  `doc/07_guide/platform/simpleos/simpleos_baremetal_board_support.md`;
- feature/layer knowledge:
  `doc/00_llm_process/feature_expert/simpleos_toolchain_selfhost/skill.md`,
  `doc/00_llm_process/layer_expert/llvm_toolchain_port/skill.md`,
  `doc/00_llm_process/layer_expert/os_kernel_exec/skill.md`, and
  `doc/00_llm_process/layer_expert/compiler_driver/skill.md`;
- blocker records: the existing deployed-ABI, native-emit, and in-guest
  execution records, plus dedicated records for any still-missing admitted
  compiler, guest linker/manifest, or live-receipt defect.

Workflow skill/command docs are N/A unless implementation changes their
contract. The generated manual and operator guides are always required.

## Implementation sequence

1. Resolve B-HOST-CLI at the pure-Simple owner boundary; admit Stage 3 and an
   exact Stage 4 CLI, then run the bounded essential-tools gate once.
2. Build the target payload from that admitted CLI with fallback disabled; bind
   compiler/payload provenance and strict ELF evidence.
3. Build genuine guest-static `ld.lld` from the pinned fork and retain compiler,
   validator, hash, readelf, and dependency receipts.
4. Stage every manifest identity, build the kernel/image, and make manifest
   validation fail before boot on any missing, stale, wrong-target, or
   non-byte-identical input.
5. Implement the frozen combined wrapper
   `scripts/check/check-simpleos-toolchain-desktop-boot.shs`. It must build and
   boot canonical `gui_entry_desktop.spl`, keep that exact QEMU guest alive,
   capture same-run desktop readiness and scanout/framebuffer evidence, run literal
   `/usr/bin/simple --version`, compile `/HELLO.SPL` using embedded
   `/usr/bin/ld.lld` and `/usr/lib/SIMAIN.O`, execute the mounted-filesystem ELF,
   and bind exact output/rc to the manifest.
6. Replace/repair the existing supporting specs with the frozen SSpec, generate
   and review the operator manual, and update every affected knowledge owner.
7. Run the one-pass criteria, merge review, and stop on PASS or bounded WARN.

## Historical evidence (not restart12 acceptance)

The earlier macOS lane reported a focused payload hash
`91828e55fac193e6b695cf6f2aac782d6af11889fd1147f25533ab850284273e`, a
strict FAT image, an SSH/fsexec kernel, and OVMF/GRUB progress through opening
`/HELLO.SPL`. Those paths lived under `/Users/ormastes/...`, `/private/tmp/...`,
and now-absent `build/` outputs. The run then stalled after `post-read`, and no
guest-native linker existed. These facts motivate the plan but prove no current
criterion.

Previously landed source fixes include the SysV archive helper, target-only
runtime ABI bridges, hash-aware stamp freshness, x86_64 PML4 publication,
`SIMAIN.O` staging, and stricter SSH exit/marker handling. Their presence is
source context only until the fresh end-to-end evidence above passes.

## Bootstrap handoff applicability

B-HOST-CLI produces and adopts a Stage 4 CLI, so the canonical bootstrap
handoff contract is applicable rather than N/A. Preserve Gate 1 Stage 3
admission, Gate 2 x86_64 Linux Stage 4, Gate 3 frozen candidate sanity/hash,
Gate 4 all four essential-tool markers, and Gate 5 deploy plus the rollback
receipt produced by `sh scripts/bootstrap/rollback-bootstrap-deploy.shs <canonical-triple>`
and arithmetic receipts. Then call
`step_bootstrap_platform_handoff_readiness` through
`sh scripts/check/check-bootstrap-platform-handoff-readiness.shs`.

The checker's existing SimpleOS Gate 6 is not a substitute for this plan's
x86_64 production desktop/toolchain evidence. Extend its platform receipt
contract for the x86_64 external image-admission receipt, or keep the checker
BLOCKED; only the same-run AC-4/AC-5 receipt may satisfy this plan's Gate 6.

## Integration lifecycle

After higher-capability plan acceptance and all intentional edits are committed:

Run this exact single-shell lifecycle after committing, with the lock held from
the first fetch through the atomic receipt rename:

```sh
set -eu
trap 'rm -f /tmp/restart12-simpleos.done.tmp' EXIT HUP INT TERM
exec 9>/tmp/simple-main-restart12-push.lock
flock 9
before=$(git ls-files | wc -l | tr -d ' ')
git fetch origin main
git rebase origin/main
after=$(git ls-files | wc -l | tr -d ' ')
test "$after" -ge "$before"
test -z "$(git diff --name-only --diff-filter=U)"
env -u GH_TOKEN -u GITHUB_TOKEN git push origin HEAD:main
git fetch origin main
git merge-base --is-ancestor HEAD origin/main
test -z "$(git status --porcelain)"
commit=$(git rev-parse HEAD)
printf '%s %s\n' "$commit" PASS > /tmp/restart12-simpleos.done.tmp
mv /tmp/restart12-simpleos.done.tmp /tmp/restart12-simpleos.done
trap - EXIT HUP INT TERM
flock -u 9
```

Use `WARN` instead of `PASS` only for the bounded blocker outcome defined in
the AC ledger. Any failed command exits before the receipt rename. Never merge,
force-push, or create a branch.

Never force-push. The done receipt must remain absent before reachable push.

## Review record

- Sidecar A acceptance audit: merged 2026-08-14; found stale historical PASS
  labels, missing AC ledger/host matrix, absent manifest schema, and incomplete
  lifecycle instructions.
- Sidecar B guide/traceability audit: merged 2026-08-14; found missing frozen
  SSpec/manual targets, knowledge links, blocker coverage, and independent
  review ownership.
- Higher-capability review: PASS 2026-08-14; confirmed AC-1..AC-12,
  blocker honesty, same-run desktop/toolchain proof, non-circular manifests,
  frozen SSpec interfaces, host matrix, guide/manual scope, retry cap, and
  locked integration lifecycle are complete for an implementation-ready plan.
- Accepted done/exclusion marks: none.
