# SimpleOS x86_64 Toolchain Deployment Image and Desktop Boot Plan

Date: 2026-08-14

Status: PLAN COMPLETE (higher-capability PASS) / IMPLEMENTATION WARN — no deployment acceptance PASS
SPipe state: `.spipe/simpleos-toolchain-deployment-desktop-boot/state.md`
B-HOST-CLI scalar-metadata repair sublane: 85% implemented and focused-green;
Stage 3/4 admission remains blocked and the complete deployment feature is not
85% complete.
Full umbrella implementation estimate: 40%. AC-1 and the plan/review/knowledge
contracts are current; AC-2..5 remain production-blocked, AC-6/7 now have a
fail-closed executable/manual source but lack Stage-4 execution/docgen/quality
evidence, and AC-12 has no pushed integration receipt.

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

Inventory inspected on 2026-08-14 at baseline HEAD
`683e2d1009e16a3db6ed59d547eeb1592a851b88`. Historical paths and hashes in
later sections remain non-PASS.

| Required item | Exact current path | Fresh status |
|---|---|---|
| Pure-Simple host CLI | `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` | PRESENT, bootstrap-only Stage 2, SHA-256 `f879f1bd1116cb8ac8fe04fdeff278a5dbc01821b993ace5bce3b16b96167218`; not Stage 3/4 admission |
| Stage 3 compiler | `build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple` | ABSENT / B-HOST-CLI |
| Target Simple payload | `bin/release/x86_64-unknown-simpleos/simple` | ABSENT / B-TARGET-SIMPLE |
| Genuine guest-static linker | `build/os/clang_static/bin/lld_static` and `build/os/llvm/cross-x86_64-unknown-simpleos/bin/ld.lld` | ABSENT / B-GUEST-LLD |
| Runtime entry object | image identity `/usr/lib/SIMAIN.O` | ABSENT from current build output / B-IMAGE |
| Guest source | image identity `/HELLO.SPL` | ABSENT from current build output / B-IMAGE |
| Production desktop kernel | `build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf` (canonical `gui_entry_desktop.spl` output) | ABSENT / B-IMAGE |
| Deployment image | `build/os/elfexec_simple/fat32-simple.img` | ABSENT / B-IMAGE |
| Embedded/external admission records | `/SYS/SIMPLETOOL.SDN`; `build/os/evidence/simpleos-toolchain-image-admission-v1.sdn` | ABSENT / B-IMAGE |
| Combined desktop/toolchain wrapper | `scripts/check/check-simpleos-toolchain-desktop-boot.shs` | SOURCE COMPLETE canonical admission/preflight/receipt contract; live owner BLOCKED / B-DESKTOP-LIVE |
| Frozen executable/manual | `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl`; `doc/06_spec/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.md` | SOURCE COMPLETE / runtime B-SPEC |
| Same-run live evidence | manifest, QEMU argv, serial, SSH, framebuffer/readback, guest output receipts | ABSENT / B-DESKTOP-LIVE |

The fresh static-owner repair lane fixed the `runtime_error` receiver
corruption. A later GDB run proved the next exit 139 at
`maybe_copy_array_value` passing an aggregate `HirType` into
`remember_local_hir_type`. The scalar-ID, owner-local metadata-copy repair now
has source-bound unit coverage plus a pure-Simple Stage-2 native fixture for
append, update, missing-source, isolation-state, and resource-state behavior.
Stage 3/4 admission remains pending; this focused PASS is not deployment or
self-host convergence evidence. Retained earlier logs are
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`
(SHA-256 `1dfe959161d18cc16146825d69f9b5f64240c6917e67ab28718ddd339252bf8f`)
and `stage3-native-build.log`
(SHA-256 `51877e1e469e9504934b68097db3a8250bbf85f666247aa652e3e1c676606a5b`).
Stage 2 is bootstrap-only, never a Stage 4 CLI, SPipe runner, deployment
payload, or acceptance authority.

## Current blockers

The umbrella ledger is
`doc/08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md`.
It supplies the owner file/line and unblock condition for every row below.

1. **B-HOST-CLI:** no admitted Stage 3 and Stage 4 pure-Simple host CLI. The
   `runtime_error` static-owner defect is fixed and regression-covered. The
   GDB now identifies aggregate `HirType` transport from
   `maybe_copy_array_value` into `remember_local_hir_type` as the exact crash.
   A scalar-ID metadata-copy repair and focused native regression are green;
   Stage 3/4 verification remains required per
   `stage3_post_file_copy_exit139_2026-08-14.md`.
2. **B-TARGET-SIMPLE:** no fresh strict
   `x86_64-unknown-simpleos/simple`. Resume after B-HOST-CLI with the AC-2
   command below.
3. **B-GUEST-LLD:** no genuine static x86_64 SimpleOS `ld.lld`. Resume with the
   pinned LLVM fork build; host Mach-O/Linux binaries and wrappers are invalid.
4. **B-IMAGE:** no manifest-bound kernel/deployment image containing the exact
   admitted payload, linker, runtime input, source, and canonical aliases.
5. **B-DESKTOP-LIVE:** the production wrapper, canonical Stage-4 admission,
   shared sorted/hashed receipt validator, and 16-case hermetic self-test now
   exist. Live composition remains blocked because the canonical fullscreen
   owner launches with `-net none`, terminates QEMU after capture, and
   `gui_entry_desktop.spl` does not start or cooperatively poll SSHD. No fresh
   same-run OVMF/GRUB desktop plus SSH transcript exists for version, compile,
   link, mounted-filesystem execution, exact output, and exit status.
6. **B-SPEC:** the duplicated opt-in Clang/Rust live specs were removed. The
   canonical frozen executable/manual now call the production combined-wrapper
   path and fail closed while it or any receipt is unavailable. Stage-4
   execution, pure-Simple docgen, and the all-seven-score maintenance scan are
   still required before this row can pass.
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
- Same-run desktop/guest receipt: `simpleos_toolchain_desktop_guest_receipt`.
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

The final step executes these literal guest commands in order; the combined
wrapper records each argv, stdout, stderr, rc, input/output hash and ELF
identity in `simpleos_toolchain_desktop_guest_receipt`:

```sh
/usr/bin/simple --version
/usr/bin/simple compile --emit-object /HELLO.SPL -o /HELLO.O
/usr/bin/ld.lld -flavor gnu --no-mmap-output-file -T /sysrt/simpleos.ld -nostdlib -static --gc-sections -o /HELLO.ELF /usr/lib/CRT0.O /usr/lib/SIMAIN.O /HELLO.O --start-group /usr/lib/SIMPRT.A /usr/lib/SOSLIB.A --end-group
/HELLO.ELF
```

`require_guest_hello_receipt` requires version rc=0; `/HELLO.O` static ET_REL;
the exact linker argv including `-flavor gnu --no-mmap-output-file` (required to
avoid the known bare-output-slot `EMFILE` failure); link rc=0; `/HELLO.ELF`
static target-native ET_EXEC with no `PT_INTERP`;
execution stdout exactly `Hello World`, empty stderr, and rc=0. `/HELLO.ELF`
must be executed from the mounted filesystem rather than a preload alias. The
manifest also binds `/usr/lib/CRT0.O`, `/usr/lib/SIMPRT.A`,
`/usr/lib/SOSLIB.A`, and `/sysrt/simpleos.ld`, because the frozen link command
consumes them.

The embedded manifest is `/SYS/SIMPLETOOL.SDN`, schema
`simpleos-toolchain-deployment-v1`. Its producer is the install-image builder;
its validator is `require_toolchain_deployment_manifest`. It records path,
SHA-256, byte size, provenance, and applicable ELF class/machine/type, entry,
and `PT_INTERP` state for:

- admitted host compiler and its admission receipt;
- target Simple payload;
- genuine guest-static `ld.lld`;
- `/usr/lib/CRT0.O`, `/usr/lib/SIMAIN.O`, `/usr/lib/SIMPRT.A`, and
  `/usr/lib/SOSLIB.A`;
- `/sysrt/simpleos.ld`;
- `/HELLO.SPL` source bytes;
- canonical production desktop kernel
  `build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`.

It cannot hash its enclosing image. The pre-boot external image receipt is
`build/os/evidence/simpleos-toolchain-image-admission-v1.sdn`, schema
`simpleos-toolchain-image-admission-v1`, produced only after the image closes
and validated before QEMU by `require_toolchain_deployment_manifest`. It records
producer/validator versions, source commit, embedded-manifest SHA-256, final
image path/size/SHA-256, canonical production-kernel path/SHA-256, timestamp,
and reviewer status.

Post-boot evidence is a third, separate record:
`build/os/evidence/simpleos-toolchain-desktop-guest-v1.sdn`, schema
`simpleos-toolchain-desktop-guest-v1`, interface
`simpleos_toolchain_desktop_guest_receipt`. The combined wrapper produces it
after guest shutdown and `require_simpleos_desktop_boot_receipt` validates it.
It binds the admitted image/kernel hashes to OVMF CODE, per-run VARS, GRUB EFI,
QEMU argv, `[desktop-gui]`, `[production-readiness]`, `[scanout-evidence]`,
framebuffer/readback, serial/SSH, guest commands, output ELF, exact stdout and
rc hashes/values. All three SDN records use sorted canonical keys and end with
`record_sha256` over the canonical record excluding that field.

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
- `/usr/lib/CRT0.O`
- `/usr/lib/SIMAIN.O`
- `/usr/lib/SIMPRT.A`
- `/usr/lib/SOSLIB.A`
- `/sysrt/simpleos.ld`
- `/HELLO.SPL`

## AC-1..AC-12 acceptance and evidence ledger

The two statuses below deliberately separate the requested plan deliverable
from future feature execution. A plan-contract PASS never promotes a blocked
implementation row.

| AC | Plan contract | Implementation state | Authoritative plan evidence / exact resume | Owner | Final reviewer |
|---|---|---|---|---|---|
| AC-1 current truth | PASS | BLOCKED | Dated path-by-path inventory above; refresh after every produced artifact | root | higher-capability reviewer |
| AC-2 admitted compiler and target payload | PASS | BLOCKED / B-HOST-CLI, B-TARGET-SIMPLE | After B-HOST-CLI, `SIMPLE_BUILD_COMPILER=<admitted-stage4> SIMPLE_NO_STUB_FALLBACK=1 sh scripts/os/simpleos-native-build.shs --target x86_64-unknown-simpleos` | root/bootstrap owner | higher-capability reviewer |
| AC-3 deployment records | PASS | BLOCKED / B-GUEST-LLD, B-IMAGE | Frozen embedded, pre-boot image-admission and post-boot desktop/guest v1 schemas above; complete payload, linker, kernel and image | root/image owner | higher-capability reviewer |
| AC-4 production desktop boot | PASS | SOURCE COMPLETE preflight / LIVE BLOCKED B-DESKTOP-LIVE | Receipt-contract self-test is green; add cooperative SSHD polling and same-run guest-command hook to canonical desktop owner, then run `scripts/check/check-simpleos-toolchain-desktop-boot.shs` | root/QEMU+desktop owner | higher-capability reviewer |
| AC-5 in-guest Simple compile/run | PASS | BLOCKED / B-DESKTOP-LIVE | Literal guest commands, output/hash/identity, exact `Hello World`, rc=0 frozen above | root/toolchain owner | higher-capability reviewer |
| AC-6 frozen SSpec flow | PASS | SOURCE COMPLETE / EXECUTION BLOCKED | Canonical target contains exact helpers/visible steps, calls the production wrapper, and has no skip/non-execution pass; run once with Stage 4 after B-DESKTOP exists | root/spec owner | higher-capability reviewer |
| AC-7 operator manual and traceability | PASS | SOURCE COMPLETE / QUALITY GATES BLOCKED | Manual and REQ matrix exist; pure-Simple docgen plus all seven `sspec-maintain` scores remain required | root/doc owner | higher-capability reviewer |
| AC-8 host/capability honesty | PASS | BLOCKED rows retained | Matrix below gives prerequisite, post-implementation command, artifacts, owner and reviewer per row | root | higher-capability reviewer |
| AC-9 bounded convergence | PASS | WARN after three cycles | Attempt ledger below; no fourth or unchanged-green rerun | root | higher-capability reviewer |
| AC-10 knowledge freshness | PASS | implementation guides remain blocker-aware | Dated restart12 notes and expert cross-links listed below; umbrella bug owns every gap | root/doc owner | higher-capability reviewer |
| AC-11 cooperative review | PASS | N/A to feature execution | Both sidecar PASS verdicts and separate `higher_model_review` PASS are in the durable receipt | root merge owner | `higher_model_review` |
| AC-12 integration lifecycle | PASS | current plan commit pending integration | Exact commit/lock/fetch/rebase/push/fetch/ancestor/clean/receipt flow below | root | user-authorized push lifecycle |

Plan completion requires every `Plan contract` cell to be PASS. Feature PASS
requires fresh execution evidence for every implementation row. Feature WARN is
allowed only after no more than three distinct cycles, with unresolved rows
still BLOCKED and linked to an owner, bug, resume command, and retained
artifact; WARN is never verify PASS, release, or feature completion.

## Host and capability matrix

| Row | State | Missing prerequisite | Exact resume command | Retained artifacts | Owner | Final reviewer |
|---|---|---|---|---|---|---|
| Linux x86_64 Stage 3/4 admission | BLOCKED ([B-HOST-CLI](../../../../08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md)) | GDB-rooted `HirType` aggregate ABI repair is focused-green; Stage 3/4 verification absent | Resume the admitted Stage 3 cache once with the scalar metadata-copy repair; on candidate admission run Stage 4 plus essential-tools and handoff-readiness gates | `build/native_probe/stage3-gdb/gdb.log`; scalar-metadata unit/integration/system evidence; future candidate/provenance/admission/handoff receipts | bootstrap owner | higher-capability reviewer |
| Linux x86_64 OVMF+GRUB production desktop + guest toolchain | BLOCKED ([B-DESKTOP-LIVE](../../../../08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md)) | payload, guest linker, two-record image admission, frozen combined wrapper | After wrapper implementation: `SIMPLE_BIN=<admitted-stage4> SIMPLEOS_TOOLCHAIN_IMAGE=<admitted-image> SIMPLEOS_WM_READINESS_TIMEOUT_MS=900000 sh scripts/check/check-simpleos-toolchain-desktop-boot.shs` | embedded manifest, external receipt, QEMU argv, serial, framebuffer/readback, SSH transcript, output ELF | root/QEMU+desktop owner | higher-capability reviewer |
| Physical x86_64 board | BLOCKED ([B-PHYSICAL](../../../../08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md)) | board acquisition/identity, physical NIC driver, boot/download route | Build/check: `sh scripts/os/build-simpleos-x86_64-board-usb.shs && sh scripts/check/check-simpleos-x86_64-board-usb-image.shs`. Only after board acquisition and reviewed stable by-id recording: `SIMPLEOS_BOARD_DEVICE=/dev/disk/by-id/<reviewed-id>; test -b "$SIMPLEOS_BOARD_DEVICE"; sudo dd if=build/os/x86_64_board_usb/board-usb.img of="$SIMPLEOS_BOARD_DEVICE" bs=4M conv=fsync status=progress`; boot the named mini-PC and capture the selected evidence channel | board identity, image receipt, download log, serial or SSH transcript | board owner | higher-capability reviewer |

aarch64 and riscv64 are separate plans and outside this x86_64 deliverable;
they are not silently counted as PASS or as physical-board evidence.

## Bounded execution cycles

The feature has one shared maximum of three fix/verify cycles.

- **Feature attempt 1 (used):** strict bootstrap exposed the missing typed parser
  verification-contract owner during Stage 2.
- **Feature attempt 2 (used):** the parser-owner repair passed Stage 2 and its
  sanity gate; Stage 3 failed on fourteen inferred folded-constant types.
- **Feature attempt 3 (used):** HIR-first folded-constant typing passed Stage 2
  and removed all fourteen errors; Stage 3 later exited 139 at the distinct
  `runtime_error` static-owner receiver frontier. Exact hashes are in the fresh
  inventory and umbrella blocker ledger.
- The lane stopped with WARN after attempt 3. Every unresolved implementation
  AC remains BLOCKED, and no blocker gains an additional retry budget.

The user explicitly authorized one fresh repair lane for the primary
`runtime_error` blocker. Its three materially distinct cycles are also fully
consumed: scalar owner hint (insufficient), unique exact-symbol fallback
(primary frontier cleared), and negative-discriminant ambiguity guard (primary
frontier remained cleared; downstream exit 139 remained). No fourth retry is
permitted in this session.

The subsequent scalar-metadata lane is a distinct, GDB-rooted source repair,
not a fourth unchanged bootstrap retry. Its code and focused regression are
complete; the one materially changed cache-preserving Stage 3 resume remains
deferred while the dedicated Stage-4 owner holds the canonical bootstrap
resources. It may run once after that owner releases them. Until then
B-HOST-CLI and every downstream implementation AC remain BLOCKED.

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
this plan, never `skip()` or a green readiness-only scenario.

| Requirement / AC | Frozen scenario owner | Checker / receipt or manual section |
|---|---|---|
| REQ-SOS-TD-001, AC-1, AC-2 | `step_prepare_toolchain_deployment_image` | `prepare_toolchain_deployment_fixture`; current inventory; admitted compiler/payload provenance |
| REQ-004, REQ-SOS-TD-002, AC-3 | `step_prepare_toolchain_deployment_image` | `require_toolchain_deployment_manifest`; embedded manifest plus pre-boot image-admission receipt |
| REQ-SOS-TD-003, NFR-005, AC-4 | `step_boot_simpleos_desktop` | `require_simpleos_desktop_boot_receipt`; same-run desktop/guest receipt and framebuffer section |
| REQ-005, REQ-007, AC-5 | `step_compile_and_run_guest_hello` | `require_guest_hello_receipt`; guest commands/output ELF/exact stdout/rc section |
| REQ-006 | `step_compile_and_run_guest_hello` | mounted-filesystem `/HELLO.ELF` provenance plus canonical VFS/ELF execution receipt; no preload substitution |
| REQ-SOS-TD-004, AC-6, AC-7 | all three frozen steps | executable/manual interface, seven-score and traceability appendices |
| NFR-001 | prepare + compile/run | desktop/guest receipt requires `whole_file_buffered=false`, VFS `max_single_read_bytes <= 4194304`, loader range-read counters, and guest heap high-water below the admitted image budget while loading the large linker/toolchain ELF |
| NFR-002, NFR-SOS-TD-001, NFR-SOS-TD-002 | prepare + compile/run | fail-closed policy and component/receipt hash checks |
| NFR-004 | architecture/manual review | reuse canonical VFS, ELF loader and image owners; no parallel loader or filesystem bypass |
| NFR-SOS-TD-003, AC-8 | boot step plus capability appendix | QEMU and physical BLOCKED rows with owner/reviewer/resume |
| REQ-001, REQ-002, NFR-003 | N/A to this narrow toolchain/desktop objective | HTTP/DB protocol and bounded query/network evidence remain owned by `test/03_system/os/server/simpleos_server_execution_matrix_spec.spl` and the combined filesystem-toolchain/server plan; not counted as PASS here |
| REQ-003 | N/A to this Simple payload/guest-linker objective | mounted `/usr/bin/clang` execution remains owned by lanes C3–C5 of `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`; not counted as PASS here |
| AC-9 | verification appendix | three-cycle ledger and no-repeat rule |
| AC-10 | traceability appendix | dated knowledge checklist and umbrella blocker ledger |
| AC-11 | review appendix | durable sidecar/final-review receipt |
| AC-12 | integration appendix | commit/lock/rebase/push/reachability/clean/done receipt |

After B-SPEC and B-HOST-CLI unblock, run each exact gate once and read the
generated mirror as an operator manual:

```sh
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl
test "$(find doc/06_spec -name '*_spec.spl' -print -quit)" = ""
```

## Knowledge and traceability checklist

The 2026-08-14 plan-completion refactor records an explicit state for every
authority; future implementation changes refresh the same owner instead of
creating another contract.

| Authority | Plan-completion state |
|---|---|
| `doc/01_research/{local,domain}/simpleos_filesystem_toolchain_servers.md` | UPDATED with restart12 scope, current blocker authority and canonical-plan link |
| `doc/02_requirements/{feature,nfr}/simpleos_filesystem_toolchain_servers.md` | UPDATED with deployment-manifest, production desktop and evidence requirements |
| `doc/04_architecture/simpleos_filesystem_toolchain_servers.md` | UPDATED with two-record admission and same-run owner boundary |
| `doc/05_design/simpleos_filesystem_toolchain_servers.md` | UPDATED with frozen interfaces and wrapper/spec targets |
| `doc/03_plan/sys_test/simpleos_filesystem_toolchain_servers.md` | UPDATED with frozen deployment SSpec/manual and blocked execution status |
| `doc/03_plan/agent_tasks/simpleos_toolchain_deployment_desktop_boot.md` | CREATED as exact sidecar/merge/reviewer authority; older combined server plan is not this lane's owner |
| `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md` | UPDATED to point here and retire its old Rust-seed restart12 route |
| `doc/07_guide/os/simpleos_llvm_toolchain.md` | UPDATED: historical host artifacts separated from required guest-static linker |
| `doc/07_guide/platform/simpleos/{simpleos_x86_64_wm_qemu,qemu_system_tests,simpleos_baremetal_board_support}.md` | UPDATED with canonical wrapper/receipt/manifest rules |
| `doc/07_guide/os/simpleos_board_bringup.md` | CURRENT: physical evidence remains B-PHYSICAL; no QEMU substitution |
| feature/layer experts `simpleos_toolchain_selfhost`, `llvm_toolchain_port`, `os_kernel_exec`, `compiler_driver` | UPDATED with canonical plan, umbrella blocker and current WARN truth |
| `doc/08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md` plus the Stage 3 frontier record | UPDATED; every B-* row names owner file/line and unblock condition |
| `.codex/skills/system_test/SKILL.md` | UPDATED with canonical SimpleOS evidence profiles, single-owner layout, and fail-closed production-oracle rules |
| generated deployment manual | MANUAL SOURCE COMPLETE/B-SPEC: operator flow and traceability exist; pure-Simple docgen and `sspec-maintain` evidence remain blocked |

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
5. Complete the frozen combined wrapper
   `scripts/check/check-simpleos-toolchain-desktop-boot.shs`. It must build and
   boot canonical `gui_entry_desktop.spl`, keep that exact QEMU guest alive,
   capture same-run desktop readiness and scanout/framebuffer evidence, run literal
   `/usr/bin/simple --version`, compile `/HELLO.SPL` using embedded
   `/usr/bin/ld.lld` and `/usr/lib/SIMAIN.O`, execute the mounted-filesystem ELF,
   and bind exact output/rc to the manifest. Its canonical Stage-4 admission,
   preflight, shared receipt validator, forbidden-route policy, and hermetic
   self-test are implemented. The remaining production change is a same-run
   network/SSHD service hook in the canonical desktop owner; the wrapper fails
   closed with
   `blocked:canonical-desktop-owner-lacks-same-run-guest-command-interface`
   until that exists.
6. Replace/repair the existing supporting specs with the frozen SSpec, generate
   and review the operator manual, and update every affected knowledge owner.
7. Run the one-pass criteria, merge review, and stop on PASS or bounded WARN.

The 2026-08-16 supporting-spec cleanup retires byte-identical `test/system/`
copies and narrows the old bootstrap scenario to an explicit source-contract
inventory without Rust-seed or `bin/simple` acceptance. The canonical source,
wrapper-fixture, and image-admission specs remain deliberately narrower than
the live deployment scenario; none may promote B-DESKTOP-LIVE from file
presence, fixture payloads, or Rust-seed artifacts.

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
receipt produced by `sh scripts/bootstrap/bootstrap-from-scratch.sh rollback-deploy <canonical-triple>`
and arithmetic receipts. Then call
`step_bootstrap_platform_handoff_readiness` through
`sh scripts/check/check-bootstrap-platform-handoff-readiness.shs`.

The checker's existing SimpleOS Gate 6 is not a substitute for this plan's
x86_64 production desktop/toolchain evidence. Extend its platform receipt
contract for the x86_64 external image-admission receipt, or keep the checker
BLOCKED; only the same-run AC-4/AC-5 receipt may satisfy this plan's Gate 6.

## Integration lifecycle

Before taking the integration lock, stage only the owned plan/doc files, review
the staged diff, commit, and prove that no intentional edit remains unstaged:

```sh
git status --short
git add -- \
  .spipe/simpleos-toolchain-deployment-desktop-boot/state.md \
  doc/00_llm_process/feature_expert/simpleos_toolchain_selfhost/skill.md \
  doc/00_llm_process/layer_expert/compiler_driver/skill.md \
  doc/00_llm_process/layer_expert/llvm_toolchain_port/skill.md \
  doc/00_llm_process/layer_expert/os_kernel_exec/skill.md \
  doc/01_research/domain/simpleos_filesystem_toolchain_servers.md \
  doc/01_research/local/simpleos_filesystem_toolchain_servers.md \
  doc/02_requirements/feature/simpleos_filesystem_toolchain_servers.md \
  doc/02_requirements/nfr/simpleos_filesystem_toolchain_servers.md \
  doc/03_plan/agent_tasks/simpleos_toolchain_deployment_desktop_boot.md \
  doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md \
  doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md \
  doc/03_plan/sys_test/simpleos_filesystem_toolchain_servers.md \
  doc/04_architecture/simpleos_filesystem_toolchain_servers.md \
  doc/05_design/simpleos_filesystem_toolchain_servers.md \
  doc/07_guide/os/simpleos_board_bringup.md \
  doc/07_guide/os/simpleos_llvm_toolchain.md \
  doc/07_guide/platform/simpleos/qemu_system_tests.md \
  doc/07_guide/platform/simpleos/simpleos_baremetal_board_support.md \
  doc/07_guide/platform/simpleos/simpleos_x86_64_wm_qemu.md \
  doc/08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md \
  doc/09_report/review/simpleos_toolchain_deployment_desktop_boot_plan_review_2026-08-14.md
git diff --cached --check
git diff --cached --stat
git commit -m "docs(simpleos): complete deployment desktop plan"
test -z "$(git status --porcelain)"
planned_commit=$(git rev-parse HEAD)
test -n "$planned_commit"
```

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
result=WARN
case "$result" in PASS|WARN) ;; *) exit 1 ;; esac
printf '%s %s\n' "$commit" "$result" > /tmp/restart12-simpleos.done.tmp
mv /tmp/restart12-simpleos.done.tmp /tmp/restart12-simpleos.done
trap - EXIT HUP INT TERM
flock -u 9
```

Set `result=PASS` only when every implementation row has fresh authoritative
PASS; set `result=WARN` for this bounded blocker outcome. Any failed command
exits before the receipt rename. Never merge, force-push, or create a branch.

Never force-push. The done receipt must remain absent before reachable push.

## Review record

Durable receipt:
`doc/09_report/review/simpleos_toolchain_deployment_desktop_boot_plan_review_2026-08-14.md`.
It records the reviewed baseline/commit, sidecar verdicts, final reviewer,
acceptance completeness, blocker honesty, guide/wiki coverage, generated-manual
status, and done/exclusion marks.

- Sidecar A acceptance audit: merged 2026-08-14; found stale historical PASS
  labels, missing AC ledger/host matrix, absent manifest schema, and incomplete
  lifecycle instructions.
- Sidecar B guide/traceability audit: merged 2026-08-14; found missing frozen
  SSpec/manual targets, knowledge links, blocker coverage, and independent
  review ownership.
- Higher-capability review: PASS 2026-08-14 by separate `higher_model_review`;
  accepted AC-1..AC-12 plan completeness, blocker/history honesty, frozen
  interfaces and commands, exhaustive traceability, capability/retry policy,
  doc/wiki/manual status, lifecycle, and no implementation done marks.
- Accepted done/exclusion marks: none.
