---
name: sp_dev
description: "SPipe dev entrypoint: refine a feature/bug/TODO into acceptance criteria, then continue through the SPipe pipeline."
---

# SP Dev -- SPipe Development Entrypoint

`/sp_dev` is the Codex entrypoint for the SPipe development workflow. The
standalone `/dev` Codex skill has been removed so development work routes
through the explicit SPipe namespace. SPipe is the runner/docgen/process layer;
SSpec is the executable `.spl` scenario authoring surface.

Use it for a feature, bug fix, refactor, or TODO that should start with SPipe
goal refinement and acceptance criteria, then continue through research, design,
SSpec scenarios executed through SPipe, implementation, refactor, verification,
and ship handoff:

```
/sp_dev <description of what to build or fix>
```

## Dispatch

Start with the SPipe dev agent instructions in `.claude/agents/spipe/dev.md`.
Use `.claude/skills/spipe.md` for SPipe test/spec conventions when the workflow
reaches specification and verification phases.

During the SPipe Refactor phase, run the doc/wiki refactor support skill at
`.claude/skills/spipe_doc_wiki_refactor.md` so stale docs, command references,
wiki-style process knowledge, and feature/layer expert links are cleaned before
final verification. Ship consumes verify evidence and must not repair stale
process docs.

Before final verification, update every process artifact that
the lane changed: generated/manual SPipe docs under `doc/06_spec`, matching
`doc/07_guide` pages, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
`.claude/agents/spipe/`, and `.gemini/commands/` instructions. Treat stale workflow/tooling docs as
verify failures, not release cleanup. For scenario-oriented SSpec, generate the
mirrored manual doc, read it as an operator manual, and fix step names,
captures, `@inline`/`@prev` visibility, and helper names until the primary flow
is understandable without opening the source spec.

When `$sp_dev` creates requirement option docs, do not leave them as the final
state. After the user selects feature and NFR options, write the final
`doc/02_requirements/feature/<feature>.md` and
`doc/02_requirements/nfr/<feature>.md`, delete unchosen `*_options.md` files,
and refresh the matching `doc/07_guide` page before verification. A lane with
selected options but lingering "Pending Selection" docs is not complete.

Completion gate: do not mark a goal, SPipe phase, verify report, or ship lane
complete when workflow/tooling behavior changed and the matching guide, skill,
agent, command, or generated/manual spec docs are still stale. Update the docs
first, then run focused verification evidence once.

For must-check hook work in linked Git worktrees, remember that the hooks
directory is shared. Install the stable `scripts/hooks/pre-push-worktree-launcher`
and let it resolve the active worktree; never bind the shared hook to one
worktree's absolute dispatcher path.

Check the canonical hook wiring before installing or repairing it. On Unix-like
hosts, run:

```sh
sh scripts/setup/install-must-check-hooks.shs --check ||
  sh scripts/setup/install-must-check-hooks.shs --install
```

If `spipe` is absent or returns `unknown command: self-review-guide`, first
fetch and fast-forward the current `main`, then initialize the pinned plugin:
`git fetch origin main`, `git switch main`, `git merge --ff-only origin/main`,
and `git submodule update --init .spipe/spipe`. Run the
`node .spipe/spipe/cli/spipe.js self-review-guide` form. The unknown command
means a stale installation; it does not authorize falling back to author
`gh pr review --approve`.

```powershell
& scripts/setup/install-must-check-hooks.ps1 -Check
if ($LASTEXITCODE -ne 0) { & scripts/setup/install-must-check-hooks.ps1 -Install }
```

See `doc/07_guide/tooling/must_check_tiering.md` for the tier contract and
linked-worktree launcher details.

For every acceptance criterion, record one passing result and do not rerun the
same unchanged green command. Stop after three verify/fix cycles for one
feature and report any remaining failure; convergence ends the lane instead of
starting another confirmation loop.

Bootstrap/tooling lanes that produce a Stage 4 full CLI must retain the bounded
`scripts/check/check-bootstrap-essential-tools-smoke.shs` gate against the exact
fresh binary. Require the test-runner, lint, duplicate-check, and aggregate pass
markers. Raw-source execution, a deployed wrapper, Rust seed, stale artifact,
or disabled stub-fallback guard is not equivalent evidence. Treat this as
post-bootstrap command sanity; it does not replace release `--whole` tests or
the applicable full lint and duplication gates. If duplicate caching changed,
the same gate must prove token/cosine create/reuse parity, changed/deleted-file
invalidation, `--no-cache`, exit parity, and JSON stdout purity.
The completion recorder must override ambient `SIMPLE_BINARY`/`SIMPLE_BIN` and bind every
automated bootstrap gate to the exact validated Stage 4 candidate.

For bootstrap/compiler debugging, keep normal SPipe verification on the
default-off path. Use `--diagnostics=test` for progress and coarse phase
timing without parser trace; use `--diagnostics=debug` (or bare `--diagnostics`)
only when detailed phase trace, retained successful LLVM IR, and memory
snapshots are needed. Both modes imply `--progress`. AOP call/assignment
tracing is not implied: scope it with `SIMPLE_AOP_DEBUG=<pattern>` and enable
the specific AOP log flag only when weaving is under investigation. Never use
debug-mode output alone as Stage 4 admission or release evidence. Bind an
isolated sweep with `--diagnostic-child-compiler=<absolute admitted CLI>` and
record both driver and child identities.

Use `bin/simple lint <changed .spl files>` and
`bin/simple duplicate-check <owned-dir> --mode token --min-lines 5` for those
pure-Simple gates. `bin/simple build lint` and `build check` are Rust workspace
clippy/rustfmt commands, not substitutes.

An explicitly admitted Stage 2 or Stage 3 Simple binary may run focused
pure-Simple compiler/interpreter/loader work under the canonical minimal-
bootstrap guide. Record exact path, hash, stage, provenance, supported commands,
isolated output/cache, and stage-scoped evidence; fail closed on unsupported
commands and never fall back to the Rust seed. It is not deployed Stage 4,
general `run`/`test`/SPipe/docgen, release, convergence, or cross-host evidence.
If a direct lexer probe and parser-facing token stream disagree, capture both
streams plus continuation state in one compiled probe. After three distinct
fix/probe cycles, update the tracked bug and lane state and stop; do not rewrite
valid source merely to bypass the parser defect.

For standalone target products such as Office, separate target construction from
compiler bootstrap. Use only an explicitly supplied, provenance-admitted Phase
3 compiler; put output/cache under `build/standalone`, preserve strict no-stub
and fabricated-stub guards, and record its digest. Missing admission is a
blocker, not authorization to start Stage 1 or use the Rust seed. A Phase 3
artifact may build a target but never substitutes for a Stage 4 CLI in SPipe,
deploy, test, or release evidence.
Authenticated interpreter `--assert-ran` requires canonical `simple-bdd-v1`
evidence; stdout summaries or colored pass markers are never execution proof.

If a stale deployed pure-Simple test runner crashes during repair, temporary
Rust-runner evidence may use only the explicit `SIMPLE_TEST_RUNNER_RUST=1`
seed opt-in. Bound it with the canonical resource cap, `timeout -k`, and
redirected output. Never treat that opt-in as production fallback or release
evidence; remove it after the rebuilt pure runner passes the same fixture.

Runner subprocess capture must use the shared bounded process facade (4 MiB
per stdout/stderr stream), preserving head, tail, and the omitted-byte marker.
This applies to interpreter, native/SMF compile+run, composite, doctest,
parallel temp-file, and fork lanes. Timeout verification requires both the
timeout exit and marker, plus descendant-held-pipe evidence; do not treat every
spawn/internal `-1` as a timeout or truncate only after an unbounded capture.

For release-bound SPipe lanes, the final test-runner evidence is
`bin/simple test test --whole --mode=interpreter`. `--whole` must retain all
spec/long-test discovery and execute both `.spl` comment doctests and configured
Markdown code fences; a narrower `--all`, `--only-slow`, or smoke run is not
release evidence.

For work spanning multiple host or capability rows, keep every unavailable
row's acceptance-criterion IDs active. Reuse its authoritative TODO and plan,
or create them when none exist, and record the missing prerequisite, exact
resume command, and retained artifacts.
Postponement is not completion: it cannot move the row into exclusions, close
its TODO, or permit a phase, verify report, or goal to be marked done. Postpone
only native execution that genuinely requires another prepared host; keep all
host-independent and current-host rows active until finished.
Keep every unavailable row visible in executable and generated-manual evidence
as `unsupported` or `blocked`; never omit it, convert it to `skip()`, or count
it as PASS. `Current-host scope complete` is narrower than feature completion.
The authoritative resume plan must name the target host/capability,
prerequisites, exact command, retained artifacts, owner, and final reviewer.

For physical-board bring-up, run the stateful serial session once and make its
receipt the sole acceptance oracle. Detect adapters by stable USB identity and
interface metadata, never fixed `ttyUSB` numbering; preserve and restore any
temporarily detached kernel driver. A missing adapter, silent UART, all-zero or
all-one JTAG scan, or unavailable admitted compiler is `BLOCKED` (exit 2 plus a
specific reason), never PASS. A wrong TAP ID, malformed receipt, observed boot
failure, destructive flash verb, or missing restoration evidence is FAIL.
Offline contract/self-tests may prove the classifier, but cannot promote live
hardware acceptance. Bind the build receipt to the exact compiler path/hash and
provenance; a stale Stage 2/3 binary may diagnose a closure but cannot supply
release, SPipe/docgen, or physical-board PASS evidence.
For UART evidence, prove the bounded reader retains partial bytes when timeout
terminates a tty read. Prefer a byte-streaming `dd`-style capture with a file
receipt; do not assume `timeout head -c <large-count>` preserves reset bursts.
If a direct read sees bytes while the wrapper reports silence, classify the
wrapper as failed and repair it before diagnosing target wiring.

For original UP Squared Apollo Lake bring-up, use removable x64 UEFI media and
the fallback path `EFI/BOOT/BOOTX64.EFI`; never use the host system disk or the
board's internal eMMC for first light. CN16 is 3.3 V TTL UART. CN22 pin 4 is
1.8 V and its documented JTAG is FPGA/CPLD/BIOS service, not a proven Apollo
Lake CPU JTAG port; complete signal thresholds are unpublished, so do not
drive it with Tigard/OpenOCD. The retained handoff is
`doc/03_plan/agent_tasks/up_squared_apl_simpleos.md`; its offline image and
partial source state are not physical boot or `ls` evidence.
Media attached to UP2 is not addressable by the build host merely because the
board has a Micro-B OTG port. Prefer moving the stick to the writer host. A
remote write is admissible only when UP2 already runs a trusted Linux/SSH or
RAM/PXE environment: stage and hash the image on UP2, resolve one stable
`/dev/disk/by-id` identity, reject root/swap/mounted/internal media, bind an
explicit serial/capacity confirmation, write locally, sync, recheck identity,
and hash the exact image-length readback. Never stream SSH directly into a raw
device. UEFI Shell, UART, USB OTG gadget mode, and PXE availability must each be
proven rather than inferred; firmware flashing is a separate forbidden lane.
The canonical tools are
`scripts/os/build-simpleos-up-squared-usb-image.shs`,
`scripts/os/write-simpleos-up-squared-usb.shs`, and
`scripts/check/check-simpleos-up-squared-apollo-lake.shs`. The writer is
read-only until `--write-media` plus the exact identity/image SHA-256 challenge
are supplied; a media receipt with full image-length readback is mandatory
input to `--live`. The live checker must keep one UART session open from boot
markers through the freshly injected public-VFS `ls /` window.

For original-UP2 Intel DCI requests, distinguish proprietary Intel USB 3.x DCI
DbC from open xHCI DbC and from USB bridge cables. An Intel-qualified DCI DbC
cable/probe, firmware debug consent, enabled/unlocked architectural debug
interface, and Intel System Debugger/System Bring-Up Toolkit are mandatory.
Smart KM Link
`0ea0:2211`, Tigard `0403:6010`, CN22, generic GDB, and OpenOCD do not establish
DCI. Inventory with `scripts/check/check-up-squared-apl-dci.shs --inventory`;
missing tool, rules, or retained target receipt is BLOCKED. DCI run control and
physical-memory staging do not authorize BIOS, MSR, or storage writes. Boot the
existing UEFI image under DCI observation unless a reviewed CPU-state-specific
RAM trampoline exists; perform persistent writes only through an identity-gated
target-side storage driver with flush and exact readback evidence.
Intel documents that Apollo Lake OpenRC warm reset can strand cores in an
undefined state and requires manual reset; reject it rather than treating DCI
reset as generic. A Power-Good reset is unqualified without exact-board proof.
Before any proposed RAM load, run
`scripts/check/inspect-up-squared-apl-dci-elf.shs --inspect`; non-contiguous
`PT_LOAD` ranges and `p_memsz - p_filesz` zero-fill must be honored. Prefer a
UEFI-resident mailbox loader over debugger-authored CR/GDT/page-table state.
Treat the inspector output as authoritative over copied sizes in manuals or
tests. The 2026-08-22 admitted artifact is 298,648 bytes, and its writable
segment ends at `0x0b000000`; when the kernel changes, update any fixture that
claims to represent the "exact current" layout before accepting mailbox tests.
For the retained UP2 A+B+D selection, reuse the pure-Simple admission policy in
`src/os/kernel/arch/x86_64/up_squared/dci_mailbox.spl`: payload-before-commit,
fresh generation/nonce, SHA-256 binding, physical `PT_LOAD`/BSS validation,
RAM allowlisting, and exact storage identity/challenge/bounds. Do not promote
these host-independent checks to physical DCI, boot, or storage-readback PASS.
Intel's System Bring-Up Toolkit is a CNDA/Registration Center download, not an
APT package; missing authentic installer or `99-dci.rules` stays BLOCKED.
Intel's Target Connection Agent matrix listing Apollo Lake establishes silicon
and tool-family support only; it does not prove that a particular UP2 FAB routes
the DCI port or that its BIOS enables and unlocks debug consent. Likewise, the
UEFI Debug Support protocol and Debug Support Table aid a resident agent or an
external debugger's memory discovery; they do not reserve a command mailbox,
authenticate a payload, load ELF segments, exit boot services, or transfer
control. `dci_mailbox.spl` remains policy rather than a loader, but the separate
GNU-EFI `up2_dci_uefi_loader.c` now implements that boundary. Require
`scripts/check/check-simpleos-up-squared-apollo-lake.shs --ovmf-dci-admission`
to prove commit-last GDB RAM authorship, nonce/SHA/ELF admission, final EFI map,
embedded ELF32 shim entry, and SimpleOS shell without GRUB; retain physical DCI
and multi-core firmware/kernel AP-state evidence as separate gates. PI firmware
owns the ExitBootServices AP-idle transition; do not dispatch a non-returning
`StartupAllAPs` procedure and call it parking.
Pair it with `--ovmf-dci-rejection`, which must reject a fully written kernel
whose committed descriptor carries the wrong digest before transition or GRUB.
Require `nonce-source=firmware-or-rdrand` for committed boot. A time/TSC nonce
may preserve diagnostics and GRUB fallback but must not authorize RAM execution.
Before using a UP2 image hash in a media/storage challenge, run
`scripts/check/check-simpleos-up-squared-apollo-lake.shs --image-reproducibility`.
It must build twice in fresh directories and compare the full GPT/FAT image;
pin SOURCE_DATE_EPOCH, disk/ESP GUIDs, FAT ID, and copied-file timestamps rather
than treating stable kernel/PE hashes as proof of a stable container.
For UP2 physical boot, record Secure Boot state, use F7 for the one-time entry,
and use DEL or ESC for firmware setup. Treat an EFI-shell launch as a distinct
fallback with mapped-filesystem and artifact evidence.
For the current UP2 image, `BOOTX64.EFI` is the directly entered PE32+ resident
loader and `GRUBX64.EFI` is its uncommitted-timeout fallback. Code first entered
through the embedded ELF32 Multiboot2 shim is post-UEFI and cannot truthfully
claim ownership of page reservation, the final memory map, or
`ExitBootServices`; those remain owned by the PE32+ layer and its reviewed
64-to-32-bit handoff.
When Intel DCI is unavailable, do not claim that OpenOCD, CHIPSEC, KGDB, xHCI
DbC, or host GDB replaces it. The free UP2 lane is removable UEFI boot plus a
target-resident debugger over CN16 UART (and later xHCI DbC). Wire CN16 pin 8
GND, pin 10 board TX to adapter RX, and optionally pin 9 board RX to adapter TX;
use 3.3-V TTL at 115200 8N1 with no flow control, and never connect 5-V pins 1/5.
Tigard FTDI interface 00 is Port A/Serial; interface 01 is Port B/JTAG. CN22 is
1.8-V CPLD/BIOS service, not an Apollo Lake CPU TAP. A zero-byte capture is
BLOCKED pending power/reset/wiring proof, not a boot FAIL.
For legacy-COM1 first light, initialize the UART before the first marker and
consume any loopback-test byte before normal input. Writing `0xAE` while MCR
loopback is enabled without reading DATA afterward contaminates the first
command (`0xAEls /`). Require an emulator transcript proving the first clean
command, while retaining physical CN16 as a separate evidence gate.
For the current free UP2 memory lane, enter the target monitor with shell
command `gdb`. Admit only checksummed GDB RSP `m`/`M` requests inside the
linker-owned `0x0a000000..0x0b000000` staging segment, cap transfers at 1024
bytes, and read every write back before `OK`. An OVMF receipt may prove the
packet/RAM path, but physical CN16 remains separate. Never promote unsupported
register, breakpoint, continue, step, reset, or binary `X` packets to PASS.

When a user asks to close an implementation phase with external verification
still unavailable, record an **implementation handoff** in the plan and Todo
DB. It may end the coding turn only after code and host-independent tests are
landed; it must retain each external acceptance criterion as blocked and must
not be reported as a verify PASS, release, or umbrella-goal completion.

For SimpleOS QEMU host-GPU NFR-006, TODO 566 postpones only unavailable
non-current native timing rows. Hardware-independent source/parser/self-test
work and the current Linux native row remain active. Evidence must cover one
guest-observed interval from device initialization through every rejected or
timed-out Metal, DirectX, and Vulkan attempt to backend selection or CPU
fallback. Daemon HELLO `elapsed_us` and cross-ISA TCG prove correctness only,
not the 500 ms native target.

For SimpleOS compiler-in-filesystem lanes, completion requires the Simple
compiler/interpreter/loader payload to be embedded in the SimpleOS install image
and executed from the SimpleOS filesystem. SPipe specs must prove the target
payload is SimpleOS-native, not host `bin/simple`, and that the image contains
`/usr/bin/simple(.smf)`, `/bin/simple(.smf)`, `/sys/apps/simple(.smf)`,
`/sys/apps/simple_compiler(.smf)`, `/sys/apps/simple_interpreter(.smf)`,
`/sys/apps/simple_loader(.smf)`, and `/SYS/SIMPLETOOL.SDN`. A PASS claim also
needs in-guest evidence for `/usr/bin/simple --version` plus compiling and
running a small `hello world` from the mounted filesystem. QEMU fixed-command
stubs, host-side compiles, and placeholder marker apps are blockers, not proof.
Physical-board claims additionally need board identity, boot/download path, and
serial or SSH transcript; otherwise record QEMU-only or source-present status.

For SimpleOS QEMU matrix work, use the shared settings and host-admission
scripts before every run, isolate each nonce-patched image, and make the
collector nonce distinct from any workload nonce that the target also prints.
The ordered transcript must prove `guest-entry`, real filesystem listing,
mounted target stdout, exit 37, exact reap, and `TEST PASSED`. Emit a row only
with `produce-sosix-qemu-native-pass-bundle.shs`; the 24-row collector is the
sole matrix promotion owner. Keep Windows/FreeBSD target-host rows blocked and
macOS postponed when their native executor is unavailable—never omit or count
them as PASS. The current evidence ledger is
`doc/03_plan/sys_test/sosix_qemu_matrix_evidence_status_2026-08-13.md`.
Before a native run, execute `sh scripts/check/produce-sosix-qemu-native-pass-bundle.shs --self-test`;
that temporary direct-kernel fixture validates producer closure only and never
replaces pre-run host admission or real row evidence.

For recent unfinished-plan cleanup lanes, use
`doc/07_guide/infra/recent_plan_cleanup.md`. Keep the cleanup matrix under
`doc/03_plan/agent_tasks/` with sidecar lanes/`N/A`, merge owner, and final
reviewer, keep SPipe state under `.spipe/<cleanup-name>/`,
classify every candidate as `mark-done`, `needs-evidence`,
`needs-requirement-selection`, `needs-implementation`, or `superseded/merge`,
and run normal LLM review before accepting generated-manual quality, done marks,
or broad exclusions.

When implementation changes add or replace evidence wrappers, refresh the
matching guide/process documentation in the same lane. For GPU, Engine2D, Simple
Web, Electron/Tauri, QEMU, or backend readback evidence, update the relevant
`doc/03_plan`, `doc/07_guide`, and `doc/09_report` references so future agents
can find the canonical wrapper instead of repeating stale commands.
For HTML-backed GUI modernization, pair screenshot or bitmap evidence with
structured Electron interaction evidence. A pass needs visible controls to
receive focus, keyboard/input, pointer, and click events, or the wrapper must
classify the missing GUI host dependency explicitly.
For RenderDoc evidence specifically, use
`scripts/tool/renderdoc-evidence.shs capture-simple` for the Simple
in-application `rt_renderdoc_*` path and
`scripts/tool/renderdoc-evidence.shs capture-html` for original
RenderDoc+Chrome HTML/CSS capture, plus
`scripts/tool/renderdoc-evidence.shs capture-electron-html` for bundled
Electron Chromium HTML/CSS capture. Tests should route through
`test/helpers/renderdoc_capture_helper.shs` or the compatibility wrappers.
For GUI/web/2D RenderDoc+Vulkan work, use
`scripts/setup/setup-gui-web-2d-vulkan-env.shs --check` for readiness,
`--browser-backing` for focused direct Electron Chromium backing proof, `--run`
for direct Electron/Chrome/Simple probes, and `--renderdoc-simple` for the
Simple in-application RenderDoc debug path on a prepared Linux or macOS
RenderDoc host. Leave `RDOC_SIMPLE_BIN` unset unless deliberately overriding;
the helper builds `src/compiler_rust/target/release/simple` so the
`rt_renderdoc_*` externs are current. Use all-lane `--renderdoc` only for
cross-surface evidence collection.
For browser RenderDoc diagnostics, `RDOC_RENDERDOC_HOOK_CHILDREN=0` omits
`--opt-hook-children`; this may isolate Chromium child-hook crashes, but it is
not passing evidence unless the Chrome/Electron GPU-process capture still emits
a valid `.rdc` with `RDOC` magic.
Do not accept `--in-process-gpu` as a Linux Chromium/Vulkan workaround unless a
fresh run proves Vulkan remains enabled and emits valid browser `.rdc` evidence;
current Electron/Chrome diagnostics show that mode is unsupported or crashes.
For the NVIDIA 8K80 container campaign, prepare/check the image with
`scripts/setup/prepare-render-perf-8k80-container.shs`. Require a digest-pinned
NVIDIA CUDA devel base, the checked-in package snapshot, `vulkan-tools`,
`/usr/bin/time`, no `mesa-vulkan-drivers`, and an immutable image-ID receipt.
The live check must request `compute,utility,graphics` and name an NVIDIA
Vulkan device; inventory still does not replace strict submit/readback proof.
On Windows, first read `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md`.
`vulkaninfo --summary` plus Chrome/Electron installation proves host readiness
only; it does not prove Chrome or Electron are Vulkan-backed. The Vulkan SDK
installer may require administrator elevation, and SDK readiness requires a
fresh shell where `glslangValidator`, `spirv-as`, and any required shader
compiler such as `dxc` resolve. If `winget install --id
KhronosGroup.VulkanSDK` reaches an elevation prompt and is canceled, record
`sdk-tools-missing` and do not claim SDK setup complete.
Install/refresh `vulkan-tools`, `vulkan-loader`,
`vulkan-headers`, `molten-vk`, `spirv-tools`, and `glslang`; prove MoltenVK
with `vulkaninfo --summary`; then require Simple Vulkan/Engine2D evidence,
original Chrome evidence, Electron Chromium evidence, and production GUI/web
parity evidence. A Chrome/Electron bitmap with a log containing Chromium's
`angle=vulkan` unavailable failure is a fallback render, not Vulkan proof;
record `vulkan-angle-unavailable` and leave the gate failed. The aggregate
audit must expose `gui_web_2d_vulkan_comparison_fixture_status`,
`gui_web_2d_vulkan_comparison_artifact_status`,
`gui_web_2d_vulkan_comparison_artifact_reason`,
`gui_web_2d_vulkan_electron_argb_viewport_match_status`,
`gui_web_2d_vulkan_electron_argb_file_status`,
`gui_web_2d_vulkan_electron_argb_nonblank_status`,
`gui_web_2d_vulkan_chrome_argb_file_status`,
`gui_web_2d_vulkan_chrome_argb_viewport_match_status`,
`gui_web_2d_vulkan_chrome_argb_nonblank_status`,
`gui_web_2d_vulkan_simple_evidence_file_status`, and
`gui_web_2d_vulkan_simple_backend_status` before treating Electron,
Chrome, and Simple artifacts as comparable. The audit may still emit
`gui_web_2d_vulkan_chrome_screenshot_*` diagnostic keys, but a missing Chrome
PNG is not a comparison blocker when the Chrome ARGB artifact is present,
viewport-matched, and nonblank.
Artifact presence is not a pixel-equivalence claim. Require
`gui_web_2d_vulkan_pixel_comparison_status=pass`,
`gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff`, ARGB metadata for
Electron/Chrome/Simple, and the zero-mismatch pairwise diff statuses
`gui_web_2d_vulkan_electron_chrome_pairwise_diff_status`,
`gui_web_2d_vulkan_electron_simple_pairwise_diff_status`, and
`gui_web_2d_vulkan_chrome_simple_pairwise_diff_status` before claiming the
Electron baseline, Chrome Vulkan-backed render, and Simple GUI/web/2D Vulkan
render match pixels. If the aggregate reports
`gui_web_2d_vulkan_pixel_comparison_status=fail` with
`gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff-mismatch`, treat it
as a real pixel mismatch to fix, not as missing evidence.
Browser Vulkan proof must be read
from `gui_web_2d_vulkan_browser_backing_status`,
`gui_web_2d_vulkan_browser_backing_reason`, and
`gui_web_2d_vulkan_browser_backing_mode`; fallback bitmap comparison is not
Vulkan-backed browser proof, and the aggregate GUI audit must remain incomplete
until browser backing is `pass`. Read current macOS blocker lanes from
`gui_web_2d_vulkan_renderdoc_blocker_status`,
`gui_web_2d_vulkan_renderdoc_blocker_reason`,
`gui_web_2d_vulkan_renderdoc_blocker_gate_count`, and
`gui_web_2d_vulkan_renderdoc_blocker_gates` before claiming RenderDoc, Simple,
Electron, or Chrome Vulkan-backed capture is ready; blocker status `blocked` is
a completion blocker, not a warning. GUI widget fixture evidence must
also prove per-widget feature witnesses via
`gui_widget_rendering_fixture_coverage_renderdoc_fixture_widget_features`, not
only widget/class presence. When a task claims all GUI items are RenderDoc
tested, run `scripts/check/check-gui-widget-renderdoc-goal-status.shs`; require
`gui_widget_renderdoc_goal_status=pass`,
`gui_widget_renderdoc_goal_widget_feature_covered_count=43`,
`gui_widget_renderdoc_goal_simple_gate_status=pass`,
`gui_widget_renderdoc_goal_electron_gate_status=pass`, and
`gui_widget_renderdoc_goal_blocked_gate_count=0`. Normal non-Mac runs may report
`incomplete`, but release or completion claims must use `--strict` with real
Simple Vulkan Engine2D and Electron Chromium/Vulkan `.rdc` evidence. Defer
Windows and Linux claims until platform-specific runbooks validate the same
evidence keys and RDOC gate contract.
For Linux Vulkan render-log comparison, require the aggregate audit to expose
`linux_vulkan_render_log_compare_renderdoc_simple_env_file_status`,
`linux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status`,
`linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic`,
`linux_vulkan_render_log_compare_renderdoc_chrome_env_file_status`,
`linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status`,
`linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic`,
`linux_vulkan_render_log_compare_renderdoc_electron_env_file_status`,
`linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status`, and
`linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic`; an env file
that exists without a real `RDOC` artifact remains a blocker.

For Tauri2 mobile renderer parity, use
`scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`. It must pass
the desktop production GUI/Web parity source first, then require live iOS
Tauri2/WKWebView screenshot evidence plus Metal markers and live Android
Tauri2/WebView screenshot evidence plus Vulkan/skiavk or host-emulator Vulkan
markers. Both mobile lanes must also expose
`*_mdi_event_status=pass`, `*_mdi_capture_status=pass`,
`*_mdi_performance_status=pass`, and `*_mdi_animation_status=pass` from the
`[tauri-shell] mdi proof:` JSON. That proof covers window-manager event
delivery, viewport capture provenance, `performance.now()`, two animation
frames, and CSS animation support. A packaged APK or a nonblank Android
screenshot is not Vulkan proof if logcat contains `F/DEBUG`, `Fatal signal`,
`VulkanManager`, `Headless UI completed`, or subprocess parse failures; leave
the aggregate unavailable/failed until the Android renderer log, screenshot,
and MDI proof all pass. Host/emulator GPU logs such as ANGLE/Vulkan or
Apple/SwiftShader Vulkan are supporting evidence only when `com.simple.ui`
remains foreground, a `[tauri-shell] render, html_len=` marker is present, the
screenshot is captured from the live app, and the MDI proof is valid.

For runtime concurrency work, keep the public API map current in
`doc/07_guide/lib/misc/stdlib.md`, `doc/07_guide/compiler/check_perf.md`, and
`.codex/skills/coding/SKILL.md`. In particular, distinguish `thread_spawn`
(OS thread), `cooperative_green_spawn` / `cooperative_green_spawn_value`
(implemented cooperative green-thread queue on the current OS thread),
`multicore_green_spawn` (Pure Simple bounded-worker facade over `rt_pool_*`),
and `task_spawn` (pool-backed native task path when `rt_pool_*` links). Do not
document cooperative green-thread APIs as Go-style M:N CPU parallelism. When a
profile or test claims M:N behavior through `multicore_green_spawn`, require
`MulticoreGreenHandle.used_runtime_pool()` evidence so inline fallback cannot
masquerade as CPU-parallel work.

For dynSMF or SMF-startup work, distinguish three separate lanes before
editing: SimpleOS disk SMF placement, GUI SMF dynlib release evidence, and the
general dynSMF background compile/startup lane. If the request says the
interpreter should compile SMF while reading/running scripts, or mentions
precompiled `build/dynsmf/*.smf` artifacts, start with
`src/os/smf/dynsmf_session.spl`,
`src/app/startup/dynsmf_autoload.spl`, and
`scripts/check/check-low-dependency-dynsmf-build-plans.shs`. This is not
GUI-only: GUI renderer entries and non-GUI entries share the same manifest,
build-plan, `compile_background` evidence, and checked-autoload contract. Update
`doc/07_guide/lib/api/dynlib_api.md`, the low-dependency dynSMF architecture
and design docs, and the matching SPipe specs whenever that contract changes.

For optimization work, use `.codex/skills/optimize/SKILL.md`. SPipe optimization
tasks must start from a baseline, run
`bin/simple run src/app/optimize/main.spl <file> --full --level=O3` on touched
`.spl` files, preserve behavior, and rerun both correctness tests and the same
perf script. Do not rewrite Simple features in C/Rust to claim C-level speed; if
parity is blocked by runtime/compiler behavior, record a measured blocker under
`doc/08_tracking/bug/`.

Minimize runtime coupling first in SPipe lanes. App, GUI, web, 2D, MCP/LSP, and
benchmark code should use Simple facades instead of new raw runtime calls,
env/CLI shortcuts, direct backend field poking, or tool-local runtime aliases.
A build-local alias entrypoint is a last-resort compatibility shim, not the
default path for new capability. If performance or correctness is blocked by
generated native code, fix the Simple compiler/codegen/runtime owner path with
the smallest reproducer and gate; only edit `src/runtime/**` when the lane is
explicitly runtime-owned or the bug is proven there. Do not hide a
compiler/runtime bug by normalizing an `rt_*` workaround in feature code.

Before adding any new `rt_*` import, extern, wrapper, alias, runtime-backed
fixture bypass, or direct backend field access outside `src/runtime/**`, stop
and record the decision in the lane state:

- `runtime_need`: the exact missing capability or measured bottleneck.
- `facade_checked`: the existing `std.*`, `app.*`, owner-module, or build-local
  alias facade checked first.
- `chosen_path`: `reuse-facade`, `add-smallest-owner-facade`,
  `fix-codegen-runtime-owner`, or `runtime-owned-change`.
- `rejected_shortcuts`: raw aliases, fixture-only branches, backend pokes, or
  generated-code workarounds deliberately not used.

The default chosen path is `reuse-facade`; the default answer to a new `rt_*`
shortcut is "do not add it". Add the smallest missing facade in the owner module
or improve codegen/runtime once at the owner boundary. Pixel/rendering evidence
tools may keep bounded local fixture painters, but must not grow new raw runtime
shortcuts to paper over renderer, compiler, or backend bugs. Any attempt to
solve an SPipe failure by adding `rt_*` plumbing must also add or cite a focused
gate proving the facade/codegen/runtime boundary, not just the feature output.

Before handoff, run `sh scripts/audit/direct-env-runtime-guard.shs --working`
for runtime-adjacent lanes and treat any new raw env/process/runtime access
outside owner modules as a fix-before-done issue.

Before touching runtime-adjacent code in an existing lane, read that lane's
recorded `rejected_shortcuts` first; do not retry a rejected `rt_*`, fixture
bypass, backend-poke, or generated-code workaround unless new evidence changes
the decision.

For runtime-vs-pure-Simple algorithm work, use the shared dual-backend mode
names consistently in specs, docs, and code:

- `alpha` = current default, run both and stop on diff
- `beta` = run both and log a critical diff report
- `normal` = run only the preferred implementation

Prefer helper names that expose those mode names directly:

- `dual_backend_alpha_default_mode()`
- `dual_backend_beta_default_mode()`
- `dual_backend_normal_pure_simple_mode()`

Keep the legacy `assert/critical/pure_simple` helper names only as temporary
compatibility aliases. New wrappers, examples, and docs should use the
`alpha/beta/normal` helper names.

For Pure Simple SSH/HTTPS server work, use `alpha`/`beta`/`release` mode names:
`release` is the production single-path Simple protocol mode, while `alpha` and
`beta` may compare against native/SFFI protocol wrappers. Runtime/SFFI may supply
host access only (TCP accept/read/write, time, entropy, filesystem/cert/key
access, and process execution). Release-mode production wrappers must not call
`rt_ssh_*` or `rt_tls_server_*` as complete protocol bypasses. Keep
`doc/07_guide/lib/networking/pure_simple_servers.md` current when this contract
changes.

For native HTTPServer/static-file performance lanes, keep the canonical evidence
set current before handoff: `scripts/check/check-native-pure-simple-goal-status.shs`,
`scripts/check/check-web-server-nginx-live-compare.shs`,
`scripts/check/check-web-server-static-external-live-compare.shs --require-simple-ge-all`,
`scripts/check/check-web-server-go-erlang-static-compare.shs --require-simple-ge`,
`scripts/check/check-httpserver-live-static.shs`, and
`scripts/check/check-httpserver-static-profile-counters.shs --broad --require-retained`.
Update `doc/07_guide/infra/testing/benchmarking.md`,
`doc/10_metrics/perf/web_server_nginx_compare.md`,
`doc/09_report/perf/web_server_nginx_compare_2026-06-17.md`, and the active
tracking docs when retained rows or wrappers change. Do not keep a
micro-optimization that fails retained rows; revert it or record the measured
blocker/rejected result under `doc/08_tracking/`.

When a task introduces a new runtime/pure wrapper, update the shared guide at
`doc/07_guide/os/crypto_dual_backend.md` and prefer an explicit
`DualBackendConfig` dependency-injection entrypoint plus a default-config
convenience wrapper. If `normal` mode is meant to avoid dual execution on the
hot path, use the `dual_backend_run_*` lambda-based helpers rather than
precomputing both outputs before comparison.

For UI, GUI, MDI/window-manager, Draw IR, Simple 2D, or Engine2D backend-lane
work, keep the stack architecture current in
`doc/04_architecture/ui/simple_gui_stack.md` and its TLDR companion. If the work
changes shared UI contracts, event propagation, Draw IR source/event metadata,
or the drawing-vs-processing backend split, update the generated/manual spec
docs under `doc/06_spec`, the relevant `doc/07_guide` process note when one
exists, and cite the canonical implementation paths such as
`src/lib/common/ui/draw_ir.spl`,
`src/lib/common/ui/window_scene_draw_ir.spl`, and
`src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`.

For UI-test helper work, keep the test-library surface consistent: new SSpec
manual specs use canonical `use std.spec.*` and `step("...")`, existing
`use std.spipe` remains an alias, and UI/SGTTI/Draw IR helpers must layer inside
SSpec scenarios instead of replacing `describe`, `it`, `expect`, `step`, or the
built-in matchers. `Given_*`, `When_*`, and `Then_*` helpers are legacy manual
text helpers.
SGTTI is a test/debug evidence interface. Production entrypoints must not import
`std.ui_test.sgtti`, `SgttiTestDriver`, or SGTTI capture builders unless the
specific debug/test entrypoint explicitly opts in; compile-time entry-closure
builds must be able to elide SGTTI entirely. When adding TUI/GUI debug evidence,
include a system spec that proves the normal entrypoint has no SGTTI/debug-TUI
import path.
When a UI change claims layout, border, color, style, or text-bound parity,
prefer the Protocol-v2 Draw IR baseline diff
`/api/test/draw-ir/diff?baseline=...&capability=draw_ir` or the shared
`common.ui.draw_ir_diff` helper as structured evidence before falling back to
pixel-only assertions.
When the question is "where did this GUI component render?", use
`/api/test/draw-ir/layout?id=...&capability=draw_ir` or `expect_draw` to assert
the stable id, role/kind, geometry, hit rect, parent, and computed style inside
the SSpec case.
After adding or moving UI-facing app feature specs, run
`test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl` to keep
the critical UI SSPEC lane mirrored into generated manuals with visible
evidence markers.

For portable processing, GPU compute, ML matops, draw-kernel, RV64GCV, VHDL/RTL
accelerator, or `simplegpu64` work, keep the processing lane current in
`doc/04_architecture/compiler/backend/processing_backend.md`,
`doc/04_architecture/compiler/backend/processing_backend_tldr.md`, and
`doc/07_guide/compiler/backends/processing_backend.md`. Treat CUDA, Vulkan,
RV64GCV, VHDL/RTL, and CPU fallback as backends below ProcessingIR, not separate
public API forks. Do not claim Simple has a real RISC-V64 Adreno/Mali-like GPGPU
until CPU oracle, software backend, and RTL/simulation evidence agree for the
same processing scenarios.

For compiler cache, loader, JIT, formal verification, or accessor-forwarding
work, include SPipe evidence for semantic invalidation. A change to public ABI,
field-wrapper shape, forwarded getter/setter behavior, or generated accessor
dependencies must miss the interpreter/incremental cache and any SMF/JIT cache
that could otherwise reuse stale code. Add focused specs near the cache owner
instead of relying only on broad loader suites.

For MCP/runtime-forwarding or startup-latency work, refresh both the lane state
file and `doc/07_guide/app/mcp/startup_performance.md` before handoff. Keep the
guide aligned with the current wrapper contract (native-first, probe-stamped,
no silent source fallback in production), the direct-`rt_*` guard policy, the
interface-cache/source-mtime contract, and the latest local smoke numbers from
`scripts/check/check-mcp-native-smoke.shs`.
Use `bin/simple deps fast|normal|deep <entry.spl>` and
`doc/07_guide/compiler/deps_tool.md` when a startup or tool-server change claims
dependency-closure reduction; record before/after file counts and the concrete
imports removed or localized.

Do not write boolean-wrapper assertions in new SPipe specs:
`expect(a == b).to_equal(true)`, `expect(a != b).to_equal(false)`, and similar
forms are quality-gate failures. Assert concrete values directly, or use
`to_be(true/false)` only when the boolean value itself is the unit under test.

For Simple Web/Electron renderer parity, keep the canonical wrapper documented
as `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`.
Generated-GUI evidence may record explicit `text_normalization_pixels` for
fixture-scoped browser text antialiasing normalization, but must still require
matching checksums, `mismatch_count=0`, and `blur_or_tolerance=false`. Treat
Linux Metal readback as host-unavailable (`metal-requires-macos`) and require
native raw Metal readback evidence on macOS. A production renderer pass must
also forward `scripts/check/check-wm-browser-event-routing-evidence.shs` under
`production_gui_web_renderer_parity_event_routing_*` and require focus, window
move/maximize, title-command keyboard input, body text input, pointer down/up,
and `blur_or_tolerance=false`; render/capture parity without interaction
delivery is incomplete evidence.
For GUI/web queue proof, runtime queue/drain receipts are necessary but not
sufficient. Production proof requires same-frame backend `device_readback`, a
positive backend handle, and matching checksum; runtime-only, synthetic-handle,
upload-only, or CPU-mirror evidence fails.

Before marking a feature tracking row `status=done`, fill `requirement`,
`research`, `plan`, `architecture`, `design`, `system_spec`, `spec_doc`,
`implementation`, `unit_tests`, `integration_tests`, and `guide`, then run
`<runtime> lint doc/08_tracking/feature/feature_db.sdn`.

When a workflow or tool contract changes, update the matching `doc/07_guide`,
`doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
`.claude/agents/spipe/`, and `.gemini/commands/` instructions before handoff. Treat stale process docs
as unfinished work, not release cleanup.

For broad SPipe planning lanes, split independent research or implementation
checks across lower-model parallel agents when available (for example Codex
Spark, Claude Haiku, or Claude Sonnet). The best available
normal/highest-capability model must review and accept the merged result before
requirements, done marks, broad exclusions, or release-blocking verification are
trusted. Before lower-model sidecars fan out, that best-model pass must define
shared interface names, manual-facing `step("...")` flow helpers, and
setup/checker helper names; temporary helpers must fail explicitly with
`assert(false)` or `fail(...)`.
Final verification must prove the recorded cooperative review plan is complete
or explicitly `N/A`, including generated-manual quality and done-mark review.

If other Codex, Claude, or Gemini sessions are active, identify the lane this
`/sp_dev` invocation owns before editing or syncing. Do not absorb unrelated
dirty files into the feature just because they are present in the shared
checkout. Preserve other-agent work, report it separately, and commit only the
intentional lane unless the user requests a combined integration.

For scenario-oriented work, the SPipe loop also includes generated manual
review. After SSpec `.spl` scenarios are written or changed, generate the
mirrored `doc/06_spec/...` document and read it as a scenario manual. Update
`step("...")` text, capture policy, inline/previous scenario expansion, and manual
visibility until the generated manual is good enough to use without opening the
source test. See `doc/07_guide/infra/sspec_scenario_manual.md`.

Run `sh scripts/setup/install-spipe-dev-command.shs --check` on Unix-like hosts, or
`powershell -ExecutionPolicy Bypass -File scripts\install-spipe-dev-command.ps1 --check`
on Windows, to verify that this repository still routes Codex development
through `/sp_dev` and does not carry a separate `/dev` skill.

Before handoff, run the generated-spec layout guard:

```sh
find doc/06_spec -name '*_spec.spl' | wc -l
```

The result must be `0`; executable SSpec belongs under `test/`, while
`doc/06_spec` contains generated/manual Markdown and evidence assets only.
Also run `sh scripts/audit/direct-env-runtime-guard.shs --working` and
`sh scripts/audit/direct-env-runtime-guard.shs --staged` before final verify so
new app/gc env reads and process calls use env/process facades instead of local
`rt_env_get`, `rt_process_run`, `rt_process_run_timeout`,
`rt_process_spawn_async`, `rt_process_wait`, `rt_process_is_running`, or
`rt_process_is_alive`, or `rt_process_kill`.

## LLM Fine-Tune Handoff

For SPipe LLM-backed app/server work, use the fine-tune registry commands under
`.spipe/llm-finetune-process/`. If an artifact exists but misses its target eval,
record the failed eval, create or link the retry attempt, and file remaining
retry/verification/safety/deployment work in `doc/08_tracking/todo/todo_db.sdn`
and `doc/08_tracking/feature/` before reporting the handoff state.

## Reference: SimpleOS LLVM/Clang toolchain

For the Stage-4 bootstrap migration, require Clang/LLVM 23.1 together with a
matching Rust LLVM binding/vendor update. A legacy LLVM 18/20 bootstrap is
diagnostic-only: do not report it as a 23.1 candidate or use it for deployment.
Record unavailable-host/toolchain state with the exact resume command and keep
the corresponding platform acceptance row active.

Building a C/C++ "hello world" for SimpleOS with clang? The LLVM→SimpleOS port
has a host cross toolchain and static sysroot, but it is not a general POSIX
port and must not be described as easy guest-native Clang support. The current
Clang-20 cross driver has a register-allocator failure for ordinary C code;
historical in-guest proof is limited to `clang -cc1 -emit-obj`. Guest driver
mode additionally needs filesystem exec plus fork/exec. Keep host cross,
guest `-cc1`, guest link, and guest run as distinct gates. Full guide + exact
commands:
`doc/07_guide/os/simpleos_llvm_toolchain.md`.

## Session update 2026-07-18

SimpleOS desktop bring-up continues through the C1-C8 baremetal codegen 
landmine catalog (doc/08_tracking/bug/). Recent fixes shipped: seed 
import-alias resolution, receiver-binding under --entry-closure, NVMe DMA 
zero-address guard, interpreter stack overflow, i64 print precision. Canonical 
reference guide (in progress): doc/07_guide/os/baremetal_simple_codegen_landmines.md.

## Verification tiering (build infra)

Follow `doc/07_guide/compiler/minimal_bootstrap_configuration_composition.md`.
Start with the smallest named target, provider, and SCI projection and retain
the build receipt. A compiler path is not a bootstrap reason. Unknown
compatibility rebuilds the smallest relevant closure; full bootstrap is limited
to a typed incompatibility or explicit release/trust target.

For mandatory-check tiering, keep the interactive push gate bounded and route
expensive gates through `scripts/check/check-bootstrap-must-pass.shs`. Ledger v3
rows must name a non-empty owner; TODO/blocked rows require an actionable
non-`none` unblock condition, while PASS rows require
`unblock_condition=none`. The push consumer must fail closed on violations.

## Log-retention convention (debug/perf instrumentation)

General policy (canonical statement: `doc/07_guide/infra/logging/`): when
cleaning up instrumentation/debug/perf logs, do not delete the insert —
convert it to a level-gated log (debug level, or another appropriate level;
perf/timing instrumentation becomes a perf-level log disabled by default) so
it stays reusable for the next investigation. Deletion is reserved for
overly-specific one-off logs with no reuse value. Prefer one shared
gate/flag or an existing log facility over ad-hoc per-file booleans.

Worked example — baremetal/kernel entry files: debug probes are debug-gated,
not stripped. Prefer wiring into the existing
`src/os/baremetal/profile/log_policy.spl` `BaremetalLogPolicy` facility when
a target already threads it through; the minimal fallback for a target that
doesn't yet is a per-file `fn _probe_debug() -> bool: false` (flip the
literal to re-enable) — a **function**, not a module-level `val`, since
module-global initializers are unreliable on the freestanding lane
(module-init gap) and would make a bool `val`'s flip-to-`true` re-enable
silently no-op — with an early `if not _probe_debug(): return` guard in the
probe body so call sites stay untouched. Silent in production boots, still
there for the next investigation. Never gate a probe whose output an
evidence/gate script asserts on. See
`doc/07_guide/os/baremetal/baremetal_simple_codegen_landmines.md` § "Probe
caveats".

## SSpec documentization maintenance

For SSpec authoring or cleanup, run `simple sspec-maintain scan <spec>` as the
quality peer of lint and duplicate-check. Review all seven scores and stable
`SSDOC-*` findings; blockers cap the aggregate at 49. Directory/CI policy must
fail closed for empty scope, missing/stale mirrors, configured thresholds, and
machine-output contamination. `improve` previews; write only after explicit
confirmation, retain rollback material, and rerun the focused evidence once.
`scaffold` preserves reference hash and REQ identity and keeps unresolved
oracles fail-fast. `documentize` adds professional scoring/provenance through
the canonical SPipe manual owner. Baseline review uses `--baseline`;
suppression review uses `--suppressions` with rule, owner, reason, and optional
fingerprint, and blockers cannot be suppressed. Optional LLM advice is
source-evidenced preview only, excluded
from scoring, and never self-applies.
Full external-standard imports follow the shared `spec-to-spipe` architecture
(`spec-to-sspec` is a compatibility name) and retain source-ledger coverage;
the maintenance scaffold alone is not a lossless importer.

## Typed evidence (Modern SSpec)

An **observation** is what the capture recorded; an **oracle** is the typed
check that decides pass/fail — never assert on a string built from the
observation itself. Modules: `src/lib/common/spec/evidence/model.spl`
(selectors, `OracleCheck`, `OracleSpec`, `check_exact`/`check_full_pattern`/
`check_ignore`/`check_multiset`/`check_bind`/`check_same_as`, `oracle_spec`)
and `evidence_comparator.spl` (`compare_evidence`).

**Fail-closed rules:** parse error fails · unresolved selector fails ·
ambiguous cardinality fails · `check_ignore` without a reason fails · a spec
where every check is `ignore` (no positive oracle) fails · closed-mode
(`oracle_spec`, not `oracle_spec_open`) rejects undeclared fields · bind-only
specs with no comparing check are vacuity-fail · non-numeric tolerance fails ·
tolerance overflow fails · an unchecked manifest digest fails. The last four
(bind-only vacuity, non-numeric tolerance, tolerance overflow, unchecked
manifest digest) were red-team findings, all now fixed — see
`doc/08_tracking/audit/modern_sspec_evidence_contract_redteam_2026-08-08.md`.

Guide: `doc/07_guide/infra/sspec_typed_evidence.md`.

For the parent-authoritative actor/process lane, keep the closed evidence
schemas separate: `actor-channel-authority/v1` covers the implemented
same-thread scheduler-owned actor compatibility surface, while
`parent-commit-piped-result/v1` covers framed process ingress, parent commit,
and lifecycle. Follow the frozen steps and exclusions in
`doc/03_plan/sys_test/actor_channel_authority.md` and
`doc/03_plan/sys_test/parent_authoritative_actor_process.md`. In-memory typed
comparison is not retained provider provenance, and authored mirrors are not
generated PASS while Stage-4 docgen/maintenance are blocked. Never substitute
the Rust seed.


## Bootstrap platform handoff readiness

For bootstrap/platform handoff work, use the canonical readiness checker:

```bash
sh scripts/check/check-bootstrap-platform-handoff-readiness.shs
```

Plans and manuals must call the helper step exactly
`step_bootstrap_platform_handoff_readiness` after Gate 5R. The helper checks
receipts for the same source and frozen candidate lineage; it does not rebuild,
substitute the seed, accept stale artifacts, or infer a PASS from partial logs.
Only a complete Gate 1-6 sequence may emit PASS. Missing native hosts are OPEN
or BLOCKED, never PASS.

Stage 3 may be owned by another agent. Stage 4 and external-host preparation
may proceed independently, but later gates consume the Stage 3 owner's exact
path, hash, authority identity, and admission receipt. Independent preparation
must not be reported as admission or platform success.

Gate order is fixed: 1) Stage 3 admission, 2) x86_64 Linux Stage 4, 3) frozen
candidate sanity/hash, 4) four essential-tool smoke markers, 5) deployment then
`sh scripts/bootstrap/rollback-bootstrap-deploy.shs <canonical-triple>` with
rollback receipt, and 6) the selected native/QEMU/target platform acceptance.
The rollback receipt includes command, exit status, pre/post/restored hashes,
receipt path, and arithmetic smoke output.

A live failure permits at most three distinct fix/verify cycles. Stop after the
third cycle and do not rerun an identical failed command. Cross-builds, stale
artifacts, static review, and unavailable hosts cannot produce a false PASS.

## Post-bootstrap Stage 4 SSpec

Run the exact candidate once against
`test/03_system/check/post_bootstrap_stage4_acceptance_spec.spl`, setting
absolute `STAGE4_POST_BOOTSTRAP_BINARY` and adjacent
`STAGE4_POST_BOOTSTRAP_PROVENANCE`. It verifies unchanged retained smoke and
does not replace deployment, rollback, QEMU, or native-host gates.

## Multi-TAP JTAG evidence

Do not infer a CPU target from a matching TAP ID alone. A board may expose
multiple TAPs with the same ID code. Declare the complete ordered chain and
select the architecture/hart required by the boot contract before any memory
oracle. A RAM-write acceptance probe must use a reviewed scratch address, save
the original value, write and read back a distinctive pattern, restore the
original value, resume the target, and restore any host USB driver. Scan-only
evidence never proves RAM read/write access.

For firmware-managed targets, a verified JTAG RAM load is not a verified kernel
handoff. Record load and boot as separate phases. Direct debug-PC resume must
reproduce the firmware privilege, interrupt, hart, and DTB contract or remain a
diagnostic action; prefer the board firmware's reviewed ELF/FIT handoff for
acceptance. Derive UART register width and shift from the board contract: a
shared base does not make QEMU byte-wide 16550 access compatible with a
DesignWare 8250 requiring 32-bit accesses.

When U-Boot is the launcher, distinguish its ELF application ABI from an
OpenSBI kernel handoff. `bootelf` may pass argc/argv instead of hart/FDT in
`a0/a1`; the board shim must validate any fixed firmware FDT address before
using it and fail closed otherwise. Record whether program-header (`-p`) or
section-header (`-s`) loading was proven on the exact U-Boot build. A loader
exception is a loader failure, not a guest boot failure.

If generic JTAG reset does not reboot the SoC, a reviewed SBI SRST trampoline
may be injected into an allowlisted RAM scratch address: set the SRST EID/FID
and cold-reboot arguments, execute `ecall` in supervisor mode, retain UART proof
of BootROM/OpenSBI/U-Boot restart, and restore the debug-probe driver. Keep the
trampoline fixed and reject arbitrary code/addresses. On the proven StarFive
JH7110/Tigard lane, use `scripts/os/starfive-jtag-sbi-reset.shs`; generic
OpenOCD `reset run` is hart-level debug control and is not a full-SoC reset
oracle. Do not claim reset from the OpenOCD command alone: the retained UART
transcript must show a fresh BootROM/OpenSBI/U-Boot sequence. For immutable
packaged roots, a VFS-owned manifest is valid evidence when the shell calls
public `readdir`; names must not be embedded in the shell output path.

On JH7110, declare all five harts on the U74 Debug Module before examination.
Keep them out of an SMP halt group for staging/reset automation: a firmware-
running boot hart 1 may reject halt while parked secondary hart 2 remains fully
examinable. The canonical SBI helper uses hart 2, explicitly writes debug
resume privilege `S`, and verifies a new session returns hart 2 to the OpenSBI
machine-mode window. That is JTAG proof of firmware re-entry; physical boot
acceptance still requires the UART firmware sequence. Stage the ELF file via
hart 2, then let U-Boot on hart 1 perform the reviewed `bootelf` handoff.

If SBI injection is impossible even through the parked secondary hart, an
`ndmreset` pulse remains diagnostic only until a fresh session proves firmware
re-entry and UART shows restart. Otherwise classify BLOCKED and require probe
reconnection or one physical reset/power-cycle; never repeat an unverified
software-reset loop.

For StarFive VisionFive 2 NVMe work, separate PCI identity, NVMe Identify, and
destructive provisioning. The M.2 socket is JH7110 PCIe1/domain 1; DT parsing,
clocks, resets, PHY, PERST, PLDA quirks, and link validation remain in the
StarFive port, while ECAM enumeration, NVMe commands, GPT, FAT32, and VFS remain
host-neutral. A missing `pci`/`nvme` command in vendor U-Boot is firmware-build
evidence, not proof that the SSD is absent. JTAG/ECAM can at most establish PCI
vendor/device/class and cannot substitute for an NVMe Identify command.

Run identification without writes and retain exact controller serial, model,
firmware, NSID, LBA size/count, and capacity. Provisioning requires a separate
explicit action bound to that immutable identity; never use a password as the
destructive confirmation. Reject mounted, in-use, ambiguous, changed, or boot-
source targets. Format only a bounded GPT partition, never namespace LBA 0 as a
filesystem. Persistence PASS requires write, flush, unmount, remount, hash-
equal read, and command-correlated VFS `ls /nvme` from one retained transcript.
If failed high-address debug access leaves a hart unexaminable, stop software-
reset retries and require a physical reset/power-cycle.

For non-coherent JH7110 PCIe DMA, carry allocator handles with queue and bounce
resources. Flush SQ/data buffers before ringing a doorbell and synchronize CQ,
Identify, and read buffers before CPU inspection. A linked image or clean
Identify parser test without those ownership transitions is not live NVMe
evidence.

For UP Squared NVMe work, reuse the host-neutral `NvmeDriver`, lease-backed
`NvmeBlockAdapter`, GPT, and FAT32 owners; the board leaf owns only PCI
discovery/grant, freestanding x86 DMA/MMIO providers, and shell admission.
Identify must remain write-free. Destructive format requires the exact live
serial/NSID/LBA-count challenge and two bounded leases (namespace for GPT,
partition for FAT32). Verify flush plus fresh-adapter readback and an external
FAT reader on a dedicated scratch image before claiming interoperability.
Never test against the development host's system NVMe.

For full UP2 disk images, keep `os.services.storage_image_provision`
host-neutral and the UP2 leaf identity/staging-specific. The protocol is plan,
exact `UP2-STORAGE-WRITE` confirmation, ordered <=1 MiB chunks, then finish.
Use SHA-256 of length-delimited canonical identity fields in the confirmation;
print the complete identity separately so long hex-rendered Identify strings do
not overflow the serial line buffer.
Hash every staged chunk before write, flush, and compute streaming whole-image
SHA-256 over the exact range through a fresh adapter. Abort on identity,
ordering, hash, I/O, or readback change. Do not reuse the FAT32 challenge for a
raw image or promote emulator evidence to physical persistence.
On the UP2 freestanding RSP transport, parse high-volume `M` packets with
scalar state directly into the admitted staging window and immediately read
each byte back. Do not materialize or slice repeated 2 KiB text packets: the
monotonic 16 MiB heap cannot reclaim that traffic. Keep checksum ACK distinct
from storage authorization, and never bypass a target SHA mismatch merely
because an RSP `m` readback passed.
For freestanding streaming hashes, require one reusable fixed block and
schedule with in-place state updates; per-block arrays are incompatible with a
monotonic heap at disk-image scale. Keep target write/Flush/fresh-readback,
independent host SHA, unchanged surrounding ranges, and USB-absent NVMe boot as
separate receipts.

For UP Squared debug-tool admission, distinguish software availability from a
usable transport. GNU GDB/OpenOCD/picocom are the free baseline, but OpenOCD
does not decode Apollo Lake's proprietary Intel DCI ExI protocol. Admit Tigard
only when FTDI `0403:6010` enumerates, CN16 UART only when a tty appears, and
DCI/DbC only with a qualified USB3 debug interface and a retained connection
receipt. Reject Smart KM Link `0ea0:2211`: its storage/HID descriptors provide
no UART or debug endpoint. A missing USB device is BLOCKED, not grounds for
repeated software-reset attempts.
