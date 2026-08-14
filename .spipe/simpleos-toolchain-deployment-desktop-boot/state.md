# Feature: SimpleOS Toolchain Deployment Image and Desktop Boot

## Raw Request

Fresh yolo replacement lane for SimpleOS toolchain deployment image and desktop
boot. Read AGENTS.md first. Immediately inspect and update the canonical
`doc/03_plan` plan with current acceptance items and blockers, then implement
the remaining work without shortcuts. Work only in this isolated detached
worktree. Verify each criterion once, with at most three fix cycles. Commit all
intentional changes. Serialize integration using
`/tmp/simple-main-restart12-push.lock`: fetch origin main, rebase onto
origin/main, push `HEAD:main` with `GH_TOKEN` and `GITHUB_TOKEN` unset, fetch
again, and prove HEAD is reachable from origin/main. Never force push or create
a branch. Leave a clean tree and write `/tmp/restart12-simpleos.done` with
commit hash and PASS or WARN only after a reachable push.

Continuation: use `$sp_dev` with parallel agents, guide coverage, and a higher
model review to complete the plan document.

## Task Type

feature

## Refined Goal

Complete the canonical, implementation-ready plan for a strict x86_64
SimpleOS deployment image that boots through the production desktop firmware
path and runs the image-embedded Simple toolchain to compile and execute Hello
World inside the guest.

## Acceptance Criteria

- AC-1: The canonical plan identifies current artifacts and blockers from this
  worktree, separates historical evidence from fresh evidence, and records no
  stale artifact as PASS.
- AC-2: The plan requires an admitted pure-Simple host compiler and a fresh
  static `x86_64-unknown-simpleos` payload built with
  `SIMPLE_NO_STUB_FALLBACK=1`; Rust seed use is bootstrap-only and cannot be
  deployment or runtime evidence.
- AC-3: The embedded component manifest interface
  `simpleos_toolchain_deployment_manifest` binds the exact payload, genuine
  guest-native static `ld.lld`, `/usr/lib/SIMAIN.O`, `/HELLO.SPL`, kernel, and
  all canonical filesystem aliases; the external
  `simpleos_toolchain_image_admission_receipt` binds the final image SHA-256 to
  the embedded manifest SHA-256 without self-reference.
- AC-4: The production boot flow uses OVMF pflash plus GRUB-EFI and canonical
  `gui_entry_desktop.spl`, never the x86_64 QEMU `-kernel` shortcut or a
  fixed-command SSH fixture, and same-run evidence binds `[desktop-gui]`,
  `[production-readiness]`, `[scanout-evidence]`, framebuffer proof, and the
  toolchain serial/SSH transcript to the image and kernel hashes.
- AC-5: The guest transcript proves `/usr/bin/simple --version`, compiles
  `/HELLO.SPL` to a native guest ELF using the embedded linker/runtime inputs,
  executes that ELF from the mounted filesystem, prints exact `Hello World`,
  and exits zero.
- AC-6: Executable SSpec uses the frozen manual helpers
  `step_prepare_toolchain_deployment_image`, `step_boot_simpleos_desktop`, and
  `step_compile_and_run_guest_hello`; setup/checkers are
  `prepare_toolchain_deployment_fixture`,
  `require_toolchain_deployment_manifest`,
  `require_simpleos_desktop_boot_receipt`, and
  `require_guest_hello_receipt`. Any incomplete helper calls `fail(...)`.
  Visible manual text is exactly `Prepare the toolchain deployment image`,
  `Boot the SimpleOS production desktop`, and
  `Compile and run Hello World inside the guest`.
- AC-7: The executable spec remains under `test/`, the mirrored Markdown under
  `doc/06_spec` reads as an operator manual with zero stubs, every REQ/AC is
  traceable, and `sspec-maintain scan` plus the generated-spec layout guard
  pass once.
- AC-8: The plan records each host/capability row as fresh PASS or BLOCKED with
  owner, missing prerequisite, exact resume command, retained artifacts, and
  final reviewer; QEMU-only evidence does not claim physical-board completion.
- AC-9: The plan names no more than three distinct fix/verify cycles, forbids
  rerunning an unchanged green criterion or identical failed command, and
  defines PASS/WARN stop conditions without weakening any criterion.
- AC-10: Knowledge is current in the canonical plan, affected research,
  architecture/design/test-plan artifacts, the SimpleOS toolchain/board/QEMU
  guides, feature-expert and compiler/OS layer-expert wiki skills, and every
  unresolved gap has a `doc/08_tracking/bug/` record with file/line and unblock
  condition. Workflow skill/command docs are N/A unless the implementation
  changes their contract; generated manuals remain mandatory.
- AC-11: Parallel sidecar findings are merged by the root owner, and a separate
  higher-capability reviewer accepts acceptance completeness, blocker honesty,
  guide coverage, generated-manual quality, and all done/exclusion marks.
- AC-12: Intentional changes are committed and integrated exactly through the
  user-authorized detached-worktree lock/fetch/rebase/push/reachability flow;
  the final tree is clean and the done receipt is written only after reachable
  push.

## Scope Exclusions

- Physical-board PASS until board identity and live boot evidence exist.
- aarch64/riscv64 completion, full LLVM self-bootstrap, and unrelated compiler
  or desktop rendering work.
- Host binaries, placeholder apps, fixed-command fixtures, and historical
  transcripts as substitutes for fresh guest execution.

## Cooperative Review

- Sidecar A: acceptance/evidence and blocker audit.
- Sidecar B: guide, knowledge, SSpec/manual, and traceability audit.
- Merge owner: Codex root lane in this isolated worktree.
- Final reviewer: separate higher-capability Codex model after merge.
- Shared interfaces: `simpleos_toolchain_deployment_manifest` and
  `simpleos_toolchain_image_admission_receipt`.
- Manual steps: `step_prepare_toolchain_deployment_image`,
  `step_boot_simpleos_desktop`, `step_compile_and_run_guest_hello`.
- Exact visible step text: `Prepare the toolchain deployment image`,
  `Boot the SimpleOS production desktop`,
  `Compile and run Hello World inside the guest`.
- Setup/checkers: `prepare_toolchain_deployment_fixture`,
  `require_toolchain_deployment_manifest`,
  `require_simpleos_desktop_boot_receipt`, `require_guest_hello_receipt`.
- Placeholder policy: `fail(...)` only; no no-op/pass placeholder.
- Generated-manual review owner: final higher-capability reviewer.

## Phase

dev-done

## Log

- dev: Created state file with 12 acceptance criteria (type: feature).
- review: Sidecar acceptance and guide/traceability findings merged; independent
  higher-capability review PASS on 2026-08-14 for plan completion only.
- impl: WARN after three attempts. The nested-guard fix passed the old Stage 3
  parser frontier and its Rust-seed diagnostic unit spec passed 5/5, but strict
  self-host Stage 3 later exited 139; downstream deployment ACs remain BLOCKED.
