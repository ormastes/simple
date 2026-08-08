# Feature: SimpleOS ARM64 WM real screen

## Raw Request
`$sp_dev impl simple os wm real screen.md plan. after sync and push gh.`

## Task Type
feature

## Refined Goal
Build an attested current-source ARM64 SimpleOS desktop, boot it in one visible
QEMU Cocoa window, and retain correlated guest, framebuffer, and physical-input
evidence proving the window manager draws and reacts on the real screen.

## Acceptance Criteria
- AC-1: The producer accepts only a receipt-qualified pure-Simple compiler with
  strict no-stub and no-fabrication evidence.
- AC-2: The current ARM64 ELF, FAT image, frozen-source manifest, build manifest,
  compiler receipt, and hashes agree.
- AC-3: Diagnostic QMP evidence correlates guest frame/input events with
  before/after framebuffer captures.
- AC-4: A visible Cocoa QEMU interval records physical click, title-bar drag,
  `a`, Ctrl press, and Ctrl release, each followed by a guest frame.
- AC-5: Boot-to-paint, frame identity/checksum/dimensions, argv/accelerator,
  revision, timing, RSS, and no-orphan cleanup receipts satisfy the plan.
- AC-6: The executable SSpec, generated manual, operator plan, report, and SPipe
  state describe the same commands and retained evidence.
- AC-7: Final synchronized GitHub `main` contains the reviewed implementation
  and evidence artifacts without unrelated work.

## Scope Exclusions
Clang browser-demo work and optional bootstrap migration are separately owned.

## Cooperative Review
Existing sibling WM/VMM, strict-stub, and compiler-global lanes are merged by
the root Codex agent. The root agent is also sole QEMU launch owner and final
high-capability reviewer. Shared evidence helpers and scenario vocabulary are
defined by `arm64_simpleos_qmp_input_spec.spl`; no new placeholder is allowed.

## Phase
dev-done

## Log
- dev: Reconstructed the authoritative refinement from the existing plan with
  seven acceptance criteria; implementation/evidence remains in progress.
- audit: The separately owned 7200-second Stage 4 producer ended after entering
  the 1030-file driver and emitted no compiler. No receipt or ARM64 QEMU process
  appeared; unchanged Stage 2/3 admission failures were not repeated.
- admission: Current `origin/main` supplied the owner-reset repair at
  `039cad933a`. Its separately built 22 MiB Phase 2 compiler passed bootstrap
  sanity and identified as `simple-bootstrap 1.0.0-beta` with SHA-256
  `30e9889950e6ed620fcaea51fcb1fb472be200679d4c8cb12bf633c339193b37`.
  The one canonical strict non-entry module-global admission still failed
  closed with signal 11 after `function:locals` and `function:params`. The
  three-cycle compiler cap is exhausted; no receipt, ARM64 build, or QEMU
  launch is permitted from this candidate.
- resumed-fix: A fresh bounded lane moved `MirBody.return_ty` reads and
  flattened-body construction through owner methods (`22b04a7b46`,
  `6471bf9a57`). A direct strict Phase 2 build emitted a 22 MiB compiler
  (`fd5fd23fd4ce3321eedaf9c9d7a0c369ed351371de4f32e60a3a3f6a91e29d0e`),
  but its source changed during the build and canonical module-global
  admission still exited 132 after `function:params`. The fresh three-cycle
  cap is exhausted; no receipt or QEMU launch is allowed.
