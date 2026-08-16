# Feature: SOSIX QEMU Matrix Remaining Implementation

## Raw Request

`what blocked? even block imple and make modern sspec system tests for them? and add to todo db?`

## Task Type

feature

## Refined Goal

Implement every host-independent and current-Linux SOSIX QEMU matrix blocker, cover each owner with modern fail-closed SSpec system scenarios, and register every externally unavailable native row in the Todo DB without misreporting it as complete.

## Acceptance Criteria

- AC-1: The collector distinguishes structural bundle validation from matrix promotion and cannot emit matrix PASS when any of 24 rows is blocked, unsupported, postponed, duplicated, or missing.
- AC-2: Nonce-media preparation rejects identical resolved source/run paths before mutation and proves distinct source preservation, copied-run mutation, and readback failure behavior.
- AC-3: Compiler-in-filesystem validation uses the hash-bound admitted runtime selected for the row and rejects missing, stale, seed, hardcoded, or identity-mismatched substitutes.
- AC-4: RV64 produces a fresh admitted Linux bundle proving named/immediate inline-asm transport, OpenSBI/direct-kernel boot as applicable, real filesystem listing, mounted program output, exit 37, exact reap, and `TEST PASSED`.
- AC-5: x86_32 links and executes a real CPL3 filesystem lifecycle with strong GDT/TSS/`esp0`, authenticated scalar token, `enter_user_first`, trap return, scheduler continuation, exit 37, and exact reap.
- AC-6: ARM32 links and executes a real EL0/SVC filesystem lifecycle with strong vector/entry/token/result/scheduler owners, mounted ELF staging, exit 37, and exact reap.
- AC-7: A modern SSpec system spec uses the frozen steps `Validate matrix promotion`, `Reject mutable source aliasing`, `Bind the admitted runtime`, `Admit the Linux guest lifecycle`, `Record unavailable native hosts`, and `Retain the implementation handoff`; every scenario has concrete assertions and typed evidence, blocked rows remain executable fail-closed cases, and the mirrored manual is operator-quality with zero stubs.
- AC-8: Todo DB has explicit open rows for the three Linux guest closures, shared L0 defects until verified, six Windows rows, six FreeBSD rows, and six macOS rows; each names prerequisites, exact resume command, retained artifact root, execution owner, merge owner, and high-capability reviewer.
- AC-9: Guide, canonical plan, evidence ledger, feature/layer experts, architecture/design, executable spec, generated manual, and open-owner tracking agree with the final implementation and evidence.
- AC-10: Each focused gate runs once; at most three fix/verify cycles are used. Unavailable native hosts remain BLOCKED/POSTPONED and prevent umbrella matrix completion.
- AC-11: FAT32 provides true cursor-independent positioned primitives and generation-safe aliased file objects; the production syscall 134/135 shim retains the concrete owned-copy backend, and a modern SSpec admits it only through a receipt-bound pure-Simple runtime plus strong linked kernel symbols.

## Scope Exclusions

No Linux evidence may be relabelled as Windows, FreeBSD, or macOS. No Rust seed, stale Stage 3 artifact, host-side fixed command, cached transcript, or synthetic bundle may satisfy a native row.

## Cooperative Review

Parallel architecture/compiler lanes were explicitly requested. `/root` owns
the merge; each broad lane required high-capability review before acceptance.

Shared interfaces: `simple-qemu-settings.shs`, `simple-qemu-host-admission.shs`, `prepare_qemu_nonce_media.shs`, `produce-sosix-qemu-native-pass-bundle.shs`, `collect-sosix-qemu-evidence.shs`.

Manual steps: the six phrases in AC-7. Setup/checker helpers retain the canonical script names; unresolved helpers must fail with `assert(false)` or `fail(...)`.

## Phase

blocked

## Log

- dev: Refined the implementation request into ten acceptance criteria; external-host evidence remains active and cannot be completed locally.
- impl: AC-1 through AC-3 now have behavioral proof: a real 24-row non-PASS collector fixture, physical/symlink alias rejection before mutation, and path/SHA/version-bound runtime admission with missing/seed/stale/identity-mismatch rejection. The integrated shared-owner self-test passed once.
- impl: AC-4 through AC-6 now have direct live-QEMU implementation evidence:
  RV64 Sv39 isolation and exact fault/reap ownership; x86_32 PAE/NX CPL3,
  hardened ELF/FAT admission, context/fault/reap ownership; and ARM32 EL0 MMU,
  hardened ELF/FAT admission, scrubbed entry, authenticated SVC/fault/reap.
  Each emitted its architecture contract markers and `TEST PASSED`.
- blocked: AC-4 through AC-7 are not canonical matrix PASS until a usable
  source-matched self-hosted runtime produces native bundles and executes the
  SSpec/docgen. Direct QEMU receipts cannot substitute for those owners.
- impl: AC-7 source uses bounded process execution, typed command evidence, and an exact 24-row oracle (3 PASS, 15 BLOCKED, 6 POSTPONED); AC-8 and AC-9 Todo/document contracts are synchronized.
- blocked: The available self-hosted runtime crashed with exit 139 when executing the modern SSpec, and its earlier `spipe-docgen` attempt also crashed with exit 139. Neither unchanged command will be retried this session; no handwritten manual substitutes for generated evidence.
- impl: The stale runtime crash was traced to an obsolete two-argument
  `rt_env_set`; current source and its two-text ABI admission are correct. A
  full bootstrap now builds and sanity-checks Stage 2 after completing the
  missing typed parser-contract owner.
- impl: Stage 3 now opts into the existing transient per-file surface pipeline;
  its command hash and transcribed environment bind the opt-in, compiled-AOT
  mode transport is admitted, and the successful lifecycle fixture covers two
  physical sources plus one alias. A missing `defer_unsupported_marker`
  declaration that blocked Stage 2 was also restored; Stage 2 rebuilt with
  `3 compiled, 855 cached, 0 failed` and passed sanity.
- blocked: The final Stage 3 cycle released ten physical surfaces, then grew
  from about 325 MiB to 17 GiB without an eleventh release receipt. Glibc arena
  and trim policy improved the early RSS checkpoint but did not bound this
  later owner. The mandatory three-cycle cap was reached; no Stage 4 artifact
  was deployed and SSpec/docgen were not retried with the stale release binary.
- tracking: Todo DB rows 784-805 retain all shared, Linux, Windows, FreeBSD, and macOS owners.
- impl: AC-11 host-independent source is complete: FAT32 overwrite/extension/
  zero-hole semantics, canonical object IDs and alias retirement, concrete
  SOSIX backend, shim retention, and dup/fork/exit lifecycle hooks are present.
- tests: `sosix_fat32_positioned_io_spec.spl` and its mirrored operator manual
  retain fail-closed source, missing-environment, and qualified admission flows
  with REQ-SQ-018..020 traceability. The qualified wrapper runs each focused
  spec once only after runtime and linked-kernel admission.
- blocked: No admitted source-matched Stage-4 runtime or fresh positioned
  x86_64 kernel ELF exists. Runtime SSpec, docgen, `sspec-maintain`, and live
  QEMU PASS remain open; source self-test and the Rust seed cannot close them.
