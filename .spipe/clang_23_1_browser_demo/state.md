# Feature: Clang 23.1 Browser Demo Migration

## Raw Request
$sp_dev in separate worktree migrate current clang-18 dependency to clang 23.1. do research more what to check and migrate. deep plan and migrate and check adhoc bootstrap too. if there are critical problem which 23.1 not support problem. 1. migrate clang 18 dependency to 23.1 and 2. complete the browser demo.

## Task Type
feature

## Refined Goal
Migrate every owned Clang/LLVM 18 or version-pinned browser-demo/bootstrap dependency to Clang/LLVM 23.1, preserve supported cross/freestanding behavior, document any genuine 23.1 incompatibility, and produce passing browser-demo plus SimpleOS QEMU rendering evidence from the isolated worktree.

## Acceptance Criteria
- AC-1: A repository-wide owned-code inventory identifies every Clang/LLVM executable name, package/version pin, search path, environment variable, diagnostic, bootstrap contract, browser-demo contract, and documentation reference relevant to the 18-to-23.1 migration; vendored sources are excluded.
- AC-2: Research records authoritative Clang/LLVM 23.1 availability, tool naming, installation/distribution constraints, target support, linker/runtime compatibility, removed/deprecated behavior, and macOS/Linux/Windows implications, with explicit critical-risk conclusions.
- AC-3: Final feature and NFR requirements plus architecture, detail design, migration plan, system-test plan, agent-task plan, executable SSpec, and mirrored operator manual exist under the canonical repository paths and trace all acceptance criteria.
- AC-4: Production scripts and configuration prefer and validate Clang/LLVM 23.1 consistently; no owned production path silently selects Clang/LLVM 18 or hardcodes the obsolete browser-demo `clang-20` dependency.
- AC-5: Tool discovery fails closed with actionable diagnostics when a compatible 23.1 compiler/toolchain is unavailable and rejects an incompatible or falsely labeled compiler.
- AC-6: Focused tests cover discovery precedence, exact version admission, missing-tool behavior, cross/freestanding target invocation, and browser-demo compilation without placeholder passes or fabricated runtime stubs.
- AC-7: The ad-hoc bootstrap path completes with the migrated toolchain or produces retained evidence of a concrete upstream 23.1 incompatibility after at most three fix cycles; the exact candidate binary, commands, versions, hashes, logs, and unsupported behavior are recorded.
- AC-8: The browser-demo client builds successfully with Clang/LLVM 23.1, is staged into the SimpleOS image, and the canonical SimpleOS WM QEMU wrapper reaches boot and retains its required framebuffer, font, keyboard, pointer, and browser-content evidence bundle.
- AC-9: Required compiler/core/lib/MCP checks, direct-runtime and numbered-artifact guards, rendering source-coupling guard, SPipe quality/docgen checks, and relevant bootstrap/browser-demo/QEMU gates pass once against final unchanged inputs.
- AC-10: Operator guides, bootstrap setup documentation, generated/manual SPipe documentation, changelog, and all changed workflow references consistently describe the 23.1 toolchain and recovery/install procedure; no stale 18/20 instructions remain in owned scope.
- AC-11: Final verification audits every AC against retained evidence and reports `STATUS: PASS`; any genuinely unsupported Clang/LLVM 23.1 behavior remains a concrete open blocker rather than a compatibility fallback or downgraded warning.

## Scope Exclusions
- Vendored LLVM/Clang source and third-party package internals are inventory-only unless an owned integration patch is required.
- Unrelated GPU-offload, WM event-routing, ARM64 kernel, and compiler work in the primary dirty worktree is not merged into this branch.
- Release tagging and pushing are excluded unless separately requested after verification PASS.

## Cooperative Review
- Local source inventory sidecar: bounded read-only research of owned Clang/LLVM references and call chains.
- Domain sidecar: authoritative Clang/LLVM 23.1 compatibility, packaging, target, and removed-feature research.
- Verification sidecar: bounded read-only bootstrap/browser-demo/QEMU gate and artifact analysis.
- Merge owner and final reviewer: root Codex agent.
- Shared interfaces: `resolve_clang_23_1_toolchain`, `validate_clang_23_1_toolchain`, and existing browser-demo/QEMU wrapper interfaces unless research proves established repository names should be retained.
- Manual flow steps: `Inspect the installed Clang 23.1 toolchain`; `Build the browser demo with the admitted compiler`; `Run the ad-hoc bootstrap smoke`; `Boot SimpleOS and exercise browser content`; `Validate retained rendering and input evidence`.
- Setup/checker helpers: reuse existing setup and evidence wrappers where possible; any new placeholder must use `fail(...)` until implemented.
- Generated-manual review owner: root Codex agent after sidecar findings are merged.

## Phase
verification-blocked

## Log
- dev: Created state file with 11 acceptance criteria (type: feature).
- research: Merged local, domain, and gate sidecars; user-selected final requirements written for the 23.1 family with rc2 truthfulness.
- design: Architecture, detail design, system plan, agent tasks, executable SSpec, and mirrored operator manual created.
- implementation: Pure-Simple backend, SimpleOS guest filesystem/tool launch, explicit provider builder, and browser build admission migrated in parallel.
- blocker: Upstream inkwell 0.9/llvm-sys 221 stop at LLVM 22; Rust in-process LLVM 23.1 integration cannot be completed without an upstream release or maintained fork.
- verify: Signed rc2 provider source accepted after importing and fingerprint-checking the release key; bounded provider build active.
- verify: Provider, coherent target smoke, browser ELF build, staging, disk image, and focused contracts passed.
- blocker: Fullscreen QEMU exhausted three cycles. `native_probe/simple` fabricated `rt_array_sort`; the older external Phase artifact did not reach current scanout/desktop readiness; no fourth cycle was run.
