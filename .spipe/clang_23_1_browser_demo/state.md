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
- verify: A later bounded current-source run passed the sort and concrete software-dispatch blockers and rendered Browser, Hello, and Clang surfaces, then failed closed because Aetheric shorthand retained 73 raw layer bytes and produced no material receipt.
- implementation: Reused the existing architecture/detail artifacts and restored the typed `parse_background_layers` path lost by tree-restore commit `7f5a55fa46e`; one reproducible linear layer plus base color now retains full GAP-2 stops/angle while unsupported layers remain a raw rejection witness.
- implementation: QEMU evidence now correlates software with solid/CPU receipts and host GPU with solid/CPU/Metal receipts; every path still requires rendered status, a strong digest, exact theme/source, and no rejection marker.
- verify: Migration contract passed 5/5 and both evidence wrappers passed shell syntax. The focused browser renderer and gradient specs reached the pre-existing `browser_renderer_protocol.spl` multiline-import parser failure before assertions; the QEMU wrapper contract also hit existing self-host interpolation semantics (`font_guest_path`, `handled_text`) after 5 passes. The three-cycle QEMU cap remains exhausted, so AC-8/9/11 are not marked complete in this session.
- implementation: A current-source focused x86_64 guest proved the custom-property loss in two owners: chained text concatenation erased its intermediate type into numeric `rt_any_add`, and dynamic `.index_of(":")` lowered through the unresolved freestanding path. The collector now keeps every concatenation statically `text`, and state parsing uses the existing `find_from` byte-search primitive.
- implementation: Backdrop admission no longer depends on freestanding `starts_with`/`split`/`to_i64`; it parses the exact ASCII grammar with bounded `byte_at` decimal accumulation and retains the 4px realized-blur and 300% saturation limits.
- verify: The retained focused Clang 23.1 guest passed exact collector/state/resolution/background/gradient/backdrop/memo receipts, including `backdrop-admission value=true:4:1700`, and exited through the expected debug port without a fault.
- verify: Canonical QEMU cycle 1 isolated backdrop admission. Cycle 2 cleared admission but exposed a page fault in a provisional global `rt_any_add` widening; that unsafe change was reverted and replaced with the typed producer fix. Cycle 3 rebuilt 6 modules with 725 cached and reached CPU-entry/font rendering without rejection or fault.
- blocker: Cycle 3 exhausted the 180-second readiness window while allocating repeated 1,048,576-element draw/font arrays and emitted neither desktop/browser-ready nor framebuffer/input/content evidence. The mandatory three-cycle cap is reached; AC-8, AC-9, and AC-11 remain incomplete and no fourth run was attempted.
- implementation: Reused one FontRenderer atlas across size-only config changes and cached the exact registered-font identity before rebuilding the 1.7MB renderer. The focused Clang 23.1 atlas guest proved one 1,048,576-element allocation, non-empty 16/32/16 batches, and a clean return to the cached 16px glyph generation.
- verify: Fresh canonical cycle 1 passed the former font stall and isolated a 193,664-element (`0x2f480`) window scratch allocation after Browser material admission. Cycle 2 lowered the existing attribution threshold only for diagnosis and mapped caller `0x82acbcc` to `backend_emu_adv.emu_draw_blur_rect`; the temporary threshold change was then reverted.
- implementation: Added an exact rolling-sum path for blur radii through seven. It retains one final division and clipped-edge sample counts, and the focused Clang 23.1 freestanding probe passed centered radius-4 plus clipped radius-2 byte parity against the retained square-tap oracle (`ENGINE2D_BLUR_EXACT_PROBE_PASS`, QEMU debug exit 7).
- blocker: Fresh canonical cycle 3 retained RIP `0x82ad0a0` inside `emu_draw_blur_rect`'s legacy square-tap loop, proving the production Browser command uses a radius above seven. The 180-second readiness gate again emitted no desktop/browser-ready or framebuffer/input evidence. The three-cycle cap is reached; resume from `doc/08_tracking/bug/simpleos_browser_large_radius_emu_blur_qemu_timeout_2026-08-04.md` and do not claim AC-8, AC-9, or AC-11.
- blocker: The deployed `bin/simple` could not execute the new unit spec or lint the three blur files: the test runner lost `std.spec`/`SoftwareBackend` imports after seed-sibling delegation failed, and lint exited 132 on `field access on nil receiver`. These are retained in `backend-emu-blur-spec.out` and `blur-lint.out`; the authorized provider artifact has no `test` command. Focused correctness therefore remains the exact freestanding probe, not Stage 4 or AC-9 evidence.
- implementation: A fresh ownership audit restored all ineffective material-provenance/sidecar experiments to the published branch state and preserved the unrelated generated Gradle EOL change. The retained three provider-candidate probes (`native_probe`, Stage 2, and Stage 3) all failed before compilation with `LLVM backend requested but 'llvm' feature not enabled`; no fourth pre-existing artifact was tried.
- research: The full pure-Simple CLI can drive the external LLVM backend without Rust `inkwell`, but final evidence needs a current-source provenance-verified Stage 4. Its required external family includes `clang`, `ld.lld`, `llc`, `opt`, `llvm-ar`, `llvm-nm`, `llvm-objdump`, `llvm-objcopy`, and `llvm-config`; hardcoded `cc`, `ld.lld`, and shell `nm` paths must fail closed through the admitted prefix.
- implementation: The signed `llvmorg-23.1.0-rc2` cached provider build installed and validated all nine tools in `build/toolchains/llvm-23.1.0-rc2`, emitted canonical absolute handoff paths, and retained hashes in `build/toolchains/llvm-23.1.0-rc2-provider-sha256.txt`. Pure-Simple routing and the LLVM-default QEMU wrapper contract remain in review before the Stage 4/QEMU gates.
- implementation: Rust native-project mangling now qualifies the exact legacy `__module_init_dynamic` with the module prefix and retains already-qualified initializer ABI names. The focused Rust regression passed 1/1; a fresh Stage 2 and Stage 3 each compiled 728 modules, linked without the former 33-object collision, passed sanity, and sealed Stage 3 provenance.
- blocker: The third and final bootstrap cycle reached Stage 4, loaded a 1,758-file closure, then terminated with SIGSEGV immediately after `phase2:surface:file:released path=src/app/cli/main.spl seq=1`. The full CLI, its essential-tools smoke, and the LLVM QEMU gate remain unavailable; no fourth bootstrap or QEMU attempt was made. Resume from `build/bootstrap-clang-23-1-stage4-cycle3.out` and `build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log` after repairing the streaming-surface parse-release owner.
- sync: Rebased onto `origin/main` at `34e7d0f303`, importing the load-bearing transient-scope-before-`ast_reset()` repair from `ec75d8c609`. The diagnosed Stage 4 lifetime defect is fixed in source, but the three-cycle cap remains exhausted; Stage 4, essential-tools, and LLVM QEMU must be rerun in a fresh scoped verification session before AC-8/9/11 or `STATUS: PASS`.
- blocker: The final bootstrap-portability gate exhausted three focused cycles after fixing macOS `/var` authority canonicalization and jj 0.38 non-colocated fixture setup. It now stops at `native architecture gate wiring missing`: line 235 expects three `check-llvm-simd-row-native-arch.shs` workflow references, while the Cranelift-isolated workflow has two trigger references and line 266 rejects an execution step. Retained log: `build/clang-23-1-final-bootstrap-portability-cycle3.log`; resolve the contradictory count contract before rerunning this gate.
- verify: A fresh portability cycle corrected the LLVM gate count to its two restoration triggers, restored all four retired-workflow push/PR triggers, and refreshed native-parity registration totals to 101/145 default and 102/146 expanded. Cycle 3 then stopped at stale C-backend provenance text: the checker requires `hirlowering_for_module(source_file, {})`, while the current owner correctly passes `retained_module_surfaces`. Retained log: `build/clang-23-1-portability-cycle3.log`; the feature-wide three-cycle cap prevented another edit/run or the prepared Stage4/QEMU commands in this turn.
