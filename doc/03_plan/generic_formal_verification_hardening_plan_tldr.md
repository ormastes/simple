# Generic formal verification hardening — TLDR

<!-- codex-architecture -->

[Full plan](generic_formal_verification_hardening_plan.md). Baseline: `release_phase3` at `e6a4904a9faf67c4ee11d199cb197b002a9bf21c`, inspected 2026-10-18.

The retained eight-target Lean project passes its model checks. That proves neither the production compiler nor source-to-proof correspondence. Reviewed donor bridges, reference fixtures and unrun tests remain separate evidence; this document does not mark them landed.

Preserve all seven generic gates and C1–C7 formal obligations. Connect actual typed/specialized/woven artifacts to obligations, generated Lean, theorem roots, trusted replay and exact published artifacts. Missing translations, unsupported constructs, incomplete closure and unavailable proof authority must refuse admission.

Common contracts belong in `src/compiler/00.common/assurance/`; substitution stays in mono, VIR in MIR, translation in the backend, and process/trust control in verify. Reuse existing interfaces, codecs, SSpec and replay owners.

Bind owner/body/effects/Throws, arguments, bounds/witnesses, profile/configuration, collection backend/tag/layout, target/ABI, loader generation and ordered aspect weaving. Test each relevant mutation against real cache and publication paths. Avoid caller-controlled success flags and hash-only semantic cache collisions.

The confirmed effect-transport bug drops declared effects from rewritten generic caller signatures and omits them from the archive signature digest. Its correction is separate source work, not a landed or runtime-qualified fix; digest omission alone does not establish a replay bypass.

Bound specialization/proof caches, recursion and workers. Preserve live leases across eviction/unload; measure cold/warm time, code size and peak RSS before accepting budgets. Do not introduce repeated whole-tree scans or global cache registries into hot paths.

Implementation order: baseline/bug closure → generic semantics → admitted formal subset → trusted proof replay → dynamic/profile invalidation → resource/engine qualification → guarded landing. Real negative controls and a calibrated existing runner are mandatory. Reject placeholder proofs, undeclared axioms, solver unknown/timeout and missing evidence.

Next inspect: `src/compiler/40.mono/monomorphize_integration.spl`, `mono_archive_types_v1.spl`, common `formal_interfaces.spl`, MIR `verification_ir.spl`, Lean backend, and verify `replay_runner.spl`. Root owns composition/landing; an independent reviewer checks each phase. No overall formal-verification PASS is established.

2026-10-19 status (§12): new manual `MonoBoundaryModel` Lean target states variant-shadowing owner preservation (PR #3807), E-MONO-041 owner proof and E-MONO-033 mono→MIR boundary soundness under a diagnostic-coverage premise. Source-coded only — not kernel-built (no Lean toolchain on the authoring host). Class-static template inference is a TODO pending its branch landing.
