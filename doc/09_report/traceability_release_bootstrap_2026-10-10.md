# Traceability release-target bootstrap work

STATUS: WARN — protected integration and product implementation remain open.

The user requested `fix`, then `bootstrap ans land impls on release branch`. This work uses isolated branch `work/traceability-release-20261010` at initial release target `d66172f8fde`; unrelated worktrees are preserved. The new compiler pass permits at most three changed-source repair cycles and preserves all prior failures.

## Concrete change

Two calls incorrectly addressed the hoisted module-level `folded_global_scalar_type` as a MirLowering method. Both now call its defining function. The focused MIR regression checks clean HIR/MIR diagnostics, canonical immutable address storage and initializer symbols, text/bool scalar types, and linkage of the ordinary read return to its constant. The pre-existing suite now also rejects lowering diagnostics. The obsolete source-string oracle requiring the wrong calls was removed. Astra's local review found no remaining P0/P1 after corrections; local review is not authenticated release admission.

## Bootstrap evidence

- Phase2 compiler construction: PASS, 1,222 modules, zero compilation failures, 146.2 seconds compile+link.
- Fresh compiler HelloWorld construction and execution: PASS, exact `hello` stdout.
- Standalone SSpec orchestration runner construction: PASS, 217 modules, zero failures, 6.5 seconds. It delegates test execution to a general interpreter; its construction does not mean specs executed.
- Working and staged direct-env-runtime guards: PASS before later documentation changes.
- Traceability application construction: FAIL in HIR startup (SIGSEGV) for parallel and serial configurations; no application produced.
- Full CLI construction: compilation PASS for 2,570 modules, linking FAIL with 157 undefined core ABI symbols; no CLI produced.
- Actual focused MIR SSpec native capsule: construction PASS (406 modules, zero failures, 35 seconds); execution FAIL (3 examples, 2 failures). Ordinary immutable read passed; both address-storage cases failed. Capsule exit zero is a separate recorded defect.
- Pre-existing complete MIR spec native construction: FAIL on unresolved `g_linkage`; no stubs allowed.
- Third/final focused diagnostic capsule: construction PASS (2 compiled, 404 cached); execution FAIL with the same 2 failed examples. Both inputs have zero HIR/MIR diagnostics. Integer shared+mutable source produced only the mutable address/static (1 address, 1 static); text/bool immutable source produced no addresses or statics. The bounded pass is exhausted; no further builds were retried. Private instrumentation was removed from the assertion-focused spec afterward.
- Compiler/lib/MCP/LSP checks and production smoke: NOT RUN, general tools unavailable.

All successful binary constructions used the Rust seed only for bootstrap construction. They are development Phase2 products, not admitted release artifacts. Immutable runtime inputs and producer digests are retained under `build/native_probe/traceability-release-*`. No shared deployment or version/tag publication has occurred.

## Integration gate

The live release line requires PR integration, Code Idiom & Structural Ratchet Gates, and SPipe Self Review Admission. The trusted checked-in review workflow exposes legacy `self_attestation`; the canonical SPipe guide says that cannot supply authenticated admission. No admission check has been fabricated or bypassed. The target is advancing; exact target reconciliation and current review are required before landing.

## Product scope

The original 20 REQ-TRC requirements, 40 AC-TRC cases and WP0–WP7 remain open. This compiler prerequisite fix does not implement or verify the complete traceability/SDN/Slop product. Its plan, architecture, test drafts and earlier receipts remain in the owned product worktree.

## Review-branch reconciliation

The review branch was rebased onto release snapshot `e40f0bbd001abdd134ab8b350cc0bb39a12b4833` after the bounded diagnostic pass. The two stale helper calls remained present on that target and the patch applied without conflicts. Bootstrap/test observations above belong to the earlier frozen `d66172f8fde` source plus the patch; they are not renewed exact-head qualification of this newer base. This change is draft-only until the two failed regressions, missing general-runtime checks and authenticated admission are resolved.
