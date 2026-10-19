# Native entry discovery selects an empty legacy environment facade

Status: reproduced by closed Phase3 builds; minimal resolver fix applied to shared `release_phase3`, pure-Simple regression execution pending. No compiler rebuild or closed-entry retry performed by this review. Root owns commit/review admission.

## Evidence and cause

The retained final-cycle build at `build/native_probe/phase3-original1220-80030-20261010/chunk12-final-cycle3/module-0773/compile/retained.log` reports `module std.env has no exported item env_get_or` and the consequent unresolved call at `src/compiler/10.frontend/core/_AstExpr/accessors.spl:179`. The request's source manifest admits only `src/lib/nogc_async_mut/env/mod.spl` from the environment package. Its frozen bytes contain legacy submodule `import` statements and no export declarations. The log identifies the selected physical facade as `lib.nogc_async_mut.env.mod`.

This is not evidence that a missing sync-tier directory corrupted the capture. Native entry discovery in `src/compiler/80.driver/driver_source_loading.spl` probes `.spl`, then `mod.spl`, then `__init__.spl` within each existing root/family. The earlier async tier already supplies `env/mod.spl`, so adding the later sync-tier directory alone would not change selection. The full release tree contains `nogc_async_mut/env/__init__.spl`, which exports `variables.env_get_or`, and its real `variables.spl` implementation. The chosen `mod.spl` masks that facade before the closure can follow it.

Canonical directory-module resolution in `src/compiler/99.loader/module_resolver/resolution.spl:475` recognizes `__init__.spl`; it does not select `mod.spl` as the directory entry. The proposed native adjustment prefers that initializer over the legacy fallback, keeping existing root/family ordering and `.spl` handling unchanged. File-versus-directory ambiguity policy is outside this candidate.

## Version and ownership boundary

Reviewed immutable release: `a4ca8226e21f8df3374c3eea1109e6365c4d7d79`. Producer source donor: `990fb41d98e2143e22f0dfda11178e0b458efdd4`. Both retain this precedence. Their source-loading difference is the visibility of `_driver_try_numbered_entry_import_rel_checked_v1`, not facade choice. Shared-main clean files differ from release; the candidate is generated against the immutable release, not copied over the dirty working tree.

The earlier release-based proposal remains in `build/native_probe/phase3-memory-perf-review-20261011/env-facade-proposal/` for provenance; do not overwrite the branch file with that full candidate. The actual change was adapted to the branch's existing `driver_source_loading.spl`: exactly six initializer/legacy probe pairs are reordered, with one explanatory comment. No pairs are missing on this older branch. Its numbered-directory helper uses `rt_file_exists` and a text result rather than release's checked source-root result; those differences are preserved. No source read, export validation, cache identity, or diagnostic is bypassed. Applying the fix to an incomplete historical capture cannot recover initializer/provider files that are absent; any future capture must include the selected real source closure.

## Regression and qualification plan

`test/01_unit/compiler/bootstrap/entry_package_facade_precedence_spec.spl` exercises actual resolver/scanner APIs against a temporary frozen tree:

- An environment facade with both carriers selects `__init__`, retains the `std.env.variables` export edge, and resolves its named provider.
- An unrelated package follows the same rule, preventing an env-specific exception.
- A legacy-only package retains its existing `mod.spl` fallback.
- A direct `.spl` file retains precedence when both directory carriers exist.

The test saves `SIMPLE_SCV_SNAPSHOT_ROOT` using the nullable `std.io_runtime.env_get_nullable` facade and restores nil with `env_remove_process`; present values, including empty text, go through `env_set`. It does not collapse absent state to empty. Helper signatures were inspected: directory creation, writes and environment mutation return `bool`; file reads and absolute paths return `text`; the clock returns `i64`.

These tests are prepared but **UNRUN**. Static validation on the actual modified branch file confirmed all six initializer-before-legacy pairs, retained preceding direct-file returns, and an identical multiset of noncomment statements before/after. `git diff --check` passed for the production file. These are source checks, not a simulation or execution of the resolver. The closed native failure is the baseline evidence; no executable red/green TDD result is claimed. Run once under the independently qualified full pure-Simple CLI when available; then qualify real environment exports/closure under that same producer. Do not use the Rust seed as the test runtime. No timing, RSS improvement, or Phase3 completion is claimed. All four final-cycle builds remain closed at their attempt cap.

For an independently authorized fresh-entry capture, the narrower bootstrap workaround is changing only the accessor import from `std.env.{env_get_or}` to the explicit provider `std.nogc_sync_mut.io_runtime.{env_get_or}`. The real public function already exists in the captured `nogc_sync_mut/io_runtime.spl:434`. The shorter `std.io_runtime` facade does **not** export `env_get_or` in the original capture, so that intermediate proposal was corrected before capture or execution. A prepared `accessor-fresh-capture-workaround.patch` in the proposal directory includes the canonical bug/recovery marker. Its `recover` value is the actual resolver-fix commit `a38b7d7ede8b8abfe6a62f349206ffd1c18287ec`; apply and qualify that fix before removing the workaround. The original-source commit `6bf3276a4344923bea1dae84c933b2aeda13db58` is only a preimage/provenance reference, not a recovery fix (its accessor text matches the closed capture after newline normalization). Apply only after verifying a fresh capture's accessor matches that preimage, then record its actual private commit and new closure pins. This patch is not applied here, is not the global facade repair, and does not authorize replaying a capped entry.

## Separate imported MIR type investigation

The prior direct-HIR logs reported imported `MirType`/`MirSignature` failures in consumers. Their defining source imports and re-exports exist. The closed log has no unresolved-owner advisory for those names and has no enabled `[ist-*]` projection trace. Tagged direct imports remove these diagnostics in the final pilot, but do not establish which owner-qualified binding failed. Release already carries qualified dependency materialization, recursive generic projection, Reference projection, and nominal owner work; PR #3042 additionally owns generic transport integration. No speculative type-context patch is included here. Optional/other projection gaps have historical explicit allowlist evidence and are not asserted as this failure's cause.
