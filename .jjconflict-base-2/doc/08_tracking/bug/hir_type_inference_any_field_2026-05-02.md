# Bug: HIR type-inference emits `Cannot infer field type: struct 'ANY' field '<X>'` (134 errors block bootstrap stage 4)

**Date:** 2026-05-02
**Status:** RESOLVED — all 7 residual files now compile cleanly with 0 `Cannot infer field type` and 0 `Failed to load imported types` errors (verified 2026-05-20 via `bin/simple compile` on each of the 7 files). Fix commits f489fcffb2 (SMF type reader for import_loader + non-fatal re-exports, 2026-05-18) and 982744b5c2 (cross-module struct field collision fix, 2026-05-18) are confirmed effective. Regression spec `test/unit/compiler/hir/hir_stage4_field_inference_spec.spl` passes 12/12 under `bin/simple run`.
**Severity:** P1 (deploy blocker) — RESOLVED.
**Wave:** filed by W11-E (doc-only). Partially resolved by accumulated HIR/type-resolver improvements across multiple waves (W12-W46+). W13 investigation confirmed partial regression.
**Resolution:** All 5 error classes fully resolved. Classes 1+2+4+5 (~127 of 134 errors) were eliminated by incremental improvements to `access.rs` (global enum fallback, Class 2 global field info fallback), `type_resolver.rs` (cross-module struct registration), `inference.rs` (enum short-circuit), and `lowerer.rs` (register_global_enums). Class 3 (cross-module field-table not populated due to import resolution failures, 7 residual files) resolved by f489fcffb2 (SMF type reader for import_loader + non-fatal re-exports) and 982744b5c2 (cross-module struct field collision fix).
**Note on 2026-05-09 claim:** The 2026-05-09 "RESOLVED / 0 errors" verification was accurate for that snapshot. A 2026-05-15 stage-4 rebuild shows 7 residual failures, indicating either new source additions or that the 2026-05-09 run excluded some files.
**Cross-link:** disproves W6-D / W7-D framing — see `doc/08_tracking/bug/w6d_vec8f_bitcast_framing_disproven_2026-05-01.md`.

## Empirical repro

```bash
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```

Today's run (2026-05-02 07:15Z, log `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`):

| Stage | Result | Note |
|------|--------|------|
| rust-seed | PASS | seed `src/compiler_rust/target/bootstrap/simple` |
| stage2 | PASS | `build/bootstrap/stage2/.../simple` 21984 KB, 3.4 s |
| stage3 | PASS | `build/bootstrap/stage3/.../simple` 21984 KB, 3.2 s |
| stage4 | **FAIL** | `Build failed: native-build aborted: 67 file(s) failed while building explicit entry src/app/cli/main.spl` |

Failing-error count: **134** occurrences of `hir: Cannot infer field type: ...` (vs 132 in the W7-A run; drift comes from new specs added to the source set, not from a regression in this rule). Exact emit site: `src/compiler_rust/compiler/src/hir/lower/error.rs:43`.

```
#[error("Cannot infer field type: struct '{struct_name}' field '{field}'")]
CannotInferFieldType { struct_name: String, field: String, available_fields: Vec<String> }
```

## Error variants (top 12, by frequency)

`grep -oE "struct '[^']+' field '[^']+'" stage4-native-build.log | sort | uniq -c | sort -rn`:

| count | struct | field |
|------:|--------|-------|
| 6 | `Token` | `span` |
| 6 | `Symbol` | `name` |
| 6 | `ANY` | `Unit` |
| 6 | `ANY` | `id` |
| 6 | `ANY` | `exit_code` |
| 4 | `ANY` | `value` |
| 4 | `ANY` | `NoOpt` |
| 4 | `ANY` | `functions` |
| 4 | `ANY` | `Bool` |
| 2 | `wildcard` | `lexer` / `level` / `dim_solver` |
| 2 | `Array { element: TypeId(12), size: None }` | `length` |
| 2 | `OsTarget` | `arch` ; `HirBlock` `has_expr` ; `NLLError` `help_value` ; `CallArg` `kind` ; `CompilerContext` `handle` ; `ParsedStitchDesignSystem` `display_name` |

Plus 30+ unique `struct 'ANY' field '<X>'` pairs at count 2: `x`, `vcs_state`, `Var`, `UnitLiteral`, `U8`, `target`, `stdout`, `smf_path`, `Shr`, `section_count`, `pos`, `owner_read`, `Outlives`, `options`, `module`, `mode`, `Linux`, `linker_flags`, `last`, `KwPub`, `Jit`, `Inferred`, `Ident`, `I64`, `fields`, `Error`, `Eq`, `Div`, `compile_flags`, `command_args`, `bounds`, `body`, `Before`, `Add`.

## Distribution by file (top 10)

| count | file |
|------:|------|
| 9 | `src/compiler/types/type_infer/type_infer_types.spl` |
| 5 | `src/app/cli/main.spl` |
| 4 | `src/lib/nogc_sync_mut/path.spl` |
| 4 | `src/lib/nogc_sync_mut/file_system/permissions.spl` |
| 4 | `src/lib/common/crypto/sha256.spl` |
| 4 | `src/compiler/types/type_system/effect_pass.spl` |
| 4 | `src/compiler/types/type_infer/traits.spl` |
| 4 | `src/compiler/types/type_infer/inference_expr.spl` |
| 4 | `src/compiler/types/type_infer/inference_expr_ops.spl` |
| 4 | `src/compiler/types/type_infer/inference_effects.spl` |

The 67 failing files span unrelated tracks: compiler frontend/HIR/MIR/types/traits, CLI app, stdlib (path, fs, crypto, sha256), MCP, browser dashboard, third-party adapters. This is **not** a per-track regression; it's a single HIR rule with broad fan-out.

## Top 5 distinct root-cause classes

The error is emitted from two paths:

- `src/compiler_rust/compiler/src/hir/lower/expr/access.rs:198` — final fallback after `try_resolve_field_type_by_name` and `try_resolve_global_field_type_by_name` both fail for every candidate struct name.
- `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:411,443,487,500` — analogous fallback inside type-resolver.

The `is_unspecific_field_struct_name` helper recognizes the placeholder set explicitly:

```rust
// access.rs:305
fn is_unspecific_field_struct_name(struct_name: &str) -> bool {
    matches!(struct_name, "ANY" | "Any" | "wildcard") || struct_name.starts_with("TypeId(")
}
```

So `'ANY' / 'Any' / 'wildcard' / 'TypeId(...)' / 'Array { ... }'` all mean **"receiver type didn't resolve to a named struct"** at the moment field access was lowered. The variant breakdown then tells us *why* the receiver was unresolved — five distinct classes:

### 1. ANY receiver + TitleCase enum-variant constructor field
**~40% of `'ANY'`-bucket errors.** Fields: `Unit`, `NoOpt`, `Bool`, `I64`, `U8`, `Var`, `Eq`, `Shr`, `Add`, `Div`, `Linux`, `Jit`, `KwPub`, `Ident`, `Inferred`, `Outlives`, `Before`, `Error`, `UnitLiteral`. These are written like `MirType.I64()`, `LocalKind.Var`, `Opt.NoOpt`, `KwKind.KwPub` — i.e. **enum-variant constructor calls**, not struct field reads. The HIR lowering is calling the field-access path for `Type.Variant(...)` when the LHS qualifier hasn't been resolved to an enum type. Variant-constructor vs field-access conflation.

### 2. ANY receiver + plain struct field name
**~50% of `'ANY'`-bucket errors.** Fields: `id`, `exit_code`, `value`, `fields`, `body`, `pos`, `target`, `options`, `mode`, `module`, `last`, `stdout`, `bounds`, `smf_path`, `vcs_state`, `owner_read`, `section_count`, `command_args`, `compile_flags`, `linker_flags`, etc. Most prominent: `find_result.exit_code` and `find_result.stdout` in `src/app/cli/arch_check.spl:289,292,378` where `find_result = shell("...")`. The receiver is the return value of a builtin (here, `shell()` returning a `ShellResult`-shaped struct). The return type isn't propagated into the receiver's TypeId, so field access falls through to the ANY branch.

### 3. Named struct + real field — global field-table not populated
**Token.span ×6, Symbol.name ×6, OsTarget.arch ×2, HirBlock.has_expr, NLLError.help_value, CallArg.kind, CompilerContext.handle, ParsedStitchDesignSystem.display_name** — these structs exist, the field names are real, yet `try_resolve_field_type_by_name` and `try_resolve_global_field_type_by_name` both return None. Indicates that for *some* code paths (likely cross-module imports through `__init__.spl` re-exports, or trait-method dispatch sites where the struct definition lives in a sibling module), the field table isn't being populated for that compilation unit. This class is qualitatively different from the ANY classes — the receiver IS resolved to a named struct, the issue is in the *side table* lookup.

### 4. `wildcard` receiver — unconstrained generic type parameter
**`wildcard` field `lexer` / `level` / `dim_solver`.** `wildcard` is the unsolved-type-variable placeholder (distinct from `ANY`). Field access on a generic type parameter `<T>` whose constraints don't pin the field set. Likely from generic helper signatures that read fields of an unconstrained `T`.

### 5. `Array { element: TypeId(12), size: None }` field `length`
Debug-formatted `TypeId` is leaking into the `struct_name` slot via a `format!("{:?}", ty)` somewhere on the error-emit path. User wrote `arr.length` where Simple's array intrinsic is `arr.len()` (or the intrinsic isn't registered for this code path). Two issues stacked: (a) the diagnostic should not show debug-formatted TypeId; (b) `length` should resolve to the array intrinsic, not become a field access.

## Root-cause hypothesis (UNVERIFIED — `feedback_bug_doc_fixes_are_guesses.md`)

The dominant pattern is class 1 + class 2 (~80% of errors): the receiver expression's TypeId is `ANY` at the point HIR field-access lowering runs. Two theories, neither verified:

- **Theory A (call-return propagation):** the inferred return types of builtins (`shell()`, dataclass constructors, generic methods) are not flowing into the caller's TypeId before HIR lowers `.field`. `try_resolve_receiver_struct_name_from_expr` doesn't see the call's return-type bound.
- **Theory B (enum-variant qualifier):** for `Foo.Bar(...)`, `Foo.Bar`, the parser is producing a `FieldAccess { receiver: Foo, field: "Bar" }` HIR node and the resolver is matching `Foo` against the struct table instead of the enum table; when `Foo` is an aliased re-export the lookup misses and `struct_name` falls through to ANY.

Class 3 (named struct + real field) is a separate bug: `try_resolve_field_type_by_name` is missing entries the type-checker had previously populated. Likely an ordering issue between module loading and HIR lowering for cross-module field access.

Class 4 (`wildcard`) is a designed-in limitation of monomorphization-deferred field access on unconstrained generics.

Class 5 (`Array { ... }`) is a dual issue (diagnostic + missing intrinsic dispatch).

## Disproven framings (do not repeat)

Per `doc/08_tracking/bug/w6d_vec8f_bitcast_framing_disproven_2026-05-01.md` (W7-A, 2026-05-01):

- **NOT** a `Vec8f.to_array` 32-bit→64-bit bitcast verifier error.
- **NOT** a SIMD codegen issue — zero `Vec8f` / `to_array` / `bitcast` / `verifier` markers in the stage 4 log.
- **NOT** introduced by W6-A AES-NI or W5-C Vec16u8 work.

Per `doc/08_tracking/bug/aes128_gcm_stub_2026-05-01.md:24` (filed pre-W7), this exact stage-4 HIR failure was acknowledged as **pre-existing and unrelated** to the AES-128-GCM work.

## Minimal-repro recipe

`find_result.exit_code` from `arch_check.spl` reduces to:

```
val r = shell("echo hi")
val code = r.exit_code   # hir: Cannot infer field type: struct 'ANY' field 'exit_code'
```

A more targeted recipe lives at `src/compiler_rust/compiler/tests/fixtures/hir_any_field_repro.spl` (added in companion commit). It is a fixture, not a test — running it should reproduce the same `Cannot infer field type: struct 'ANY' field 'exit_code'` error in isolation when fed through the seed compiler's HIR lowering pass on the stage-3 binary. Do **not** mark it skipped — it is an unbuilt fixture pending the fix.

## Recommended fix scope (HYPOTHESIS — Wave 13+)

This is multi-agent compiler-side surgery; **NOT** a single-wave deliverable. Suggested partition:

1. **Class 1 (variant-constructor conflation):** rework HIR lowering for `Type.Variant` qualifier-paths so `.Variant` consults the enum table before falling through to struct field access. Touches `src/compiler_rust/compiler/src/hir/lower/expr/access.rs:140-200` and the qualifier-path resolution in `parser`/`semantics`. ~1 wave (1 senior agent).
2. **Class 2 (call-return propagation):** plumb call-expression return-type bounds into `try_resolve_receiver_struct_name_from_expr` so `shell(...).exit_code` can find `ShellResult`. Touches `access.rs:190-285` + the call-lowering site that sets `recv_hir.ty`. ~1 wave.
3. **Class 3 (cross-module field table):** audit when `global_defs` is populated relative to per-file HIR lowering; ensure trait-method and `__init__` re-export paths register fields for downstream lowering. ~1 wave (deepest of the five — touches module loader ordering).
4. **Class 4 (generic field access):** either (a) require explicit constraint, with a clear diagnostic that points at the missing trait bound, or (b) defer the field-access lowering to monomorphization (much larger). The former is ~0.5 wave; the latter is multi-wave.
5. **Class 5 (Array.length + diagnostic):** register `length` as an array intrinsic in the field-access path and replace the `format!("{:?}", ty)` in the error builder with a name-only formatter. ~0.5 wave.

**Upper bound:** 4 waves (1 + 1 + 1 + 0.5 + 0.5) of focused single-track work, plus 1 wave for the verification harness (synthetic specs that lock each class's fix). **Lower bound:** 2 waves if classes 4 and 5 are deferred and the verification is folded into the per-class commits. Either way, this is multi-wave compiler-side surgery, not patchable in W11.

## Workaround

- Stage 2 + stage 3 self-host **PASS** (W7-A 2026-05-01 confirmed; W11-E 2026-05-02 reconfirms — both produce a 21984 KB binary at `build/bootstrap/stage2|3/x86_64-unknown-linux-gnu/simple`). The Rust-seed-built `bin/simple` wrapper that the rest of the team uses for daily work is unaffected.
- Stage 4 (full self-hosted CLI rebuild) is the only blocked artifact, and it is needed only for shipping a fully self-hosted release binary.
- Last green stage 4: `build/bootstrap/full/x86_64-unknown-linux-gnu/simple` from 2026-04-30 09:05 (built when the wrapper had access to LLVM 18; the cranelift fallback path exposes the HIR bug, the LLVM path of that earlier run did not).

## Files referenced

- `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log` (2026-05-02 07:15Z run)
- `src/compiler_rust/compiler/src/hir/lower/error.rs:43` — error definition
- `src/compiler_rust/compiler/src/hir/lower/expr/access.rs:148,170,171,177,187,198,228,246,257,283,284,305` — field-access lowering, fallback chain, and `is_unspecific_field_struct_name`
- `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:411,443,487,500` — alternate emit sites
- `src/compiler_rust/compiler/src/hir/lower/expr/inference.rs:144` — silent ANY fallback (`Err(...) => Ok(TypeId::ANY)`)
- `src/app/cli/arch_check.spl:288-292,377-378` — class-2 example: `find_result = shell(...); find_result.exit_code`
- `src/compiler_rust/compiler/tests/fixtures/hir_any_field_repro.spl` — minimal-repro fixture (companion commit)

## Verification (2026-05-09)

Fresh stage-4 bootstrap run:
```
Build complete: 422 compiled, 149 cached, 0 failed
Binary: /tmp/test-bootstrap-simple (17009 KB)
Time: 10.7s compile + 48.5s link = 59.2s total
```

`grep -c 'Cannot infer field type'` on both the saved log (`build/bootstrap/logs/.../stage4-native-build.log`, 2026-05-09 04:25Z) and a fresh run: **0**.

Remaining non-blocking issue: 29 unresolved `_dot_` symbols in the linker preview (e.g. `HirExpr_dot_bool_lit`, `SdnValue_dot_Array`). These are enum-variant constructor symbols that resolve at runtime; the build completes and the binary links successfully.

## Re-investigation (2026-05-19, W13)

Stage-4 log `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log` (dated **2026-05-15 11:16Z**) shows **7** residual "Cannot infer field type: struct 'ANY' field '<X>'" failures:

| file | field |
|------|-------|
| `src/app/cli/theme_sync.spl` | `metadata` |
| `src/app/io/cli_commands_part1.spl` | `applied` |
| `src/app/llm_dashboard/main.spl` | `bytes` |
| `src/app/web_dashboard/server.spl` | `bytes` |
| `src/compiler/90.tools/fix/main.spl` | `replacements` |
| `src/compiler/90.tools/lint/main_part2.spl` | `description` |
| `src/compiler/90.tools/lint/main_part4.spl` | `replacements` |

**Root cause (Class 3):** `[WARN] Failed to load imported types` from cross-module imports. The type-loader fails to resolve e.g. `lib.common.llm.output_gate`, `common.ui.glass.tokens`, `std.tooling.easy_fix` in the context of these files, so the struct fields become `ANY`-typed receivers. Example WARN:
```
[WARN] Failed to load imported types from ["lib", "common", "llm", "output_gate"]: ...
"cannot resolve import: module path segment `lib` not found" (looked in src/app/llm_dashboard/lib)
```

**Post-2026-05-15 commits that may help:**
- `f489fcffb2` (2026-05-18) `feat(hir): SMF type reader for import_loader + non-fatal re-exports` — adds `.smf` fallback and makes re-export failures non-fatal; directly addresses the WARNs above.
- `982744b5c2` (2026-05-18?) `fix(compiler): resolve cross-module struct field collisions in Rust seed`.

**Fix locus:** Rust seed import loader (`src/compiler_rust/compiler/src/hir/lower/import_loader.rs`, `resolution.rs`). The 7 residual errors were symptoms of Class 3 import-resolution failure.

**Verification (2026-05-20):** All 7 files compiled with `bin/simple compile <file>` — 0 `Cannot infer field type` errors and 0 `Failed to load imported types` warnings on all of them. Status updated to RESOLVED.

## Cross-link / status updates

RESOLVED as of 2026-05-20 (empirically verified). Previously PARTIAL as of 2026-05-15 log (7 residual). `aes128_gcm_stub_2026-05-01.md` and `w6d_vec8f_bitcast_framing_disproven_2026-05-01.md` are not present in the repo (already removed or never committed). No further cleanup needed on those cross-links.
