# Bug: Rust seed mangler emits bare extern for free function shared across sibling split-part modules re-exported through a facade

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

- **Date:** 2026-07-30
- **Area:** `src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`
- **Class:** mangler bare-extern-on-re-export (same defect class as prior instances below)

## Symptom

Stage4 full-CLI native link fails with an undefined symbol:

```
"__find_substr", referenced from:
    _semantics__lint___SimdOpportunityLint__arithmetic_checks__lint_simd_elementwise_add in libspl_objects.a(mod_348.o)
    _semantics__lint___SimdOpportunityLint__arithmetic_checks__lint_simd_reduce_sum
    _semantics__lint___SimdOpportunityLint__arithmetic_checks__lint_simd_xor_loop
    _semantics__lint___SimdOpportunityLint__arithmetic_checks__lint_simd_elementwise_max
   (maybe you meant: _gc_async_mut__gpu__browser_engine__html_tokenizer___find_substr,
                     _semantics__lint___SimdOpportunityLint__loop_analysis___find_substr,
                     _tools__duplicate_check__math_utils__find_substr)
```

## Root cause

`_find_substr` is a free helper function DEFINED in
`src/compiler/35.semantics/lint/_SimdOpportunityLint/loop_analysis.spl` and CALLED
from its sibling split-part module
`src/compiler/35.semantics/lint/_SimdOpportunityLint/arithmetic_checks.spl` (and also
from `byte_checks.spl`). Both split-part files are re-exported (wildcard,
`export use ...*`) through the facade module
`src/compiler/35.semantics/lint/simd_opportunity_lint.spl`, which is how
`arithmetic_checks.spl` sees `_find_substr` in scope (via
`use compiler.semantics.lint.simd_opportunity_lint.*`).

The Rust seed's name mangler resolves the call site to a BARE extern symbol
(`__find_substr`, no module prefix) instead of resolving it to the defining
sibling module's fully-mangled symbol
(`_semantics__lint___SimdOpportunityLint__loop_analysis___find_substr`, per the
linker's own "maybe you meant" hint). This produces an unresolvable symbol at
native link time even though the function is unambiguously defined exactly
once in the reachable module graph.

## Real fix (belongs in the seed, not touched here)

`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs` should
resolve the call to the defining module's mangled symbol (per the facade
re-export chain) instead of emitting a bare extern when a free function is
brought into scope only via a wildcard re-export. This repo instance did not
modify the Rust seed; that is owned by another agent/session.

## Applied workaround (this change, pure Simple, source-level only)

Added an explicit direct import of `_find_substr` from its defining module in
the calling file, bypassing the facade re-export ambiguity:

`src/compiler/35.semantics/lint/_SimdOpportunityLint/arithmetic_checks.spl`:

```
use compiler.semantics.lint._SimdOpportunityLint.loop_analysis.{_find_substr}
```

added alongside the existing facade wildcard import
(`use compiler.semantics.lint.simd_opportunity_lint.*`). No other lines
changed; the defining file (`loop_analysis.spl`) was not touched.

## Prior instances of this same defect class

- `run_test_api_server_with_inject` — fixed in `b51e19436dde`
  (`src/app/office/sheets/access_server.spl`, imported direct from
  `ui.standalone.bootstrap` instead of the `app.ui.standalone` package
  re-export).
- `_text_index_len` — fixed in `6c55ea6a60c7`
  (`src/compiler/90.tools/fix/rules/impl_/lint_short_grammar.spl`, added an
  aliased explicit import from the defining module,
  `compiler.tools.fix.rules.helpers.{_text_index_len as compiler_fix_text_index_len}`,
  to disambiguate two wildcard imports both exposing the name).
- `extract_compiler_coverage_manifest_sdn` / `strip_compiler_coverage_manifest_blocks`
  — fixed in `54c7749694` (`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`,
  re-pointed from the `std.test_runner.test_executor_parsing` variant-resolution
  facade to the concrete `nogc_sync_mut.test_runner.test_executor_parsing` module).

## Update 2026-07-30 (proactive batch sweep) — discriminator validated, 5 more instances fixed

### Discriminator search

Goal: find latent instances of this defect BEFORE the next 25-minute build attempt
surfaces them one at a time. Two competing hypotheses were tested against the four
known-fixed instances above:

1. **Underscore-prefix and/or multi-definition ambiguity.** Checked each known
   symbol for global uniqueness (`grep -rn "^fn NAME(" src/{compiler,lib,app}`,
   excluding vendor):
   - `_text_index_len` — 2 definitions (ambiguous) — underscore-prefixed.
   - `_find_substr` — name shared/near-shared across 5 definitions
     (`_find_substr` exact in 2 files, `_find_substring`/`_find_substring_from`
     nearby) — underscore-prefixed.
   - `run_test_api_server_with_inject` — exactly 1 definition anywhere in the
     repo (globally unique) — **not** underscore-prefixed.
   - `extract_compiler_coverage_manifest_sdn` /
     `strip_compiler_coverage_manifest_blocks` — the defining function has since
     been deleted from `test_executor_parsing.spl` entirely (separate, unrelated
     dangling-reference issue found during this sweep, not investigated further
     here); at the time of the original fix it was not underscore-prefixed.

   **Verdict: REJECTED.** Global name ambiguity is sufficient-but-not-necessary
   (`run_test_api_server_with_inject` failed while being globally unique), so
   underscore-prefix / duplicate-definition is not a reliable standalone
   discriminator — it only explains 2 of 4 known instances.

2. **Structural shape: a free function is called from a file that does not
   itself define it, and the call is reachable in that file's scope ONLY
   through a wildcard facade import (`use x.y.facade.*` or
   `export use x.y.facade.*`), never through an explicit/direct import of the
   concrete defining module.** This matches all 4 known instances (the
   `_SimdOpportunityLint`/`arithmetic_checks.spl` case, the two `_text_index_len`
   wildcard imports, the `app.ui.standalone` package `__init__.spl` re-export
   case, and the `std.test_runner.test_executor_parsing` variant-resolution
   facade case) uniformly, independent of underscore-prefix or global-uniqueness.

   **Verdict: VALIDATED as the operative discriminator for the sibling
   split-part shape**, restricted further to: the caller and callee are BOTH
   split-part files living in the same leading-underscore directory
   (`_SomeName/`), i.e. genuine private-helper cross-calls within one former
   monolithic module, not general facade usage (most facade wildcard imports
   are fine because callers normally use their OWN split-part's definitions or
   go through explicitly-exported public API, not a sibling's private helper).

### Candidate search methodology

Enumerated all 36 `_CamelCase/` split-part directories under `src/compiler`,
`src/lib`, `src/app` (excluding vendor). For every top-level `fn NAME(` defined
in one sibling file of a directory, checked every OTHER sibling file in the same
directory for a textual call to `NAME(` that is not itself a re-definition. This
produced exactly 6 raw hits (5 distinct symbols; `svim_mode_name` was called from
two different sibling files). For each hit, confirmed the calling file's import
block reaches the split-part directory only via the parent facade module's
wildcard import (`use x.y.facade.*`), with no existing direct/explicit import of
the symbol.

### Ranked candidate list (all 5 applied — see below)

| Symbol | Calling file(s) | Defining module | Match |
|---|---|---|---|
| `svim_mode_name` | `src/app/svim/_SvimCore/session_commands.spl`, `src/app/svim/_SvimCore/text_ops.spl` | `app.svim._SvimCore.model` | facade wildcard `use app.svim.core.*`, both callers, globally unique fn |
| `decode_ppm_local` | `src/app/wm_compare/_HtmlCompat/capture_and_compare.spl` | `app.wm_compare._HtmlCompat.ppm_and_widget_pixels` | facade wildcard `use app.wm_compare.html_compat.*`, globally unique fn |
| `_link_native_mingw` | `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl` | `compiler.backend.linker._LinkerWrapper.shared_linking` | facade wildcard `use compiler.backend.linker.linker_wrapper.*`, underscore-prefixed, globally unique |
| `lint_accessor_and_parent_names` | `src/compiler/90.tools/lint/_LintMain/lint_checks.spl` | `compiler.tools.lint._LintMain.name_lints` | facade wildcard `use compiler.tools.lint.main.*`, globally unique fn |
| `sanitize_c_name` | `src/compiler/70.backend/backend/_CBackendTranslate/export_wrappers.spl` | `compiler.backend.backend._CBackendTranslate.class_core` | facade wildcard `use compiler.backend.backend.c_backend_translate.*`; 2 definitions repo-wide (2nd is `compiler.tools.header_gen.header_utils`, out of scope here so no clash, but matches the ambiguous-name pattern too) |

### Applied fixes

All 5 sites got the minimal direct-import workaround (explicit braced import of
the concrete defining sibling module, added alongside the existing facade
wildcard import; no other lines touched):

```
# src/app/svim/_SvimCore/session_commands.spl and text_ops.spl
use app.svim._SvimCore.model.{svim_mode_name}

# src/app/wm_compare/_HtmlCompat/capture_and_compare.spl
use app.wm_compare._HtmlCompat.ppm_and_widget_pixels.{decode_ppm_local}

# src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl
use compiler.backend.linker._LinkerWrapper.shared_linking.{_link_native_mingw}

# src/compiler/90.tools/lint/_LintMain/lint_checks.spl
use compiler.tools.lint._LintMain.name_lints.{lint_accessor_and_parent_names}

# src/compiler/70.backend/backend/_CBackendTranslate/export_wrappers.spl
use compiler.backend.backend._CBackendTranslate.class_core.{sanitize_c_name}
```

`bin/simple lint` on each of the 6 changed files self-crashes with
`semantic: array index out of bounds` while loading the whole compiler
pipeline — confirmed pre-existing by running the identical command on an
untouched sibling file in the same directory (`session_operators.spl`), which
crashes identically. Not a regression from this change.

### Note: shape (b), package `__init__.spl` re-exports, NOT swept

This pass focused on shape (a) (sibling split-part directories) because it is
mechanically enumerable (36 directories, bounded search). Shape (b) (package
`__init__.spl` re-exports, like the `run_test_api_server_with_inject` /
`app.ui.standalone` case) has no equivalently bounded search space — there are
many `__init__.spl`-style package facades in the repo and most link fine, so a
blanket rewrite would be unjustified churn. Not swept in this pass; left for a
future targeted investigation if it recurs at the link stage.
