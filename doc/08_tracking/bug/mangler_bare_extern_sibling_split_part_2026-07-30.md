# Bug: Rust seed mangler emits bare extern for free function shared across sibling split-part modules re-exported through a facade

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
