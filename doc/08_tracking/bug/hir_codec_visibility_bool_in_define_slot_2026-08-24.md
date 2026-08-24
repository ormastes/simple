# `hir codec: no \`Visibility\` arm for tag -1` — 25 `define()` call sites pass a bool where a `Visibility` is required

- **Date:** 2026-08-24
- **Status:** FIXED (source fix + fail-closed guard); one unrelated defect unmasked, see below
- **Severity:** critical-path blocker — Stage-2 `compile` could not run, so Stage 3/4, deploy and release were unreachable

## Symptom

A three-line hello world (`fn main() -> i64: print("hi"); return 0`) compiled with the
Stage-2 bootstrap CLI:

```
$ stage2 compile h.spl --format=smf
[bootstrap-error-count] source_idx=0 point=post-lowering count=0
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0
error: hir codec: no `Visibility` arm for tag -1; regenerate src/compiler/20.hir/generated/hir_codec.spl
rc=1
```

`native-build` on the same binary and the same source was rc=0 and ran. Lowering was
clean — zero errors at both counters.

## Root cause

`SymbolTable.define()` (`src/compiler/20.hir/hir_types.spl:316`) takes

```
me define(name: text, kind: SymbolKind, type_: HirType?, span: Span,
          visibility: Visibility, is_mutable: bool, defining_module: text?) -> SymbolId
```

Slot 5 used to be `is_public: bool`. **25 call sites were never migrated** and still passed
the literal `false` there, e.g.

```
self.symbols.define(name, SymbolKind.Variable, hir_type, s.span, false, false, nil)
```

so `HirSymbol.visibility` held a boolean. A bool is not nil, so every nil-guard in the
generated HIR codec (`if node.visibility == nil: … else: hc_enc_visibility(…)`) took the
encode branch, and the value then matched none of the six `Visibility` variants. The
`case _:` fallthrough in `hc_enc_visibility`
(`src/compiler/20.hir/generated/hir_codec.spl:6823`) fired and `hc_bad_tag` called
`exit(1)`. The `-1` is a hardcoded sentinel in that fallthrough, not a decoded tag.

The abort happened inside `hir_cache_store` (`driver_hir_pipeline_lowering.spl:840` ->
`driver_hir_cache.spl:187` -> `hir_module_encode`), which is why it landed immediately
after the post-diagnostics counter and why `native-build` never hit it.

Confirming experiment before any edit: with the cache kill switch
`SIMPLE_HIR_CACHE=0`, the `Visibility` error disappeared entirely and the build ran on to
the backend — proving the malformed value reached only the codec's encode path and that
the codec was the messenger, not the producer.

## Fix

All 25 sites now pass `Visibility.Private`, which is exactly what the old
`is_public: false` meant (`define` derives `is_public: visibility == Visibility.Public`,
so the recorded flag is unchanged). Six files gained
`use compiler.common.dependency.visibility.{Visibility}`.

The encoder was deliberately **not** touched. Mapping an unknown value to `Public`, or
emitting a default, would turn a loud, correct failure into silent corruption of a
serialized artifact. The fallthrough is behaving correctly.

Files: `src/compiler/20.hir/hir_lowering/statements.spl` (12),
`_Expressions/match_desugaring.spl` (5), `_Expressions/expression_core.spl` (2),
`_Expressions/expression_components.spl` (2), `_Expressions/expression_support.spl`,
`_Expressions/union_narrow_arms.spl`, `_Items/module_build.spl`, `types.spl`.

## Guard (reproduce spec — fails before, passes after)

`scripts/check/check-symbol-define-visibility-arg.shs` parses every `.define(` call
in `src/**/*.spl` (joining multi-line calls) and fails on any 7-argument call whose 5th
argument is the literal `true` or `false`. Hard zero-bar, not a ratchet. `--selftest`
runs first and is fatal (4 fixtures: clean must pass; the incident shape must be flagged;
the unrelated 2-argument `Env.define` must not be flagged; an empty tree must report 0
checked so the caller is forced to ERROR). A run that examined 0 call sites is ERROR,
never a pass.

- BEFORE (pre-fix tree via `git archive HEAD`):
  `FAIL — 55 call site(s) checked, 25 with a bool in the visibility slot: …` rc=1
- AFTER (whole `src/`):
  `PASS — 137 call site(s) checked, 0 with a bool in the visibility slot` rc=0

## Unmasked, not caused

With the codec abort gone, `compile --format=smf` proceeds into the SMF backend, where
the pre-existing `cranelift-direct` SEGV is now reachable. That crash was measured on the
**unmodified** Stage-2 binary with `SIMPLE_HIR_CACHE=0` before this fix existed
(`rc=139`, last lines `[cranelift-direct] start / target / module`), so it is a separate
defect this change exposes rather than introduces.

## Causal proof (harness, not inference)

A 25-line entry built with the Stage-2 bootstrap CLI
(`/mnt/data/worktrees/goal-main-1/build/bootstrap/goal-r3/stage2/x86_64-unknown-linux-gnu/simple`,
132,945,096 bytes, built 2026-08-24 02:50 — executed from a copy, never edited in place)
constructs two `HirSymbol`s that differ in exactly one field and hands both to the same
`hc_enc_hir_symbol`. Verbatim, one run of one binary:

```
GOOD visibility=Visibility.Private -> encoded, bytes=39
BAD  visibility=false -> encoding now (expect the codec abort)
error: hir codec: no `Visibility` arm for tag -1; regenerate src/compiler/20.hir/generated/hir_codec.spl
HARNESS_RUN_RC=1
```

A bool in that field reproduces the production error byte-for-byte; a `Visibility` encodes.
The harness is scratch evidence, not a tracked artifact: it needed
`SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1 SIMPLE_ALLOW_INTERNAL_STUBS=1` because its import closure
drags in 9 mmap/file runtime entries and `bytes_to_u16_le`/`bytes_to_u32_le` that the C
bootstrap runtime does not define. None of those are on the code path it exercises.

## Stage-3 build from the fixed tree

`stage2 native-build ... src/app/cli/bootstrap_main.spl` over the fixed tree reached all 692
surfaces and ran the whole HIR phase, then failed (rc=1) with **68 `hir-fatal`s, zero of them
a codec/Visibility error** (`grep -c 'hir codec' = 0`). Every fatal is the documented
Stage-3 class other lanes own: `unresolved name`/`unresolved type`, `ambiguous explicit
callable dependency DiContainer/AopWeaver`, and `field 'kind' is not visible from this module`.
The 7 that name files this change touched are all `unresolved name`/`unresolved type`
(`bootstrap_hir_functions_add`, `hir_expr_env_get`, `ModuleSurfaceEnum`, …) — none mentions
`Visibility` or an ambiguous import, so this change introduced no new lowering error. No
Stage-3 binary was produced, so `compile --format=smf` could not be re-run on a compiler
built from this fix; the harness above is the direct evidence in its place.
