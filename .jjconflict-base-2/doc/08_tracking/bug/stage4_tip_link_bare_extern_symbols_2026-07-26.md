# Stage4 one-binary build broken at tip: cross-module calls emitted as bare extern symbols

- **Date:** 2026-07-26 (evening)
- **Lane:** stage4 one-binary rebuild (seed → libspl_objects.a → clang link, aarch64-apple-darwin)
- **Status:** original blockers fixed; Stage 2/3 proven, one full Stage-4 rerun remains

## Symptom
Link fails with undefined symbols that are BARE (unmangled) references, while the
linker itself suggests the correctly-mangled definitions:

```
"__text_index_len", referenced from:
    _tools__fix__rules__impl___lint_short_grammar__check_short_grammar_refactor
   (maybe you meant: _tools__fix__rules__helpers___text_index_len,
                     _nogc_sync_mut__tooling__easy_fix__rules_helpers___text_index_len)
"_simple_contract_check", referenced from:
    _frontend___FlatAstBridge__convert_nodes__op_kind_to_binop
"_resolved_theme_fingerprint", referenced from:      # tip only (457a435787 era)
    _ui_dot_web__html_css__generate_css
```

Also at tip AND at 29f40fc2: `simple_asm_blocks.c:13:10: error: unexpected token
in argument list` — a Rust-style asm constraint (`"in(reg) id\n"`) emitted into
the generated C asm-blocks file.

## Reproduction ladder (same recipe, only base sha varies)
- tip `3da818508d29`: 3 bare-symbol failures + asm error.
- `29f40fc2` (morning): 2 failures (`_text_index_len`, `simple_contract_check`) + asm error.
- `3a6982e89c` (last-known-good deploy vintage): rebuild in progress — determines
  whether this is a source regression window (3a6982e → 29f40fc2) or seed staleness.

## Defect class
Definitions exist in Simple source (`simple_contract_check` in
`src/lib/common/contracts/contracts.spl`; `_text_index_len` in
`90.tools/fix/rules/helpers.spl` and `easy_fix/rules_helpers.spl`) but call
sites compile to bare extern references — the mangler failed to resolve the
cross-module call and fell back to extern emission. Same family as the
documented mangle.rs single-candidate erased-receiver rebind and the
"seed stale = old extern registry" failure mode (seed backfill rebuild:
`-p simple-compiler-backfill`, no-LTO runtime last).

## Sharpened diagnosis (2026-07-26 late) — THREE independent defects, NOT a seed regression
Attempt with YESTERDAY's seed (`bin/release/aarch64-apple-darwin-macho/simple_seed`,
Jul 25 13:12) fails IDENTICALLY to today's rebuilt seed, at every source sha from
`3a6982e89c` through tip. So this is not the 2026-07-26 seed rebuild; it is a set of
pre-existing, repo-wide stage4-build breakages:

1. **`simple_contract_check` / `simple_contract_check_msg` missing from the
   `core-c-bootstrap` bundle.** These are runtime `extern "C"` symbols defined in
   `src/compiler_rust/runtime/src/value/sffi/contracts.rs` — present in the full
   runtime, absent from the core-C ABI bundle. Frontend code
   (`_frontend___FlatAstBridge__convert_nodes__op_kind_to_binop`) now emits contract
   checks, so the core-C link can't resolve them. Fix path (the build note itself says
   so): add these symbols to `simple-core/core-c-bootstrap`, OR stop emitting contract
   checks in code compiled under that bundle.
2. **`_text_index_len` bare/global extern** while two mangled definitions exist
   (`90.tools/fix/rules/helpers.spl`, `easy_fix/rules_helpers.spl`) — the
   ambiguous-multi-candidate mangler fallback emits a bare extern instead of the
   module-scoped symbol. mangle.rs family.
3. **`simple_asm_blocks.c` `in(reg)` unexpected token** — Simple `asm` blocks are
   lowered into generated C carrying Rust inline-asm operand syntax (`in(reg)`).
   Codegen lowering bug, separate from the two link failures.

## Source Fixes and Focused Evidence

1. `runtime_native.c` now provides `simple_contract_check` and
   `simple_contract_check_msg`; the core-C capsule producer requires and attests
   both global text symbols. A capsule-equivalent compile plus `nm -g` found
   both providers as `T`.
2. Native-project mangling now resolves an ambiguous private call only when one
   candidate has the unique longest module-prefix match. The focused nearest
   candidate and equal-distance refusal tests pass (2/2).
3. Generated inline-asm C now filters Simple operand/clobber/options directives
   while retaining real instruction text. Its focused generated-C compile test
   passes (1/1).

The release wrapper also executes a bounded test-command ABI probe after
`--version`. The obsolete deployed binary is now rejected cleanly instead of
crashing in `rt_env_set`; the wrapper integration test passes.

These are source-level and focused-test results. A current Stage-4 binary,
full SSpec/docgen, Bootgen output, and board evidence are not implied.

## Linux Rebuild Evidence, 2026-07-27

The guarded one-worker Linux rebuild passed Stage 2/3 native builds, both
compiler sanity gates, source/tool/git provenance, and Stage-2 capability.
Admitted hashes were:

- Stage 2: `492d62e38946efb6f1af11bd4be97c47b34153f1384c8b1944a3a97e8df94875`
- Stage 3: `257e522ceecbc3bac8366066748e544a71007e029f591c3d81c653cab688dec8`

The prior 64 GiB growth did not recur: observed Stage-2 RSS was about 388 MiB
and Stage-3 RSS about 211 MiB. Stage 4 then stopped in phase 1 on an unrelated
stale import in browser custom properties. `8c7eb97d3592` restores the
animation module as the exact `CSSValue`/`CSSDeclaration` owner. A fresh
Stage-3 native probe compiled six modules and exited zero. The repository
three-cycle guard prohibits another full rerun in this session, so deployment
and firmware SSpec/docgen remain pending rather than inferred.

## Impact

The previous blockers prevented any recent Stage-4 candidate from linking.
They are fixed in source; the currently deployed binary still predates the
environment ABI and must not be used as production evidence.
