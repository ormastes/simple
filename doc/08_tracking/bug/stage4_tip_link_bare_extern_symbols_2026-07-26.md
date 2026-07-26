# Stage4 one-binary build broken at tip: cross-module calls emitted as bare extern symbols

- **Date:** 2026-07-26 (evening)
- **Lane:** stage4 one-binary rebuild (seed → libspl_objects.a → clang link, aarch64-apple-darwin)
- **Status:** open — blocks any stage4 rebuild from current main

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

## Impact
No stage4 candidate can be built from tip → runtime perf fix (`3da818508d29`)
and any future compiler fix cannot deploy until this is resolved.
