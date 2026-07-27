# `me` (receiver) reported as an unresolved NAME in class methods during stage-4 lowering

**Status:** open
**Found:** 2026-07-27 (RISC-V hardening campaign, Lane H — stage-4 full-CLI bootstrap)
**Area:** HIR lowering (`src/compiler/20.hir/`), bootstrap/stage-4 path
**Severity:** high — 543 errors; one of the two remaining stage-4 full-CLI blockers

## Finding

During the stage-4 full-CLI native build, HIR lowering emits

```
error: focused native-build: HIR lowering error in app.office.word.word_app: unresolved name: me
```

**543 times**, i.e. `me` — the method-receiver keyword — is being resolved as an
ordinary identifier and failing.

The source is ordinary, idiomatic Simple. `src/app/office/word/word_app.spl`:

```simple
class WordApp:
    ...
    me build_ui() -> UITree:
        """Build the full iOS-styled document editor UI tree."""
        val toolbar = me.build_toolbar()
        val sidebar = with_flex(me.build_sidebar(), 1)
        if me.sidebar_visible:
            ...
```

Both member access (`me.sidebar_visible`) and method calls (`me.build_toolbar()`)
are affected.

## Distribution

All occurrences are in `src/app/office/*` applications; no compiler module
reports it, although compiler classes use `me` methods extensively.

| module | count |
|---|---|
| `app.office.sheets.sheets_app` | 80 |
| `app.office.word.word_app` | 55 |
| `app.office.planner.planner_app` | 44 |
| `app.office.mail.mail_app` | 43 |
| (others) | remainder of 543 |

That asymmetry is the main clue: whatever binds `me` works for the compiler's
own classes but not for these. Worth checking what differs — declaration form
(`class X:` with `me` methods vs `impl X:` blocks), nesting, or the order in
which these modules are lowered relative to their class declarations.

## Pre-existing, and independent of import resolution

The count is **byte-identical (543)** across:

- 2026-07-27 morning run — tree at `4eb553c720e`, compiler built with the
  (later reverted) partial-module guard rounds;
- 2026-07-27 afternoon run — tree 159 commits newer, compiler built with the
  `contains_key` + index-read fix (`9b612a11418c`).

Two different trees, two different compiler builds, identical count. It is
therefore unaffected by the `Dict.get()`/`Dict.len()` defects
(`native_dict_get_struct_value_corrupt_option_2026-07-27.md`,
`native_dict_len_returns_minus_one_2026-07-27.md`) and by the glob-import fixes
(`67024e9c0a51`), which moved the overall unresolved count 11,826 → 5,950 →
4,008 → 2,224 while leaving `me` at 543.

## Repro

```bash
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
# stage-4 log: build/bootstrap/logs/<triple>/stage4-native-build.log
grep -c 'unresolved name: me' <stage4 log>
```

Faster: run the stage-4 native-build command directly with a stage3 binary
(see `bootstrap_native_build_main` in `scripts/bootstrap/bootstrap-from-scratch.sh`),
adding `SIMPLE_BOOTSTRAP_DIAG=1`.

## Suggested next step

Instrument the receiver binding in class/method lowering and compare a failing
`app/office/*` class against a working compiler class in the same run — the goal
is to find why the receiver symbol is defined for one and not the other, rather
than to special-case `me` at the use site.

## Related

- `stage4_focused_subbuild_star_import_unresolved_2026-07-27.md` — the other
  remaining stage-4 blocker (module-key canonicalization for the lexer family)
- `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` (Lane H)
