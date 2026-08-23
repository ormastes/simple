# Cross-module struct field/constructor visibility blocks the 140-module lint closure at step 2/6

Filed 2026-08-23 from the monomorphization lane, as a **measured negative
result**: it is what actually stops a real closure, and it is NOT what the
phase36 forecast predicted would stop it.

## What was run

```
native-build --source src/app/lint --entry-closure \
  --entry src/app/lint/main.spl --threads 4
```

worktree `/mnt/fast/wt-mono-1`, deployed seed
`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`,
`SIMPLE_TIMEOUT_SECONDS=0`, `SIMPLE_CACHE_SCOPE=mono1_lint_fix`.
**Closure size: 140 modules.**

## Result

`hir 140/140` completes, then rc=1 at **step 2/6** with **1512 HIR lowering
errors across 44 files**. Monomorphization is never reached: no `[mono]`
receipt is emitted, and `E-MONO-030/032/033` counts are all **zero**.

| class | count |
|---|---|
| ``field `X` is not visible from this module`` | 1238 |
| ``aggregate constructor `X` is not visible`` | 174 |
| `unresolved type` | 80 |
| `unresolved name` | 20 |

Top fields: `trimmed` 190, `line_num` 182, `byte_offset` 150, `line` 144,
`indent` 124, `results` 98. Top constructors: `SimdOpportunityWarning` 70,
`ProcessResult` 12, `LintDiag` 10, `Token` 8. Top files:
`src/lib/nogc_sync_mut/tooling/easy_fix/rules_lint.spl` 156,
`.../easy_fix/rules.spl` 148, `src/compiler/tools/lint/_LintMain/lint_checks.spl`
108.

## Mechanism (one confirmed instance)

`src/lib/nogc_sync_mut/tooling/easy_fix/rules_helpers.spl:12` declares

```
struct LineContext:
    ...
    trimmed: text          # no explicit visibility marker
```

and `rules_lint.spl` — a DIFFERENT module — reads `.trimmed` off a
`LineContext`. HIR rejects that read as not visible. So a plain, unmarked
struct field is treated as module-private, and every cross-module field read
on a shared struct fails. The `aggregate constructor` class is the same rule
applied to construction rather than field read (`ProcessResult` is exactly the
symbol the phase36 forecast's rung 1 hit on the 7-file `src/app/memstat`
closure, so this is the same defect at 20x the scale).

Not yet established, and deliberately not asserted: whether the intended rule
is "unmarked fields are public" (and the checker is wrong), or "unmarked
fields are private" (and 44 files need markers). That is a design call and is
why this is filed rather than patched.

## Why this matters to the generics/mono lane

The phase36 forecast ranked `E-MONO-033` as the CERTAIN, dominant blocker
immediately after HIR, expecting it "in the hundreds". On this closure that is
wrong in the strongest possible way: mono raises **zero** diagnostics because
**control never reaches it**. Cross-module visibility is the real next wall
for the lint closure, and it is an HIR-layer defect with no generics content
at all (`generic structs are not supported` appears **0** times).

Consequence for the mono fix landed at `75f554903ff`: it is proven at fixture
scale (closure size 1) and by call-site enumeration, but it remains
**unvalidated at real closure scale**, because no real closure currently gets
far enough to exercise it. Any claim that stage1 "now survives
monomorphization" is unsupported until a closure clears this wall.

## Also worth noting: the silent-abort symptom is gone

The forecast recorded this same lint closure exiting **rc=255 with ZERO
diagnostic output** and no receipt — its item 1, "undiagnosable as shipped".
It now exits rc=1 with 1512 clearly attributed diagnostics naming file, symbol
and reason. Whatever changed between those trees fixed the reporting defect;
the underlying failure was simply invisible before.

## Caveat on this run

The mono source was edited mid-run in this lane (a `Field`-arm experiment was
reverted while shards were live), so shards may have seen inconsistent
compiler source. The conclusion is unaffected: every one of the 1512 errors is
an HIR visibility/resolution error in files this lane never touched, and the
build died before monomorphization ran at all.

---

## RESOLVED 2026-08-23 — the checker was right, its INPUT was fabricated

The open design question ("are unmarked fields public, or do 44 files need
markers?") is answered: **an unmarked struct/class field is PUBLIC, gated by
the composite's own visibility.** Adding markers to 44 files was not merely the
wrong answer — it was not even expressible.

### Evidence

1. **Per-field visibility is structurally unrepresentable on the main parse
   path.** The flat AST decl node exposes `decl_get_fields`,
   `decl_get_field_types`, `decl_get_field_defaults`, `decl_get_field_bits`
   (`10.frontend/core/_Ast/decl_nodes.spl`) — and **no visibilities array**.
   `parse_struct_decl` (`_ParserDecls/fn_struct_decls.spl:896-909`) collects
   `field_names / field_types / field_defaults / field_bits /
   layer_field_renames` and no visibility list. So `pub trimmed: text` inside a
   struct body cannot be carried, and a Private default can **never** be
   overridden from source. A rule with no source-level remedy is not a rule.
2. **The bridge fabricated the value.**
   `_FlatAstBridge/module_assembly.spl:360` hardcoded `visibility:
   Visibility.Private, is_public: false` for every struct/class field. It was
   never read from the declaration.
3. **The same function already says Public for enum variant payload fields**
   (`module_assembly.spl:502`).
4. **The declaring module's own HIR tables grant every field
   unconditionally** — `prescan_composite_field_types` and
   `register_struct_field_types` (`_Items/module_callable_types.spl:45,67`) set
   `field_access[name] = true` and `constructor_access = true` outright.
5. **The interface digest treats an undeclared visibility as public** —
   `35.semantics/interface/compile_interface.spl:62`,
   `canon_str(sig.declared_visibility ?? "public")`.
6. **The language has an explicit private marker.** `treesitter_parse_visibility`
   (`treesitter/outline_decls.spl:79`) accepts `KwPri`. A `pri` keyword is
   pointless if unmarked already means private.
7. **Twin check (standing rule): the seed does not implement this at all.**
   `grep "not visible from this module" src/compiler_rust/` returns **0**. The
   whole diagnostic exists only in the pure-Simple HIR — a textbook
   seed-lenient / stage1-strict split. No spec anywhere asserts a field
   denial (`grep -rln` over `test/` returns 0 files).

The policy engine itself (`00.common/dependency/member_visibility.spl`) is
correct and is **unchanged** — `member_visibility_allows`,
`aggregate_constructor_visibility_allows` and every scoped kind
(Package/Internal/Up/Peer/Private) keep their exact semantics. Only the
fabricated default feeding them was wrong. Sealing via `pub(...)` on the
composite still works; nothing was weakened that source could actually express.

### Fix

- `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` — struct/class
  fields are built `Visibility.Public / is_public: true`, with the reasoning
  above recorded inline.
- `src/compiler/10.frontend/treesitter/outline_members.spl` — same-class sweep:
  enum struct-variant payload fields were hardcoded `Private` on the outline
  path while the flat-AST bridge builds them `Public`, so the two paths
  disagreed about one declaration. Now `Public` on both.

Reproduce spec: `test/01_unit/compiler/frontend/struct_field_default_visibility_spec.spl`
— **3 failed pre-fix, 3 passed post-fix**, verified by reverting the bridge
edit alone. Its third case asks the real policy owner the exact HIR question:
whether `rules_lint.spl` may name `LineContext.trimmed` declared in
`rules_helpers.spl`.

### Follow-up, recorded not guessed

Per-field visibility remains **unimplementable** on the main path: to honour a
per-field `pri`/`pub(...)` marker the flat AST needs a visibilities array
parallel to `decl_get_field_types`, plus parser and bridge support. Until then
the composite's own visibility is the only field-sealing mechanism, and
`member_visibility_allows` will only ever see `Public` for a field on this
path. The treesitter outline path *does* parse a per-field marker
(`outline_decls.spl:447`) but defaults an unmarked field to `Private`, which
now disagrees with the semantic answer above; it feeds outlines/LSP, not the
HIR surface, so it was left alone rather than changed speculatively.

### Real-scale re-measurement: COMPLETED, the visibility class is eliminated

The post-fix 140-module `src/app/lint --entry-closure` rerun finished
(`--threads 4`, matching the original probe's command exactly; closure size
reconfirmed at **140**).

| class | pre-fix | post-fix |
|---|---|---|
| ``field `X` is not visible from this module`` | 1238 | **0** |
| ``aggregate constructor `X` is not visible`` | 174 | **0** |
| `unresolved type` | 80 | 377 |
| `unresolved name` | 20 | 12 |

**The entire 1412-error visibility class is gone.** That zero is not a
truncation artifact: the three files that carried the most errors
(`rules_lint.spl` 156, `rules.spl` 148, `lint_checks.spl` 108) now report
**0** visibility errors each, and the specific fields that accounted for 522
of the 1238 (`trimmed` 190, `line_num` 182, `byte_offset` 150) appear **0**
times anywhere in the log.

### The wall moved, it did not disappear

The closure now advances deep into HIR — `hir 136/140` at step 2/6, versus
dying at the very start of step 2/6 before — and hits a **different, later**
blocker. Recorded honestly:

- `unresolved type` rose 80 -> **377**. This is expected direction, not a
  regression introduced here: 44 files previously bailed out early on
  visibility errors, so far more of their code is now reachable and lowering
  reports what was always behind that wall. Top names: `String` 84, `Option`
  63, `int` 62, `Int` 53, `Dict` 51, `Bool` 30, `Result` 16, `fn` 16 — a
  type-name/alias resolution gap (note the foreign-looking `String`/`Int`/
  `Bool` spellings), with no visibility content.
- 47 modules end `hir-poisoned`.
- The run ends **rc=255** with `native-build worker wrapper exited abnormally
  (signal or wait failure, code -1) before producing a binary`, and stderr is
  explicitly **truncated** (`!!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!`).
  So 377 / 12 are **lower bounds**, and the silent-abort symptom this record
  earlier noted as "gone" has reappeared at a later point in the pipeline.
- **Monomorphization is still never reached**: 0 `[mono]` receipts, 0
  `E-MONO-030/032/033`. The mono fix at `75f554903ff` therefore remains
  **unvalidated at real closure scale**, exactly as this record originally
  said. Cross-module visibility was one wall; it was not the last one.
