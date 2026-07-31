# `struct` source through `parse_full_frontend` under `bin/simple test` — "function `Field` not found"

**Lane:** FIELD1 (mission-critical hardening campaign, 2026-07-30/31)
**Status:** NOT REPRODUCIBLE in current tree — already fixed upstream by commit `3eb2635ea5c`, landed *before* the workaround commit that still describes it as open. VSL1's workaround (`4c1175bac2e`) and its docstring are now stale documentation for a bug that no longer exists at that call site.

## Reported symptom (background, established by lane VSL1)

Any `struct ...:` source run through `parse_full_frontend` from inside a
`bin/simple test`-interpreted spec was reported to fail with:

```
semantic: function `Field` not found
```

reproduced with a trivial one-field struct (`struct Probe:\n    x: i64\n`);
function-only source worked fine. VSL1 attributed this to
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:308`, which
constructed the frontend AST field type via a **named-argument call**
`Field(name: ..., type_: ..., ...)` — a bare, unqualified constructor call to
a struct named `Field`. VSL1's hypothesis: under the nested interpreter that
runs a compiler pipeline inside an interpreted test, this call resolved
through a bare-name/function-lookup path rather than a type-constructor path,
and since no plain *function* named `Field` exists (only a type, plus several
unrelated `Field` enum variants elsewhere — `ExprKind.Field`,
`HirExprKind.Field`, `macro_registry.IntroducedSymbol.Field`), resolution
missed and raised "function `Field` not found". VSL1 worked around it by
hand-building `HirModule`/`HirStruct`/`HirField` directly in
`test/01_unit/compiler/semantics/value_struct_layout_spec.spl` instead of
parsing real struct source, and the same workaround pattern is already used
by `transfer_share_semantic_spec.spl` and `iso_move_pipeline_spec.spl` (for
their own, unrelated frontend gaps — `iso`/`spawn` source, not this bug).

## What this lane found: NOT reproducible today

### Repro attempt 1 — parse only

```
use compiler.frontend.frontend.{parse_full_frontend}
val src = "struct Probe:\n    x: i64\n"
val module = parse_full_frontend(src, "src/field1_probe.spl", "field1_probe", make_logger())
expect(module.structs.len()).to_equal(1)
```

Run: `env -u SIMPLE_TIMEOUT_SECONDS timeout 300 bin/simple test --no-session-daemon <spec>`
Result: **PASS** — `1 example, 0 failures`, `Results: 1 total, 1 passed, 0 failed`.

### Repro attempt 2 — parse + full HIR lowering (matches VSL1's actual attempted pattern: `parse_full_frontend` + `HirLowering.lower_module`)

```
val module = parse_full_frontend(src, path, "field1_probe2", log)
var lowering = HirLowering.with_filename(path)
val hir = lowering.lower_module(module)
expect(hir.structs.len()).to_equal(1)
```

Result: **PASS** — same trivial struct, full frontend-to-HIR pipeline, no error of any kind.

Neither attempt produced `semantic: function \`Field\` not found` or any
other error. The literal repro string VSL1's docstring describes
(`struct Probe:\n    x: i64\n`) parses and lowers cleanly today.

## Corrected root cause and why it's already gone

`git show 3eb2635ea5c -- src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`
shows the exact call site VSL1 named, at what was then line 308:

```diff
-                fields.push(Field(
+                fields.push(ParserField(
                     name: f_names[fi],
                     type_: ft,
                     ...
```

i.e. **`module_assembly.spl`'s named-argument struct-field constructor call
was literally renamed from bare `Field(...)` to `ParserField(...)`** by
commit `3eb2635ea5c` ("refactor(frontend): ParserField/ParserTypeAlias —
parser_types rename 11/11 complete (PTR2)"), timestamped
`2026-07-30T08:31:17Z`. That is exactly the call VSL1's docstring blames,
and exactly the kind of bare-name collision this campaign has repeatedly
found (`Field` collides with `ExprKind.Field` / `HirExprKind.Field` /
`macro_registry.IntroducedSymbol.Field` in whatever global/bare-constructor
registry the nested interpreter uses to resolve named-arg struct
construction). The commit message independently confirms the mechanism:
"Probe: case SymbolKind.Field/TypeAlias now match with real discriminants
(100/101) — the bare-name discriminant-collision family is fully closed at
the source."

VSL1's workaround commit `4c1175bac2e` ("test(semantics): cover the by-value
struct layout check") is timestamped `2026-07-30T23:43:15Z` — **over 15
hours after** the rename fix landed at that same call site. So the fix was
already at `origin/main` when VSL1 committed its workaround; VSL1 most
likely reproduced the (real, and by then already-fixed-upstream) bug against
a working copy that had not picked up `3eb2635ea5c` yet — this environment's
shared-WC has a documented history of silently drifting below origin (see
the FIELD1 task brief's own environment warning) — wrote the diagnosis and
workaround against that stale state, and it was never re-verified against
current origin before landing.

**The orchestrator's earlier statement that VSL1's attribution was "wrong"
is itself imprecise**: the attribution (call site, file, line, mechanism)
was correct — the *code at that site* is simply no longer present, because
the very rename that the orchestrator used to check "is line 308 still bare
`Field(`?" (and found `ParserField(`) *is the fix*. The right correction is:
"attribution was right, target already patched, docstring is stale" — not
"attribution was wrong."

### Registry family verdict

This is a straightforward member of the campaign's known
**bare-name-through-a-global-registry** defect family (same shape as the
`SymbolKind.Field`/`TypeAlias` discriminant collisions this same PTR2 rename
closed), not a new/different mechanism. Confirmed by grep of remaining bare
`Field(...)` call sites under `src/compiler/10.frontend/`: none left that
construct the frontend `ParserField`/`Field` AST-field type by bare name;
the only surviving `Field(` sites are legitimate: `ExprKind.Field(...)`,
`HirExprKind`/`exprkind_Field` matches, and
`macro_registry.IntroducedSymbol.Field(...)` (all correctly qualified or
distinct declarations, not the collision site).

## Verification honesty

Both repro specs were run via `bin/simple test --no-session-daemon` against
the **unmodified, on-disk `.spl` compiler sources**, which `git fetch origin
main && git diff --stat origin/main -- <files>` confirmed matched
`origin/main` exactly for `module_assembly.spl` and
`value_struct_layout_spec.spl` (no local drift on these two files, despite
this session's broader working copy showing large unrelated drift on
~550 other paths — see the environment warning). `bin/simple` here is
`bin/release/x86_64-unknown-linux-gnu/simple`, a **Rust-built bootstrap seed**
(its own banner: "this Rust-built Simple binary is a bootstrap seed only").
Since **no source was edited by this lane**, the seed-vs-self-hosted
distinction does not undermine this finding: the seed's interpreter executed
the current, origin-matching `.spl` compiler source (including
`module_assembly.spl`'s `ParserField(...)` construction) exactly as
`bin/simple test` would in the reported scenario, and it passed cleanly.
No rebuild was necessary or attempted because nothing was changed.

## Fix status

**No fix applied by this lane** — none was needed; the underlying defect at
`module_assembly.spl`'s struct-field constructor call was already fixed by
`3eb2635ea5c` before this lane started. Nothing in `src/compiler/**` was
touched.

## Follow-up for the next lane (not done here — scope discipline)

- `test/01_unit/compiler/semantics/value_struct_layout_spec.spl`'s docstring
  (the "Why this spec hand-builds HIR instead of parsing struct source text"
  section, and its file:line attribution to `module_assembly.spl:308`) is now
  **factually stale**: it claims the bug is open and blocks the "real
  source through frontend" style. Re-verify with the same two repros above
  before touching it. If confirmed still-passing, the spec's hand-built-HIR
  section could in principle be replaced with (or supplemented by) a real
  `parse_full_frontend` + `HirLowering.lower_module` pass over actual
  `struct ...:` source — but that is a spec-content change with its own
  review surface (behavioral coverage must not regress) and is out of this
  lane's touched-files scope, so it is left as a recommendation, not applied.
- The doc this bug references,
  `doc/08_tracking/bug/newly_live_symbolkind_arms_audit_2026-07-30.md`
  ("VSL1 follow-up" section), should likewise be checked for the same stale
  claim and updated by whichever lane owns that document.

## Repro spec files (sandbox only, not committed)

- `/tmp/claude-1000/-home-ormastes-dev-pub-simple/79b2040e-4c78-4cc4-bdcb-deac69deb1a8/scratchpad/field1_repro_spec.spl` — parse-only repro
- `/tmp/claude-1000/-home-ormastes-dev-pub-simple/79b2040e-4c78-4cc4-bdcb-deac69deb1a8/scratchpad/field1_repro_spec2.spl` — parse + HIR-lowering repro
