# Enum bare-name collisions: enumeration, mechanism correction, and resolution options

**Date:** 2026-08-01
**Status:** ENUMERATION LANDED — no fix applied. Needs an owner decision on the
resolution strategy before any code change or rename sweep.
**Severity:** CRITICAL — silent wrong arm selection across a module boundary,
no diagnostic, exit code 0. Blocks promoting the match-fallthrough diagnostic
to fatal and blocks triage of 421 non-exhaustive match sites.
**Measured against:** clean export of `main@origin` `5ca84bcefe5` (tree 109,603),
`src/` only, `/usr/bin/grep` (NOT the default ugrep).
**Data:** `enum_bare_name_collision_enumeration_2026-08-01.tsv` (332 rows)

Cross-links:
- `match_enum_fallthrough_silent_2026-08-01.md` — the silent-fallthrough symptom
- `web_layout_incremental_visits_no_island_2026-08-01.md` — the found instance,
  three layers downstream of the actual cause
- `enum_payload_subpattern_always_matches_2026-08-01.md` — same MIR file, distinct defect

---

## 1. CORRECTION: the mechanism was misattributed

The prevailing account blamed `named_type_register`
(`src/compiler/10.frontend/core/types.spl:559`) — a flat, non-module-qualified
global — for enum match arms silently matching nothing across a module boundary.

**That attribution is REFUTED for enum variant dispatch** (PROVED, by direct
read of the code at the tip):

`named_type_register` is find-or-insert and only overwrites the field set when
the caller supplies a non-empty one:

```
fn named_type_register(name: text, field_names: [text], field_types: [i64]) -> i64:
    val existing = named_type_find(name)
    if existing >= 0:
        if field_names.len() > 0 or field_types.len() > 0:
            named_type_update(existing, field_names, field_types)
        return existing
```

Enums are registered as `named_type_register(enum_name, [], [])`
(`10.frontend/core/_ParserDecls/enum_module_body.spl:85`) — **both lists empty**,
so the update is skipped. That call is a pure name reservation so `-> MyEnum`
resolves as a type. Enum variants are never stored in this registry;
`c_codegen.spl:58-66` populates `named_type_*` for `DECL_STRUCT` only, never
`DECL_ENUM`. Variants go into the AST node via `decl_enum_def(...)`
(`enum_module_body.spl:202`).

The named-type registry collision is **real and is its own bug** (section 5),
but it is not what breaks enum match arms.

## 2. The actual mechanism (PROVED)

Enum match-arm dispatch is governed by two plain `{text: [...]}` maps on
`MirLowering`, keyed by the **bare** enum name:

- **Write** — `50.mir/_MirLowering/module_lowering.spl:241,244`:
  ```
  variant_index[enum_def.name] = names
  variant_discriminants[enum_def.name] = discriminants
  ```
  Unconditional assignment, no existence check. **Last registered enum wins.**
  Contrast the guarded Result/Option seeding at `:783,:794` in the same file,
  which does check.

- **Read** — `50.mir/_MirLoweringExpr/switch_operators_calls.spl:67-79`,
  `enum_variant_discriminant(enum_name, variant)`, called from
  `lower_enum_match` at `:1660`. When the arm's variant is absent from the
  *winning* declaration's list it returns **-1** — silently. No arm matches; the
  statement form is a no-op and the expression form yields the nil sentinel.

So two same-named enums in different modules share one entry. Arms naming a
variant that exists only in the losing declaration compile to a comparison that
can never be true, with no diagnostic at any stage.

### 2a. NEW: the two engines have OPPOSITE collision policies

The tree-walking interpreter keeps its own bare-keyed table,
`enum_table_register` (`10.frontend/core/interpreter/eval_tables.spl:603-612`),
which returns early on an existing name — **first wins**.

MIR (JIT/native) is **last wins**. Same collision, opposite winner. This is a
concrete engine-divergence trap: a spec that passes on the interpreter can be
wrong on the compiled lanes and vice versa, and which declaration is correct
flips with parse order. It also explains why five toy repros failed — a toy
cannot contain the losing declaration.

### 2b. The fix is far cheaper than expected: a qualified identity already exists

`HirEnum` already carries a module-qualified name built one layer up, at
`20.hir/hir_lowering/_Items/declaration_lowering.spl:720`:

```
runtime_name: if owner_module != "": "{owner_module}.{name}" else: name
```

The match path uses `.name` and never `.runtime_name`. There is also precedent
for namespace-aware handling in the *same file* as the bug:
`enum_runtime_id_index` (`module_lowering.spl:191-203`) hashes from the
qualified `runtime_name` and raises an explicit collision error.

This means the class can plausibly be fixed by re-keying two maps, not by
renaming 332 enums or re-architecting the frontend registry.

## 3. Enumeration (PROVED)

`src/` only, at `5ca84bcefe5`, `/usr/bin/grep`:

| Measure | Count |
|---|---|
| enum declarations | 2,159 |
| unique enum names | 1,502 |
| **enum names declared more than once** | **332** |
| enum names ALSO declared as a struct/class | 113 |
| enum names at risk (union of the two) | 404 |

This reproduces the previously reported "336 of 1,410" to within the scope
boundary (that census appears to have used a slightly narrower file set).

The shared named-type keyspace is much larger than the enum figure suggests —
enums, structs, classes and bitfields all share one flat key namespace:

| Measure | Count |
|---|---|
| enum + struct + class + bitfield declarations | 17,666 |
| unique names | 13,551 |
| **collided names** | **2,299** |

## 4. Classification of the 332

| Class | Count | Cost to resolve |
|---|---|---|
| **IDENTICAL** variant sets across all declarations | **192** | low |
| — of which pure tier-mirrors (same relative path under a different `lib/<tier>/`) | 86 | mechanical |
| — identical but not tier-mirrored (independent re-declarations) | 106 | low |
| **DIVERGENT** variant sets — genuinely distinct enums sharing a name | **140** | high |
| — spanning multiple top-level subsystems (real cross-module exposure) | 84 | highest priority |
| — confined to one subsystem | 56 | lower |

Identical duplicates are benign under *either* collision policy: whichever
declaration wins carries the same variants. **The 140 divergent names are the
live hazard**, and the 84 that span subsystems are the prioritised set.

No dead-duplicate class was separately identified; dead copies fall inside the
IDENTICAL group and are only distinguishable by reachability analysis, which
this pass did not perform.

Worked example of a divergent collision — `StepMode`, 13 declarations, 3
distinct variant sets:

```
app/dap/dap_types.spl:120        StepOver, StepIn, StepOut
app/dap/hooks.spl:401            Over, Into, Out
app/interpreter/debug.spl:23     Continue, StepOver, StepInto, StepOut
```

Under MIR last-wins, arms naming `StepIn` or `Into` silently never match
wherever another declaration registered later.

Top divergent names by subsystem spread are the first rows of the companion TSV:
`OptimizationLevel`, `SymbolKind`, `VariableScope`, `TaskState`, `UnaryOp`,
`StepMode`, `HttpMethod`, `TokenKind`, `LogLevel`, `ValueKind`.

## 5. The named-type registry is a separate, still-real bug

Even though it does not govern variant dispatch, `named_type_register` gives two
same-named structs/classes/enums **one shared type id**, hence one shared type
tag (`TYPE_NAMED_BASE + idx`), and for non-empty field sets the *last* writer
overwrites the fields of the first. That is a genuine type-identity collision
across 2,299 names and should be tracked on its own.

Feasibility of module-qualifying that registry (PROVED unless noted):
- All ~40 readers/writers live inside `src/compiler/`; nothing outside depends on it.
- `named_type_name(type_id)` feeds **C identifiers** directly (`type_to_c`,
  `types.spl:536-543`; `cg_stmt.spl:244,299`). Qualifying the key without a
  separate display name would emit `mymod.Style x = ...;` — invalid C. A
  key/display split is mandatory.
- **No `current_module` variable exists in the parser** (zero hits for
  `current_module|cur_module|par_module|module_prefix` across `parser*.spl` and
  `_ParserDecls/*.spl`). The only available context is the file path via
  `module_get_path()` — per-file, so nested `module` bodies get no finer
  granularity. This is the main obstacle.
- **Nothing persists type ids to disk** (no hits across `80.driver/cache/*.spl`
  or `incremental.spl`); ids are wiped by `reset_all_pools()`. Re-keying
  invalidates no cached artifact. (PROVED negative.)

## 6. Options for the owner

**A. Re-key the MIR variant maps by `runtime_name`, bare-name fallback.**
Smallest change that fixes the *class* of enum match miscompiles. Uses an
already-existing qualified identity. Touches `module_lowering.spl:241,244` and
`enum_variant_discriminant`, plus the global bare-arm fallback scan at
`switch_operators_calls.spl:1690-1699`. **Recommended first step.**

**B. Align the interpreter to the same key and policy** (`eval_tables.spl:603`)
so the two engines stop disagreeing, and add a hard collision diagnostic modelled
on the existing `enum_runtime_id_index` error at `module_lowering.spl:191-203`.
Should ship with A, otherwise A creates a *new* divergence.

**C. Then, and only then, promote the match-fallthrough diagnostic to fatal.**
It landed warn-only (`b2d42b02ecc`) because the collision made exhaustiveness
unreliable. A+B remove that blocker; note the lint's own table
(`35.semantics/lint/match_exhaustiveness.spl:110-115`) is also bare-keyed and
needs the same treatment.

**D. Named-type registry qualification** — separate lane, larger, needs the
key/display split and a module-context source that does not currently exist.

**E. Renames — fallback only.** If A is rejected, work the 84 divergent
cross-subsystem names from the TSV, using the known-good shape: pure mechanical
rename, no assertion changed (precedent: variant `Style` -> `StyleMutation`,
8 occurrences across 6 files). **A 332-name sweep is not recommended** and was
explicitly not performed here; 192 of the 332 are benign.

## 7. Verification notes

- Every mechanism claim above is PROVED by direct read of the source at
  `5ca84bcefe5`, not by running the compiler. No behavioural measurement was
  taken in this pass, so no engine is claimed clean.
- At this tip **no binary detects a missing enum variant or a wrong variant
  set** — this defect is precisely why. "No error appeared" is therefore not
  evidence of correctness anywhere in this area.
- Counts came from `/usr/bin/grep`; the default `grep` on this host is ugrep and
  the two have disagreed before.
- Symlinked compiler layer directories were not followed, so no path
  double-counting.
