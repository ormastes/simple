# Enum bare-name collisions: enumeration, mechanism correction, and resolution options

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

**Date:** 2026-08-01
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
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

---

## 8. Step (b) LANDED: the miss is now loud

Sequencing recap: (a) restore a test-capable binary, **(b) make the miss loud
and absorb the fallout**, (c) only then dual-key by `runtime_name`, (d)
reconcile the Rust seed. (b) and (c) must not be combined — re-keying while the
silent `-1` paths existed would have made ALL enums silently wrong instead of
only the 140 divergent ones.

This section records (b). **No map was re-keyed in this change.**

### What was silent, and what it says now

A collision registry is recorded at registration time in
`register_enum_variants` (`50.mir/_MirLowering/module_lowering.spl`): when a
bare enum name is overwritten by a registration whose variant set **differs**,
the prior and new sets plus the new `runtime_name` are stored in the new
`enum_bare_name_collisions` map. Identical re-registrations (the 192 benign
duplicates) record nothing. `enum_variant_miss_detail`
(`50.mir/_MirLoweringExpr/switch_operators_calls.spl`) turns that into a
message naming the enum, the variant, and the colliding owner, plus every other
registered enum that does declare the variant.

Four previously-silent paths now emit it:

| Site | Was | Now |
|---|---|---|
| `lower_enum_construct_named` | fully silent; `-1` emitted straight out as the discriminant constant, no guard at all | loud `enum variant lookup miss:` |
| `lower_enum_lit` | guarded only for an *unregistered* enum; a registered enum missing the variant (the collision case) emitted `-1` silently | loud `enum variant lookup miss:` |
| `?` try-operator `none_disc` | `Option.None` resolving to `-1` made the equality test unfireable, so every boxed Option silently took the Some lane | loud, and falls back to the reserved `None=1` |
| bare-pattern sole-owner borrow | `owner_count == 1` borrowed an unrelated enum's discriminant with no diagnostic | loud **only when that owner's bare name is a recorded divergent collision**, so ordinary unqualified `case Circle(r)` stays quiet |

Interpreter sibling (`10.frontend/core/interpreter/eval_tables.spl`):
`enum_table_register` is bare-keyed **first-wins** and silently `return`ed on
the second registration — the opposite resolution from MIR's last-wins, so the
two engines pick *different* enums for the same source. It now reports a
divergent drop via `_enum_warn_bare_name_collision`, mirroring the existing
`_ftr_warn_collision` precedent in the same file (dedup list, divergence gate).

### Deliberately NOT done

- **Nothing was made fatal.** All new messages use the prefix
  `enum variant lookup miss:`, which is absent from `_mir_error_is_fatal`'s
  allowlist in `80.driver/driver_pipeline_lowering.spl`, so they land as
  warnings. Note the pre-existing `enum match:` guards there ARE already fatal;
  they were left exactly as-is. Promoting anything to fatal stays blocked on
  resolving the 332 duplicated names.
- **No re-keying.** That is step (c).
- **The Rust seed was not touched.** It still derives a discriminant by hashing
  the variant name alone with no enum identity, so it collapses every collision
  by construction and disagrees numerically with both other engines even for
  non-colliding enums. That is step (d) and remains open.

### Evidence

Regression spec:
`test/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.spl`
(11 examples). Run under the interpreter via
`bin/simple_seed test <spec>`, which imports `compiler.mir.mir_lowering` and so
genuinely executes `src/compiler/50.mir/**.spl` — it is **not** the seed's own
Rust compile path.

- **MIR `.spl` surface — PROVED.** True-positive control: the spec constructs
  two divergent enums both named `Style`, and `lower_enum_construct_named`
  records an error whose text contains the variant and the colliding owner.
  RED control: deleting that one `self.error` call takes the suite to
  10 passed / 1 failed; neutralising the collision-recording branch in
  `register_enum_variants` takes it to 4 passed / 2 failed. A syntax fault
  injected into `switch_operators_calls.spl` aborts the run entirely,
  confirming the file is loaded from the tree under test.
- **Interpreter surface — PROVED.** The warning was observed *emitted at
  runtime*, not merely asserted in source: `[WARN] enum 'Style' has co-compiled
  declarations with DIFFERENT variants ([Bold,Italic] vs [Plain,Reverse]) ...
  [compiler_enum_bare_name_collision]`. The benign identical re-registration in
  the same run produced no warning, so the divergence gate is real.
- **Rust seed surface — NOT COVERED.** No control was run and none is claimed.

### Fallout

Measured on the interpreter surface, where the check is observable today:
across the compiler module graphs loaded by the MIR/backend/semantics/borrow
specs, **zero real divergent collisions fired**. This is a live-zero, not an
inert-zero: the synthetic control warning fired in the *same process*.

The repo-wide count remains **INFERRED**, bounded above by the 140 divergent
names in `enum_bare_name_collision_enumeration_2026-08-01.tsv`. Measuring it
properly needs the pure-Simple compiler to compile the whole repo. The binary
at `bin/simple` is the **Rust-built driver** — it prints its own
"bootstrap seed only" banner and does not embed the MIR `.spl` strings
(`strings | grep "enum construction: unregistered enum"` returns 0 for it and 2
for the bootstrap-stage binaries). It therefore cannot produce a repo-wide
fallout number for this change.

## 9. Step (c) LANDED: dual key by `runtime_name`

Base `1a6c1e362a5`. The lowering now carries a **second, qualified keyspace**
alongside the bare one. The bare maps are unchanged and still last-wins; nothing
was re-keyed in place, and the loud-miss machinery from step (b) is untouched.

### The five new maps (`50.mir/mir_lowering_types.spl`)

| Map | Key | Why |
|---|---|---|
| `enum_variant_index_q` | `runtime_name` | variant names, one entry per DECLARATION |
| `enum_variant_discriminants_q` | `runtime_name` | discriminants, parallel |
| `enum_runtime_id_index_q` | `runtime_name` | runtime identity |
| `enum_runtime_to_bare` | `runtime_name` | lets a scan hand a bare name back |
| `enum_bare_ambiguous` | bare name | the ambiguity flag, set on DIVERGENCE only |

`runtime_name` is `"{owner_module}.{Name}"` (`declaration_lowering.spl:755`) and
is unique per declaration, so **nothing is ever evicted from the qualified
maps** — both sides of a bare-name contest survive registration.

### Why this could not become a new silent wrong answer

Every reader is **qualified-first with a bare fallback**, and the fallback is
*exactly the pre-dual-key behaviour*. An un-migrated caller, or a caller whose
derived key is absent (module-name normalization drift), degrades to what it did
before — never to something new. The key is a full `"module.Name"` string, so a
mis-normalized prefix produces a **miss**, never a wrong hit.

One deliberate asymmetry: `enum_variant_discriminant_for` falls back only when
the qualified key is **not registered**, *not* when the qualified lookup
returned `-1`. If a declaration is registered and genuinely lacks the variant,
that stays a miss — letting the bare last-wins map rescue it would silently
borrow a same-named variant from a *different* enum, i.e. reintroduce the defect.
Pinned by the spec case *"does NOT let the bare map rescue a genuine qualified
miss"*.

### The four `.keys()` scans — the actual design problem

`module_lowering.prescan_enum_owner_for_variant`, the `expr_dispatch` binding
reclassification, and two in `switch_operators_calls`
(`resolve_enum_pattern_owner`, `lower_enum_match`) search for the enum that owns
a **bare** variant. They **cannot be handed a `runtime_name` by construction** —
the owner is the unknown they are searching for.

**Resolution: they do not produce a qualified key, they CONSUME the qualified
keyspace.** All four now route through one shared helper
`variant_owner_keys(variant)`. The bare map held one entry per bare *name*, so
two distinct same-named enums collapsed into a single survivor and the scans
reported *"exactly one owner"* for something genuinely ambiguous — then silently
emitted the survivor's discriminant. Counting over the per-declaration keyspace
makes the count truthful, so a real ambiguity now reaches the **already-existing
loud error** instead of a silent borrow. No new silence, and no new fatal.

`variant_owner_keys` collapses entries that would give the **same answer** (same
bare name **and** same discriminant). Without that dedup the 192 benign
identical re-registrations — and the built-in `Option`/`Result` seeds sitting
beside their real stdlib declarations — would each report a spurious ambiguity
and turn ordinary `case Some(x)` into a compile error.

### Read-site migration count

Of the **110** hits (102 code + 8 comment), **18 lines referencing the bare maps
were replaced** (counted from the diff, not estimated). Everything else is
untouched and keeps working through the bare fallback. Diffstat: 5 files,
+368/−55.

Those 18 lines span **9 read sites**:

- **2 central readers** re-pointed qualified-first
  (`enum_variant_discriminant`, `enum_runtime_id`) — this alone covers their
  ~15 indirect callers without touching any of them.
- **4 owner-search scans** → the shared `variant_owner_keys`.
- **2 symbol-holding call sites** now derive a key (`lower_enum_lit`,
  `lower_enum_match`); `resolve_enum_pattern_owner` is the third and is counted
  among the scans.
- **1 diagnostic scan** in `enum_variant_miss_detail` — it can now name the
  **evicted** declaration by runtime_name, which was previously impossible
  because the bare map no longer contained it.

Plus **7 new helper methods** (`enum_qualified_key`, `enum_bare_of`,
`variant_owner_keys`, `enum_has_variants`, `enum_variant_names`,
`enum_variant_discriminant_for`, `register_builtin_enum_dual`) and **9
write/seed/propagate sites**: the two registration functions, the per-module
reset gate, the 4 built-in Option/Result seed calls (2 in `module_lowering`, 2
in `bootstrap_globals`), and the lambda sub-lowering propagation.

Of the **41** hardcoded `"Option"`/`"Result"` lookups, only the 4 seed sites are
touched; the other 37 stay on the bare key **deliberately** — the built-ins have
no owner module, so their `runtime_name` *is* their bare name
(`declaration_lowering.spl:755` returns the bare name when `owner_module` is
empty) and both keys agree by construction.

`enum_qualified_key` reuses the existing MIR-layer normalizer
`bootstrap_mir_logical_module_name` rather than adding a **fifth** copy of a
helper whose own in-tree comment says to keep every copy byte-identical.

Two consistency traps were handled explicitly, both instances of *gate the clear
to match the writer*:

1. `enum_runtime_id_index` is reset per module; `enum_runtime_id_index_q` is now
   reset by the **same gate**. Leaving it populated would let a qualified read
   return a *stale* identity from a previous module — a stale hit is worse than
   the miss it replaces.
2. The lambda sub-lowering copies the bare maps into a child `MirLowering`; it
   now copies the qualified maps too, or every read inside a lambda body would
   silently degrade to the bare fallback.
3. In `lower_enum_lit` the runtime **identity** and the **discriminant** are
   resolved from the same key — pairing enum A's identity with enum B's
   discriminant is the same class of silent wrong value.

`enum_name` is kept **bare** wherever it also keys `enum_payload_struct_names`
(`"{enum_name}::{variant}"`); qualifying it there would turn every
payload-struct lookup into a miss. `enum_bare_of` exists for exactly the sites
that compare a resolved owner against a bare literal (`== "Option"`).

### Evidence

- **Lever is live — PROVED.** `bin/simple_seed test <spec>` on a spec importing
  `compiler.mir.mir_lowering` executes `src/compiler/**.spl`: sabotaging
  `enum_variant_discriminant` (an early `return -999` in the **implementation**,
  not a shim) took the step-(b) spec from 11/11 to 9/11, rc=1.
- **RED before GREEN — PROVED.** Sabotaging the qualified **write** side
  (`variant_index_q["__sabotage__"]`) took the new spec from 16/16 to 8/16.
  Eight distinct examples depend on the real dual-key write.
- **MIR surface true-positive control — PROVED.** In the same object that
  resolves `web.layout.Style.Bold` → 0, the **bare** lookup
  `("Style", "Bold")` still returns **-1**. The qualified hit therefore cannot
  be the bare map quietly answering.
- **Interpreter surface true-positive control — PROVED.** `enum_table_register`
  still drops the second divergent declaration **first-wins**
  (`enum_table_lookup("Style") == "Bold,Italic"`), the exact opposite of MIR's
  last-wins, with a fresh-name control registering normally in the same process.
- **Rust seed surface — INFERRED (static).** Pinned at source: the seed's
  `enum_variant_discriminant(variant_name: &str)` hashes the **variant name
  alone** and masks to 32 bits. This is a source pin, **not** runtime evidence;
  it is not presented as such.
- **Hand-computed expectations.** Every discriminant assertion is derived from
  the declared variant order, and **no** assertion has 3 as its correct answer
  (3 is the nil sentinel). One expectation of the author's was **wrong and the
  spec caught it**: two enums whose colliding variant sits at the *same* index
  are not a real ambiguity, because either choice emits the same discriminant.
  The case was rewritten to make the indices differ (0 vs 1), which is the
  actual hazard.
- **Native column — UNMEASURABLE.** `match` on an enum has no native lowering
  (`compile --native` fails closed with `[PatternMatch]`). Not claimed either way.

### Fallout — measured, ZERO

At base `1a6c1e362a5`, `test/01_unit/compiler/mir` run before and after:

- 8 files up to the pre-existing runner abort in
  `chr_native_lowering_contract_spec` (aborts identically both sides):
  failure name sets and per-example counts **identical**.
- The remaining **44** files run explicitly: **17 pre-existing failures before,
  17 after, failure NAME SETS identical**, and per-example `(passed, failed)`
  counts identical.
- The two enum specs: **16/16** and **11/11** green on the new tip.

### Deliberately NOT done

- **The fall-through warning is still warn-only.** Promoting it to fatal remains
  blocked on resolving the 332 duplicated names, which is downstream of this.
- **No bare map was removed or re-keyed in place.** The 332 duplicates still
  exist; this step gives readers a keyspace in which they no longer have to
  collide, it does not eliminate the collisions.
- **The interpreter's first-wins table is untouched**, so the two engines still
  disagree. That reconciliation is not step (c).

## 10. Step (d): the seed's discriminant is a RUNTIME ABI, not a compiler convention

This step was scoped as "give the Rust seed enum identity". Measuring it first
changed what the correct action is, so the finding is recorded before the change.

### The measured shape of the problem (PROVED)

The seed's discriminant is **not** a compiler-internal convention living in four
duplicated functions. It is a **cross-crate runtime ABI** with the authoritative
definition in the runtime crate:

`runtime/src/value/objects.rs:251` — `hash_variant_discriminant(variant_name: &str) -> u32`

and it is consumed by four independent surfaces:

| Consumer | Site |
|---|---|
| the runtime itself, building `Option` values | `runtime/src/value/objects.rs:262,266,340` (`rt_option_some` / `rt_option_none`) |
| the **bytecode** compiler, emitted into the instruction stream | `codegen/bytecode/compiler.rs:175,499` |
| the **interpreter SFFI** | `interpreter_extern/enum_sffi.rs:26` (its own comment: reuses the shared fn to match semantics EXACTLY) |
| four duplicated copies inside the compiler | `mir/lower/lowering_expr_method.rs:125`, `hir/lower/expr/access.rs:716`, `hir/lower/expr/mod.rs:92`, `codegen/llvm/emitter.rs:245` |

All five definitions compute the identical value —
`DefaultHasher(variant_name).finish() & 0xFFFF_FFFF` — differing only in return
type (`u32` in the runtime, `i64` in the compiler copies). **Verified by
reading all five.**

**Consequence, and the reason the original plan was wrong:** adding enum
identity to the compiler copies alone would leave `rt_option_none()` in the
*runtime* still emitting `hash("None")` while compiled pattern tests compared
against something else. That is a silent wrong answer at the ABI boundary — the
exact failure mode this campaign exists to remove, and forbidden by the standing
rule against trading a loud failure for a silent wrong one.

**Second correction:** all **six** call sites of the four duplicated copies are
hardcoded to `Result`'s `Ok`/`Err` for the builtin `is_ok` / `is_err` / `.ok` /
`.err` fast path. The enum identity is *already known* at every one of them.
These functions are therefore **not** the general enum-lowering path, and
"the seed has no enum identity here" overstates the practical exposure at these
particular sites. The general path is `hash_variant_discriminant` itself.

### What this step DID land

The four duplicated copies now **delegate to the single authoritative runtime
definition**. Behaviour-preserving by construction (all five computed the same
value), and it turns five definitions of an ABI into one — which is the actual
prerequisite for ever changing it. `access.rs` also drops its now-unused
`DefaultHasher` / `Hash` / `Hasher` imports.

Three **executable** controls were added on the seed surface
(`mir/lower/lowering_expr_method.rs`, `enum_discriminant_abi_tests`). Every
earlier lane could only pin the seed by *reading its source*; these run it:

1. `seed_wrapper_agrees_with_the_runtime_abi` — the wrapper is the same function
   as the runtime's, for `Ok/Err/Some/None/Circle/Bold`.
2. `seed_collapses_same_named_variants_of_different_enums` — the collapse is
   **measured**: two unrelated enums' `Circle` get the identical discriminant,
   while `Circle` vs `Square` differ (so the first assertion is not vacuous).
3. `seed_discriminant_is_a_hash_not_the_declared_ordinal` — `Ok != 0`,
   `Err != 1`, and `Ok > u16::MAX`. This pins the numeric disagreement with the
   MIR `.spl` lowering (which uses declared ordinals) so it cannot be quietly
   claimed resolved.

Test 2 and test 3 are written to **FAIL the moment the seed gains enum identity
or switches to ordinals** — deliberately. Whoever makes that change is forced to
come here and revise the expectation, rather than discovering the ABI break in
the field.

### Evidence

- **Fallout ZERO — PROVED.** `cargo test -p simple-compiler --lib` at base
  `1f7b8277e36`: **3464 passed / 118 failed** before, **3467 passed / 118
  failed** after. The +3 are exactly the three new controls; the failure **NAME
  SETS are byte-identical** (`diff` of the two 118-name lists is empty).
- **RED before GREEN — PROVED, sabotaging the IMPLEMENTATION.** Reverting one
  wrapper to a *drifted* local copy (masking `0xFFFF` instead of `0xFFFF_FFFF`)
  failed 2 of the 3 controls with the intended message — *"seed wrapper diverged
  from the runtime ABI for variant Ok"*. Restoring returned 3/3 green. The
  controls therefore catch exactly the drift they exist to catch.

### NOT done, and why

**Reconciling the numeric disagreement is NOT done.** Making the seed agree with
MIR means moving the discriminant from a name-hash to the declared ordinal
across **the runtime, the bytecode format, the interpreter SFFI, the four
compiler sites and MIR, together, in one coordinated ABI change** — plus
rebuilding every artifact that embeds the old numbering. It cannot be done
seed-side, it is not reversible file-by-file, and a partial attempt is a silent
wrong answer at the ABI boundary. It needs its own sequenced lane with an
artifact-compatibility plan. The three controls above are the tripwire that
keeps it honest in the meantime.
