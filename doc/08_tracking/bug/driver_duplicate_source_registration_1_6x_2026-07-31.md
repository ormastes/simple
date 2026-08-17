# Driver registers ~6,359 duplicate/alias SourceFiles (1.6x the source list)

**Date:** 2026-07-31
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
and load-bearing; "1.6x cost" is NOT supported by the source. One real O(N²) was
found nearby and is the actual actionable item. See "Static re-analysis" below.
**FIXED 2026-08-01** — the O(N²) linear scan is replaced by a `Dict<text, i64>`,
and the last open claim (per-alias `ParserModule` deep copy) is **disproven**: no
engine copies the AST at that line. See "Implementation 2026-08-01" below. The
whole-tree `collected=`/`unique=` measurement is still NOT taken.
**Found while:** investigating the stage-3 whole-tree parse-state defect. It is
**not** the cause of that defect (see "Not the discriminator" below), but it is a
real defect on its own.

## Measurement

Driving the real resolver helpers in
`src/compiler/80.driver/driver_source_loading.spl`
(`_driver_collect_sources`, `_driver_resolve_entry_import`,
`_driver_collect_entry_import_source`) and replicating the closure-walker at
`driver_source_pipeline_loading.spl:163-254`, over
`--source src/compiler --source src/lib --source src/app`:

| quantity | value |
|---|---|
| files on disk | 10,560 |
| `SourceFile` entries after the closure walk | **16,919** |
| duplicate / alias registrations | **+6,359 (~1.6x)** |

## Mechanism

`src/compiler/backend` is a symlink to `70.backend`, and imports use mixed
spellings. A single file can be registered under up to three distinct
`(path, module_name)` keys:

1. **canonical** — `compiler.70.backend.backend.vulkan_backend`
2. **same-path alias** — resolved via
   `_driver_resolve_numbered_compiler_import`'s last unconditional fallback
   (`driver_source_loading.spl:670`, `"compiler.backend"→"compiler/70.backend/backend"`).
   Same path as (1), but the computed `module_name` doesn't match the import
   string, so it is pushed as an alias rather than deduped. Comes from
   one-segment imports like `codegen_factory.spl:18`.
3. **symlink-exact** — `compiler.backend.backend.vulkan_backend`, resolved
   through the symlink by `_driver_try_entry_import_rel`
   (`driver_source_loading.spl:528-540`). Lexically different path string, same
   inode. Comes from two-segment imports like `mir_test_builder.spl:37`.

Dedup is by `(path, module_name)`, and all three keys differ, so nothing
collapses. The `compiler.backend[.backend].X` mixed-spelling pattern has **223**
occurrences tree-wide. Note there is **no** canonical `compiler.70.backend.`
spelling anywhere in the source — every import into that tree goes through the
symlink.

## Not the discriminator for the stage-3 parse failure

Registration counts were compared for the file that fails to parse and a control
with the identical import pattern:

- `vulkan_backend.spl` (the victim): **3** registrations
- `codegen_types.spl` (control): **3** registrations

Both are 3, so duplicate registration does **not** explain why `vulkan_backend.spl`
specifically corrupts the parser while the rest of the `70.backend/backend/`
subsystem does not. Hypothesis rejected. Still open for that defect:
order/timing dependence, or a content-specific parser side-table interaction
(matches unresolved hypothesis 3 in the earlier vhdl bug doc).

## Why it is worth fixing anyway

INFERRED (not measured): a 1.6x inflated source list costs parse time and peak
memory on the whole-tree bootstrap — the exact build currently too slow/heavy to
complete under load on this machine. Deduping by canonical path (resolve
symlinks and re-derive `module_name` before the dedup key) could materially
reduce stage-3 cost. This should be measured, not assumed, once a bootstrap can
be run to completion.

MEASURED facts above (file counts, entry counts, per-file registration counts)
came from a throwaway `.spl` probe compiled with `native-build --entry-closure`
(164 files, ~62s) — deliberately cheap, versus a full-tree build that twice ran
1800s and 3600s without emitting a byte.

---

# Static re-analysis 2026-08-01 (read-only, no builds — box in btrfs ENOSPC)

The paragraph above is **retracted**. Read of the registration path shows the
duplicates are intentional, that parsing and lowering are already deduplicated,
and that the alias branch is not even taken by the whole-tree build it blames.

## (a) Where the second registration happens, and why it was added

`_driver_module_aliases` — `src/compiler/80.driver/driver_source_loading.spl:320`,
entry-closure branch `:344-378`. It deliberately emits up to six spellings per
physical file via `_driver_push_unique_module_name` (`:348-374`): canonical,
the walked `module_name`, the path-derived physical name, the canonicalized
walked name, an optional `std.` twin (`:366`), and an optional `compiler.core.`
twin (`:373`).

Its docstring (`:321-343`) states the reason: symlinks (`src/compiler/frontend
-> 10.frontend`, `src/std -> lib`, ...) make the dotted name depend on which
path the resolver walked, and that varies **per file**, so two files in one
directory can land under different package prefixes.
`resolve_package_sibling_symbols`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1081-1117`) takes
the *self* prefix from the walked path and looks siblings up by registry key, so
a mismatch silently switches off directory-package semantics and every bare
cross-file call dies — **~530 stage-4 "unresolved name" errors from
`10.frontend/core` alone**. Registering all spellings makes the lookup succeed
whichever path either file was walked through.

A second, narrower registration site: the closure walk pushes an extra alias
under the literal import spelling when the path-derived name differs —
`src/compiler/80.driver/driver_source_pipeline_loading.spl:241-245`.

Note the symlink inventory is tree-wide, not `backend`-specific: **every**
numbered compiler dir has an unnumbered twin (`frontend`, `hir`, `types`,
`semantics`, `mir`, `driver`, ...), so the mechanism is general.

## (b) Redundant, or subtly different? — DIFFERENT. Deduping is a behaviour change.

This is the "one feeds a cache, one feeds a graph" case, explicitly. The two
consumers are already split:

| consumer | list used | state |
|---|---|---|
| parse plan + Phase 3 lowering | `unique_entry_sources` — **deduped by physical path** | `driver_source_pipeline_parsing.spl:142`, assigned to `entry_ctx.sources` at `:192` |
| module name → `ParserModule` registry | `entry_sources` — **deliberately inflated** | `driver_source_pipeline_parsing.spl:173-189` |

`_driver_entry_closure_mode` (`driver_source_loading.spl:202-217`) documents this
coupling as a two-site invariant that MUST agree: site 1 emits the aliases, site
2 (`parse_all_impl`) collapses them again with `_driver_unique_physical_sources`
before Phase 3. Decoupling them "feeds every alias into lowering and reinstates
the duplicate-HIR / duplicate-diagnostics regression".

So dedup **is already done everywhere it is safe**. Removing the remaining
duplicate module-name keys would re-break sibling resolution — a behaviour
change, not an optimisation. That is the finding.

The alias population has also already been tuned against measurement: the
docstring at `:355-365` records that making the `std.` twin unconditional grew
the tree-wide population 1.76x (12,795 → 22,504 entries, 19,144 registry keys),
so it was made conditional, landing at 1.25x. This is not unexamined code.

## (c) The 1.6x figure — real as a COUNT, unsupported as a COST

No doubled loop over N files exists on the parse path:

- **Import scanning is once per physical file.** The closure walk skips aliases
  by physical key — `driver_source_pipeline_loading.spl:191-195`.
- **`parse_full_frontend` runs once per physical file.** The parse loop iterates
  `unique_entry_sources`, not `entry_sources` — `driver_source_pipeline_parsing.spl:148`.
- **Phase 3 receives the deduped list** — `:192`.

**Measurement trap (the headline correction).** The alias branch is gated on
`_driver_entry_closure_mode()` = `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`
(`driver_source_loading.spl:344`, `:217`). In that same mode the implicit
whole-`src` bulk load is **suppressed** (`driver_source_pipeline_loading.spl:257-258`).
The whole-tree bootstrap the retracted paragraph blames runs with the mode OFF,
where `_driver_module_aliases` takes the legacy branch (`:379-401`) that aliases
only `compiler.frontend.core.*` — a narrow subset that cannot produce +6,359.
The 1.6x was measured in a configuration that is *by construction* not the slow
whole-tree build. Harness artifact read as a system property.

### What IS a real, source-supported cost

`_driver_text_list_index` (`driver_source_pipeline_parsing.spl:33-39`) is a
**linear scan**, called once per inflated `entry_source` at `:175` over
`parsed_entry_paths` (one entry per unique file):

    O(aliases x unique_files) ~= 16,919 x ~5,280 ~= 8.9e7 full-path text compares

That is a genuine O(N²) on which the 1.6x alias inflation acts as a linear
multiplier. It is a data-structure defect, not a reason to remove aliases.

**INFERENCE, not verified — must be measured, not assumed:** `ParserModule` is a
`struct` (`src/compiler/10.frontend/parser_types.spl:19`), i.e. a value type in
Simple. If `entry_modules[source.module_name] = parsed_entry_modules[parsed_idx]`
(`:189`) deep-copies, each of the 6,359 alias registrations copies a whole parsed
AST — which would make the 1.6x a real *peak-memory* factor even though it is not
a parse-time factor. This is the one claim in the original doc that may survive,
and it is exactly the claim nobody has checked.

## (d) Relation to the stage-4 facade self-hop quadratic (26.4x)

**Same hot path, adjacent halves of one quadratic — not a different area.**

- Issue A (fixed): the *inner* loop, `find_reexport_source` self-recursion,
  guarded at `module_lowering.spl:792`, landed as `9ae530acddb`. Cost is
  `O(E²)` in facade export items (`compiler.10.frontend.core.__init__` = 1,367),
  paid once per importing file.
- Issue B (this bug): the *outer* loop's key set. Aliases are added to
  `module_surfaces.index_by_name` (`src/compiler/20.hir/hir_lowering/module_surface.spl:128`;
  alias sites `:409` and `:417-444`), and that dict is **prefix-scanned, not
  keyed** per lowered module at `module_lowering.spl:1107`, with each surviving
  sibling triggering the `O(E²)` walk. Alias count therefore multiplies how many
  times the inner quadratic runs. `_driver_module_aliases`' own docstring
  (`:326-332`) names `resolve_package_sibling_symbols` as the consumer.

Verification of the alias → outer-loop link (all re-checked against source):

- `ModuleSurfaceBuilder.add_alias` (`module_surface.spl:155-171`) exists purely to
  bind an **extra module_name to an existing surface index**, and it does so via
  `module_surfaces_add_name(self.index_by_name, ...)` at `:167`. Alias spellings
  therefore **do** land in `index_by_name`.
- Both builder drivers take the alias route on a repeat physical path:
  `driver_source_pipeline_parsing.spl:90` and `module_surface.spl:409`; the latter
  then sweeps any still-unregistered spelling with `for alias in modules.keys():`
  at `:417`.
- `resolve_package_sibling_symbols` (`module_lowering.spl:1081`, invoked per module
  at `:1266`) iterates **the entire key set** — `for sibling_name in
  self.module_surfaces.index_by_name.keys():` at `:1107` — and only then filters by
  `starts_with(pkg_prefix)` at `:1110`. So the scan is `O(all keys)` per lowered
  module, and alias inflation multiplies it directly.
- The inner-loop guard is `if exp_source != wanted:` at `:792`, gating the
  self-recursion at `:793`; landed as `9ae530acddb`.

CORRECTION to an earlier draft of this section: it claimed
`doc/08_tracking/bug/hir_lowering_quadratic_symbol_define_2026-07-28.md` is stale
for still saying "no fix landed". **That was wrong** — re-reading it, the status
is deliberately scoped: root cause 1 is marked **REFUTED** on the stage-4 native
lane, and "no fix landed" refers to root causes **2 and 3**, which genuinely
remain unproven and unfixed. That doc is accurate; do not "correct" it.

Also note the in-source number is not a speedup ratio: the comment at `:789-790`
records **26.0 M allocations / 162 s for ONE importing file** on
`compiler.10.frontend.core.__init__` (1,367 export items). The "26.4x" figure
circulating for this fix is not stated anywhere in the source and should not be
cited as if it were.

## (e) The change to make (NOT made here), and how to verify it

1. **Do not dedupe the module-name registrations.** Load-bearing per (b).
2. **Fix the O(N²) instead.** Replace the `_driver_text_list_index` linear scan
   at `driver_source_pipeline_parsing.spl:175` with a `Dict<text, i64>` from
   physical key → index, built once in the parse loop at `:148-172`. Mechanical,
   no behaviour change, no effect on which names get registered. Observe the
   native Dict rules while doing it: bracket assignment only (the comment at
   `:181-188` records `.set()` silently failing at this exact site), never
   `Dict.len()`, and keep the value type `i64` so `.get()` stays safe.
3. **Then settle the memory question** — instrument whether `:189` copies the
   `ParserModule` struct per alias. If it does, hold an `i64` handle in
   `entry_modules` and index into `parsed_entry_modules`, which removes the
   memory factor without touching the key set.
4. **Only afterwards** consider reducing the alias count at source, by
   canonicalizing `pkg_prefix` inside `resolve_package_sibling_symbols`
   (`module_lowering.spl:1089-1105`) so one canonical key per file suffices.
   This is the principled fix but it IS a behaviour change and needs the ~530
   `10.frontend/core` unresolved-name errors as its regression gate.

### Verification on an idle box

- The instrumentation already exists: `log_phase("phase2:parse:closure:sources
  collected={} unique={}")` at `driver_source_pipeline_parsing.spl:144-145`.
  Run **the build that is actually slow** with phase logging on and read
  `collected` vs `unique`. That, not a probe in `--entry-closure`, is the number
  that would justify the work. Anything measured in a different mode is not
  evidence about the whole-tree build.
- A/B step 2 alone on one entry: expect `unique` unchanged, error count
  unchanged, and the wall-clock delta confined to phase 2.
- Regression canary for any alias-count change: the ~530 unresolved-name errors
  from `10.frontend/core`.
- Spec coverage gap: `test/01_unit/compiler/driver/driver_source_loading_spec.spl:12`
  asserts `aliases.len() == 1`, but it runs with the mode OFF, so it pins the
  legacy branch and does **not** cover the closure fan-out. A closure-mode spec
  would have to be added before changing `:344-378`.

---

# Implementation 2026-08-01 — (e)(2) LANDED, (e)(3) ANSWERED: no deep copy

## (e)(2) done — linear scan replaced by `Dict<text, i64>`

`_driver_text_list_index` is **deleted** (it had exactly one caller) and the
physical-key -> parsed-index lookup in
`src/compiler/80.driver/driver_source_pipeline_parsing.spl` is now a
`Dict<text, i64>` (`parsed_entry_index`) populated in the parse loop and read
with `contains_key(k)` + bracket index in the alias fan-out loop.
`O(entry_sources x unique_entry_sources)` -> `O(entry_sources)`.

Native Dict rules observed, per `doc/07_guide/language/dict_native_pitfalls.md`:
bracket assignment only (no `.set()`), no `Dict.len()`/`.length()` anywhere, and
the value type is `i64` so the bracket read cannot hit the corrupt
struct-payload path. No behaviour change: the same physical keys map to the same
parsed modules, the same cache-miss error fires on a miss, and the alias key set
is untouched — so the ~530 `10.frontend/core` unresolved-name canary is not in
scope for this change.

## (e)(3) ANSWERED — `ParserModule` is NOT deep-copied. The memory claim is DEAD.

The one surviving claim from the original filing does **not** survive. Verified
by reading the value representation on every engine that runs this line:

| engine | verdict | evidence |
|---|---|---|
| Rust seed interpreter | **reference** (refcount bump) | structs are `Value::Object { fields: Arc<HashMap<..>> }` — `src/compiler_rust/compiler/src/value.rs:1161-1164`; the hand-written `Clone` does `Arc::clone(fields)` — `value_pointers.rs:265-268`. Bracket assign is `Arc::get_mut`/`Arc::make_mut(&mut dict).insert(..)` — `interpreter/node_exec.rs:1063-1066`, `:1097-1102`; it moves the `Value` in and never touches its fields |
| seed Cranelift/LLVM + C runtime | **reference** (pointer store) | `rt_dict_set` takes `int64_t value` and stores `e->value = value` into an 8-byte slot — `src/runtime/runtime_native.c:5499-5503`, `:5400`, `:5409`. No `memcpy`, no struct-size awareness |
| pure-Simple native codegen | **reference** | the dict arm of index-assign is `box_runtime_value(...)` + `rt_dict_set` — `src/compiler/50.mir/mir_lowering_stmts.spl:1101-1141`; `box_runtime_value` falls through `case _: local` for struct-typed locals — `_MirLoweringExpr/expr_dispatch.spl:480-553` |

`copy_struct_value_recursive` (`mir_lowering_stmts.spl:147`) **is not reachable
from the index-assign arm** — its only callers are `let`/`var` binding from a
place expression (`:651`, `:826`) and by-value struct params
(`_MirLowering/function_lowering.spl:316`), and even then it recurses only into
nested *value structs*, copying Dict/array fields as raw handles.

There is one genuine shallow-one-level copy, and it is on a different line:
passing a struct **as a function argument** in the seed interpreter does
`fields: Arc::new((*fields).clone())` — `interpreter_call/core/arg_binding.rs:18-25`,
gated on `ClassDef::is_value_type`. That copies 21 field slots, each of which is
itself an `Arc`, so the AST is still shared. (Not fully resolved: whether
`is_value_type` is actually set `true` for a `struct` decl in the seed parser.)

**Therefore do NOT do step 3 as written.** Replacing the `ParserModule` value in
`entry_modules` with an `i64` handle swaps an 8-byte pointer slot for an 8-byte
integer slot: zero memory saved, one extra indirection added. Step 3 is closed
as a non-issue, not deferred.

## Still NOT measured — and why

The `collected=`/`unique=` reading on **the build that is actually slow** was not
taken; the whole-tree bootstrap has twice run 1800s/3600s without emitting a
byte, and this box is shared with parallel lanes. Stated plainly rather than
substituted with a proxy.

Note what section (c) already implies about the shape of the win: the alias
branch is gated ON `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`, and only in that mode
does `collected` exceed `unique` enough for the scan to be quadratic. In the
whole-tree build (mode OFF) the legacy alias branch is narrow, so `collected` is
close to `unique` and this fix is close to a no-op there. **The fix is correct
and removes a real O(N²), but it should not be advertised as the lever for the
60-minute whole-tree build until someone reads `collected` vs `unique` on it.**

## Spec status

`test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl`
example "registers every logical alias from one cached module result" was
updated to the new shape (asserts the `Dict<text, i64>`, the bracket assign, the
`contains_key` read; forbids `_driver_text_list_index(`, `.set()` and `.len()`
on the new dict). All eight assertions were verified GREEN against the edited
driver by running them in an isolated throwaway spec (`1 example, 0 failures`).

**Pre-existing, NOT caused by this change:** the full
`entry_closure_physical_source_dedup_spec.spl` file exits **255 with no example
output** on `simple.pre-segv-fix-20260731`. Proven pre-existing by deleting the
edited block and re-running — still 255. A control spec
(`test/01_unit/compiler/driver/driver_source_loading_spec.spl`) runs clean
(exit 0), so the harness itself is fine. Root cause of the 255 is unidentified
and belongs to that spec file, not to this fix.

Gotcha recorded while editing that spec: a bare `{}` inside an ordinary string
literal parses as an **empty interpolation**. Use a raw string (`r"..."`) or the
hand-concatenated `+ "{" +` idiom the file already uses at its
`_driver_entry_import_module_paths` example.

Also unchanged and still true: `driver_source_loading_spec.spl:12` asserts
`aliases.len() == 1` with the closure mode OFF, so closure fan-out remains
uncovered by specs. That gap gates step (e)(4), which was not attempted.

### Bottom line for the 60-minute builds

This is not the 1.6x lever it was filed as, and it should not be prioritised as
one. The defensible work here is the `O(aliases x files)` linear scan in (e)(2)
and the unresolved memory question in (e)(3) — both local, both cheap, neither
requiring the alias set to shrink.
