# Spec-Vacuity Families 3 & 4 — Full-Corpus Census

_Driver: `scripts/check/census-spec-vacuity.spl` (landed `bbe4682d52b`)._
_Status: **IN PROGRESS** — corpus/dedup section final, scan results pending._

## What this census is, and what it is not

Four spec-vacuity families are known in this repo:

1. **Non-matcher `expect` tail** — a tail method that exists on the argument's
   type but is not a matcher, so nothing is asserted. **GATED** at `47ba20fda2b`;
   its full-corpus RED census is a *separate* document,
   `expect_vacuity_gate_full_corpus_census.md` (execution-based, 2372/9872 at
   `b5b1b11b2fb`).
2. **The needle matches only a COMMENT** in the product source. Not yet gated;
   no automated scorer.
3. **A value-type helper mutates a COPY** — codes `VTM001` / `VTM002`.
4. **The spec re-implements the code under test, in-spec** — codes `SHADOW` /
   `NOSRC`.

**This document covers families 3 and 4 only.** They are the two families the
census driver scores, and unlike family 1 the driver is *static*: it does not
execute specs, so it is not subject to the daemon/timeout/no-verdict infra noise
that dominates the family-1 census buckets.

Positive control is fatal and reproduced on every run:

```
control: 5 planted VTM violations detected, 8 correct forms silent
control: SHADOW fires on a colliding name, silent on a spec-only name
```

## Corpus and duplicate-tree dedup

`test/01_unit` ≡ `test/unit` and `test/03_system` ≡ `test/system` are duplicate
trees and **both execute**. Counting them naively double-counts nearly half the
corpus.

| measure | count |
|---|---|
| raw `*_spec.spl` under `test/` | 19,599 |
| unique by content sha256 | 9,940 |
| **duplicate files (raw − unique)** | **9,659 (49.3% of raw)** |

Per-mirror-pair breakdown (files present at the same relative path in both
trees):

| pair | paired files | byte-identical | divergent |
|---|---|---|---|
| `test/01_unit` ↔ `test/unit` | 5,006 | 4,178 | 828 |
| `test/03_system` ↔ `test/system` | 336 | 276 | 60 |

Two things follow, and both matter for any gate built on these numbers:

- The mirrors are **not** clean copies. 888 paired files diverge in content, so
  a fix landed in one tree is not automatically live in the other, and a
  finding in one tree must be checked in its twin by hand rather than assumed
  identical.
- `test/01_unit` (7,497 specs) is much larger than `test/unit` (5,013) and
  `test/03_system` (3,363) than `test/system` (1,862) — the numbered trees are
  supersets, not renames. Divergence is fenced by
  `scripts/check/check-test-tree-divergence.shs` against
  `scripts/check/test_tree_divergence_baseline.txt`.

### The driver's dedup is fail-open — 5,731 specs are silently dropped

The driver's `is_duplicate_tree` is a **prefix predicate**: every path under
`test/01_unit/`, `test/02_integration/`, `test/03_system/`, `test/04_external/`
or `test/05_perf/` is marked `dup` and excluded from the deduped column. That
assumes the numbered trees are copies. They are not — they are supersets, and a
large fraction of their files have **no twin at all** in the unnumbered tree:

| numbered tree | specs | paired with twin | **orphans (no twin)** |
|---|---|---|---|
| `test/01_unit` | 7,497 | 5,006 | **2,491** |
| `test/03_system` | 3,363 | 336 | **3,027** |
| `test/02_integration` | 735 | 586 | **149** |
| `test/05_perf` | 102 | 38 | **64** |
| `test/04_external` | 0 | 0 | 0 |
| **total** | | | **5,731** |

A VTM/SHADOW finding in any of those 5,731 files is counted in the **raw**
column only and vanishes from the **deduped** column, even though nothing else
in the corpus covers it. So the deduped column is a *lower bound*, not a true
unique count — read the raw column as the real exposure, and treat any gate
built on the deduped number as fail-open by construction. Fixing this requires
the predicate to check for an actual twin at the mirrored path (and compare
content), not to match a prefix.

Every finding count below is reported **deduped / raw** as the driver emits it,
with that caveat attached.

## Method notes (reproducibility)

- Binary: `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`. It
  announces itself as the Rust bootstrap seed. `bin/simple` was **not** touched
  or relinked.
- The driver's module drops to the **interpreter** (`[jit-fallback] unresolved
  external symbol 'rt_file_is_char_device'`), costing the documented ~100-1000x.
  A whole-corpus run is therefore tens of minutes, not seconds.
- `SIMPLE_TIMEOUT_SECONDS=0` is **required**. Without it
  `kill_simple_monitor` SIGTERMs the run at 60s CPU and the census dies with no
  verdict line — indistinguishable from a clean zero unless you read the
  `TIMEOUT: killed by kill_simple_monitor` line.
- Chunking by root is counter-productive: `build_kind_index` re-scans all of
  `src/` on **every** invocation, so N chunks pay the dominant fixed cost N
  times. One whole-`test/` run is the cheapest form.

## Results — family 4 (SHADOW), independent cross-check

The driver's own whole-corpus run is slow (see below), so family 4 was also
computed by an independent path over the same corpus: extract every
`^(struct|class|enum) Name` from `src/**.spl` and from every `*_spec.spl`, and
intersect. This is the *same* rule the driver's `SHADOW` implements, derived
separately, so agreement between the two is a real cross-check rather than a
restatement.

| measure | count |
|---|---|
| distinct type names declared under `src/` | 13,232 |
| distinct type names declared in spec files | 1,478 |
| **distinct names declared in BOTH (`SHADOW` names)** | **626** |
| spec files declaring at least one shadowed name — raw | 583 |
| … in unnumbered trees only (driver's "deduped" view) | 275 |
| of those 583, also importing **nothing at all** (`SHADOW` ∧ `NOSRC`) | 410 raw / 199 unnumbered |

**Precision caveat, stated up front.** A bare name collision is not by itself a
finding. `test/feature/usage/*_spec.spl` are *language*-feature specs — they
declare `struct Point2D`, `enum Color`, `struct Shape` on purpose, because the
thing under test is the language's struct/enum machinery, not a library type.
Those are correct and must not be "fixed". The signal only becomes actionable
when the shadowed name is **specific**: declared in exactly one file under
`src/`, long enough not to be a generic noun, and shadowed by a spec that
imports nothing.

### Ranked worklist — 141 (spec, shadowed name, sole src/ declaration) triples

Full list: `doc/08_tracking/test/spec_shadow_reimplementation_worklist.tsv`
(50 distinct spec files). Filter applied: no `use` line anywhere in the spec,
shadowed name declared in exactly one `src/` file, name ≥ 12 chars,
`test/feature/**` and the numbered mirror trees excluded.

Highest-value entries:

| spec | shadows | sole src/ declaration | why it matters |
|---|---|---|---|
| `test/perf/bench/db_accel_planner/db_accel_planner_spec.spl` | `IndexDescriptor`, `PlanCandidate`, `PlanNodeKind`, `PredicateKind` | `src/lib/nogc_sync_mut/db/query_planner.spl` | A **benchmark** that re-implements the query planner in-spec. Its numbers describe spec-local code, not the product planner — a perf claim with no product under it. |
| `test/perf/bench/db_accel_index/db_accel_index_spec.spl` | `FilterInResult`, `PageSummaryIndex`, `TextIndexEntry` | `src/lib/nogc_sync_mut/db/{filter_in,page_summary,text_index}.spl` | Same shape: three index structures re-declared in the benchmark. |
| `test/unit/app/formatter/formatter_minimal_spec.spl`, `test/unit/app/formatter_minimal_spec.spl` | `FormatConfig` | `src/compiler/90.tools/formatter/main.spl` | Both copies re-declare the formatter's config and import nothing — the formatter itself is untested by them. |
| `test/unit/app/lint_simple_spec.spl` | `LintCategory` | `src/compiler/90.tools/lint/_LintMain/config_and_model.spl` | Lint's own category model re-declared in-spec. |
| `test/system/smux_system_spec.spl` | `MuxBackendKind`, `MuxClientAttachment` | `src/os/apps/smux/contract.spl` | A **system** spec re-declaring the smux contract it exists to pin. |
| `test/system/async_promise_system_spec.spl` | `WorkStealingQueue` | `src/lib/nogc_async_mut/async_host/scheduler.spl` | The scheduler's work-stealing queue re-implemented in-spec. |
| `test/unit/app/interpreter/core/environment_spec.spl` | `EnvironmentWithInterner` | `src/app/interpreter/core/environment.spl` | |
| `test/unit/compiler/all_regions_spec.spl` | `DomainHardenEntry`, `DomainKindRegistry` | `src/compiler/10.frontend/domain/domain_hardening.spl` | |
| `test/unit/app/test_runner/types_spec.spl` | `SkipFeatureInfo` | `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl` | The test runner's own skip model shadowed by the test runner's spec. |
| `test/integration/lib/database_core_spec.spl`, `test/integration/compiler/core_intensive_spec.spl` | `StringInterner` | `src/lib/nogc_sync_mut/database/core.spl` | |

The two `perf/bench` entries are the payload of this family: a green,
number-producing benchmark that never touches the code it claims to measure is
strictly worse than no benchmark, because it is cited as evidence.

## Results — family 3 (VTM001/VTM002)

Family 3 *can* be scored without the driver, because struct-vs-class is
recoverable by grep: `^(struct|class) Name` across `src/` and `test/` yields a
kind index (12,879 names; 6,025 `struct`), and a parameter's kind is then a
lookup, never a guess. An independent scorer was written to the same rules
(indentation-scoped function bodies, `mut` params excluded, `class` receivers
excluded, unknown/ambiguous types excluded) and validated against a planted
control matching the driver's: **5 planted violations fire (field assign,
nested field-chain `.push`, index assign, `.remove`, `+=`), 8 correct forms
stay silent.** Only then was it run.

| measure | raw | unnumbered trees |
|---|---|---|
| VTM001 (field/index assign through a struct param) | 25 | 6 |
| VTM002 (in-place mutator through a struct param) | 8 | 3 |
| **total findings** | **33** | **9** |
| distinct spec files | 29 | — |

Full list: `doc/08_tracking/test/spec_value_type_mutation_worklist.tsv`.

### Every finding was read. Only 2 are real — and that is the headline

Hand-adjudicating all 33 gives a **true-positive rate of ~6%**. The rule as
specified is not gate-ready, and shipping it as a gate would have been the
"lint with a high false-positive rate gets disabled" failure the driver's own
header warns about. Two false-positive patterns account for nearly all 31:

- **`dict[param.field] = value` is not a mutation of `param`.** Nineteen of the
  25 VTM001 hits are the single line `functions[func.symbol] = func` inside
  `make_module(func: MirFunction)` / `make_hir_module(fn_: HirFunction)`
  helpers across the backend, borrow-check, codegen and resource specs. The
  param appears only as a *dict key expression*; the assignment target is a
  local. `mock_manifest_update`'s `entries[e.source_path] = e` is the same
  shape. An index-assign pattern must require the param to be the **base** of
  the assignment target, not merely to appear left of the `=`.
- **`add` is not always a mutator.** `double_f32x4(v: Vec4f) -> Vec4f: v.add(v)`
  returns a new vector; nothing is mutated. `add` (and `set`, `put`) sit in the
  driver's mutator token list too, so the driver inherits this. A returned
  expression whose value is the function's result should never be flagged.
- Also excluded on inspection: `upsert_count(entries: [CountEntry])` — the
  param is an **array**, which is likewise a value type, but the function
  `return`s it and the caller rebinds, so the write-back is real;
  `append_unique(items: text)` — `text` is a primitive, not an indexed struct.

### The two genuine findings

**1. `test/unit/os/kernel/memory/vmm_vma_spec.spl:72` — `_space_add(space: ProcessVmSpace, area: VmArea)`. This is the payload of the whole census.**

```
fn _space_add(space: ProcessVmSpace, area: VmArea) -> i32:
    """Local vma_add implementation for tests — same logic as vmm.spl."""
    ...
    space.areas.push(area)
    space.vma_count = space.vma_count + 1
```

`ProcessVmSpace` is a `struct`, so **both** writes land on a copy and the
caller's `var space` never changes. It is called 9+ times, and the assertions
depend on the writes being visible:

```
val rc1 = _space_add(space, a1)
val rc2 = _space_add(space, a2)
expect(rc2).to_equal(-17)          # -EEXIST, requires a1 to be recorded
expect(space.vma_count).to_equal(2)
```

The overlap-rejection scenario is the sharp one: if `a1` was never recorded,
`_space_add(space, a2)` scans an empty space and returns `0`, not `-17`. So
either this spec is currently RED, or struct params are being passed by
reference by the engine that runs it — which would be an engine-divergence
defect in its own right, since `struct` is specified as a value type. Both
outcomes are defects and both are worth more than the spec's green tick.

It is simultaneously a **family-4** instance: the docstring says outright
*"Local vma_add implementation for tests — same logic as vmm.spl"*, and
`_space_find` likewise. The spec re-implements the kernel VMA allocator and
asserts against its own copy, so `src/.../vmm.spl`'s `vma_add`/`vma_find` are
**not covered by this spec at all** — while the known
`vmm_pml4_reads_zero_blocks_ring3_spawn` defect sits in the same subsystem.
This is exactly the shape the census exists to find: a green spec standing in
front of an uncovered, known-fragile kernel path.

**2. `test/{unit,01_unit}/compiler/interpreter/self_field_assign_spec.spl` —
`write_struct_dict_holder(self: MutableStructDictHolder, key, next)`**

```
struct MutableStructDictHolder: ...
fn write_struct_dict_holder(self: MutableStructDictHolder, key: text, next: i32) -> DictWriteResult:
    self.values[key] = next
    DictWriteResult.Success
```

The helper takes the struct **by value** and writes through it; the caller's
`var holder = MutableStructDictHolder(values: {})` is unaffected. The spec's
subject is *`self.field` assignment semantics*, so a helper that silently drops
its own field assignment is self-refuting: it returns
`DictWriteResult.Success` unconditionally, which is a success signal
independent of whether the write happened. Present in both mirror trees.

### What this means for gating family 3

The rule is sound; the two token-level patterns are not. Before `VTM001`/
`VTM002` can be promoted from census to gate, both need tightening — index
assign must be base-anchored, and mutator tokens must not fire on a returned
expression. With those two fixes the corpus yield is 2 findings, both real,
which is a gateable signal. Without them it is 33 findings at 6% precision,
which is not.

### Why the driver run is slow — an O(n²) index, recorded not worked around

`build_kind_index` inserts via `kind_index_add`, which **linear-scans** the
accumulated name list on every insert. With 13,232 distinct type names in
`src/` alone (plus the spec roots) that is ~10⁸ text comparisons, executed by
the **tree-walk interpreter** because the module drops out of JIT on
`rt_file_is_char_device`. The index phase alone exceeds 10 minutes and
dominates the whole scan.

This also defeats chunking: `build_kind_index(["src"] + roots)` re-scans all of
`src/` on **every invocation**, so splitting `test/` into N chunks pays the
dominant cost N times over. The cheapest form is one whole-`test/` run, which
is precisely the form most likely to be killed.

Two operational traps hit during this census, both of which produce a
**silent** wrong answer:

- The harness's background-Bash timeout caps at 600 s. A run past that is
  **SIGTERMed — exit 143, no verdict line**, which is indistinguishable from a
  clean zero unless the exit code is read. Run the census `setsid`-detached.
- `kill_simple_monitor` SIGKILLs any `simple` process at 60 s CPU.
  `SIMPLE_TIMEOUT_SECONDS=0` in the victim's environment is **mandatory**; it
  is read live from `/proc/<pid>/environ`, so it must be set on the census
  process itself, not on a wrapper.

Fix worth landing separately: replace `TypeKinds`'s parallel arrays with a
`Dict`, turning the index from O(n²) into O(n).
