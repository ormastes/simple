# Census: enum-variant / struct-name bare-match collisions (repo-wide, ENUM1)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

Date: 2026-07-30
Scope: `src/compiler/**` and `src/lib/**`
Trigger: `SymbolKind` (11/15 variants shadowed by same-named structs in
`parser_types.spl`) was found and fixed in `5de6f3c56e8` + `3eb2635ea5c`
(PTR1) by renaming the structs to `Parser*`. This census asks: is
`SymbolKind` the only victim of this defect class?

## 0. Environment note (important — read first)

The working tree this agent started in (`HEAD` at the time, commit
`300210806975`) is **not** on the `main` branch lineage — it is a stale/
divergent checkout: `git merge-base --is-ancestor 5de6f3c56e8 HEAD` → **NO**,
and `git rev-list --left-right --count HEAD...main` → `4  86` (86 commits
behind main, 4 commits of its own not on main). On that stale tree,
`parser_types.spl` **still had the pre-fix names** (`struct Class`,
`struct Function`, `struct Struct`, `struct Enum`, `struct Trait`, unrenamed),
so an initial pass over the live checkout produced 214 candidate collisions
including phantom "still-broken SymbolKind" entries that are already fixed on
`main`.

To get a result that reflects the actual current codebase, this census was
**re-run against `git archive main`** exported to a scratch tree
(`/tmp/claude-1000/enum1work/main_tree`), not the live working directory. All
numbers below are against `main` (local branch / `origin/main`, both contain
the PTR1 fix). No `src/` file was modified; only a read-only git-archive
export in `/tmp` was used.

## 1. Method

1. `grep -rnE '^\s*(pub\s+|export\s+|public\s+)?enum [A-Za-z_]\w*'` over
   `src/compiler` + `src/lib` (`*.spl`) → 1,485 enum declarations.
2. `grep -rnE '^\s*(pub\s+|export\s+|public\s+)?(struct|class) [A-Za-z_]\w*'`
   same trees → 9,198 struct/class declarations.
3. A `gawk` driver (`extract_variants.awk`) walked each enum-bearing file
   once, tracking indentation to collect each enum's variant identifiers →
   10,914 (enum, variant) pairs, 4,194 distinct variant names, 7,034 distinct
   struct/class names.
4. `comm -12` of the two name sets → **204 names** are both a struct/class
   name and an enum-variant name somewhere in the trees.
5. Candidate pairs = every (enum, variant) whose variant name is in that
   204-name set → **476 candidate pairs**.
6. Real-risk narrowing: grepped `case [A-Za-z_]\w*\.[A-Za-z_]\w*[,:)]` across
   the same trees (2,106 raw matches → 919 distinct `Enum.Variant` bare-match
   tokens actually used in a `case` arm), intersected with the 476 candidates
   → **36 real-risk pairs** (a bare `case Enum.Variant:` exists **and** a
   same-named struct/class exists somewhere in the trees).
7. Empirical probe (below) on one non-`SymbolKind` real-risk pair.

Caveat on "reachable in scope": determining true lexical reachability
(import graph resolution) for 36 pairs across a self-hosted compiler was out
of budget for a census; scope was approximated by listing every case-match
file and every colliding declaration's file:line so a human/agent can check
imports before spending a rename. Given the proven mechanism is a **global**
bare-name registry (the original `SymbolKind` collision fired across totally
unrelated modules — parser-internal `parser_types.spl` vs. HIR-level
`hir_types.spl`/`compiler_query.spl` — with no lexical import between them),
cross-file "not obviously imported" should **not** be read as "safe."

## 2. Counts

| Stage | Count |
|---|---|
| Enum declarations | 1,485 |
| Struct/class declarations | 9,198 |
| Distinct variant names | 4,194 |
| Distinct struct/class names | 7,034 |
| **Collision names** (name is both) | **204** |
| **Candidate pairs** (enum.variant with colliding name) | **476** |
| **Real-risk pairs** (candidate + an actual bare `case Enum.Variant:` exists) | **36** |

## 3. Real-risk table (36 pairs, `main` branch)

`CASE` = file(s) containing `case Enum.Variant:`. `STRUCT` = colliding
struct/class declaration site(s) (`file:line:kind`).

| enum.variant | case-match file(s) | colliding struct/class file:line |
|---|---|---|
| ArtifactKind.Checkpoint | src/lib/common/experiment/artifact.spl | src/lib/nogc_sync_mut/test_runner/checkpoint.spl:13:struct |
| ArtifactKind.Dataset | src/lib/common/experiment/artifact.spl | src/lib/gc_async_mut/pure/data/dataset.spl:10:class |
| BinOp.Range | src/lib/gc_async_mut/pure/evaluator.spl | src/compiler/90.tools/query_types.spl:23; src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:26; src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/lsp/protocol.spl:33 (all struct/class Range) |
| BugStatus.Closed | src/lib/nogc_async_mut/mcp/bugdb_resource.spl | src/lib/common/types.spl:104:class |
| CircuitState.Closed | src/lib/{nogc_async_mut,nogc_sync_mut}/failsafe/circuit.spl | src/lib/common/types.spl:104:class |
| CpuException.Breakpoint | src/compiler/70.backend/interrupt.spl | 9 sites: dap/hooks.spl, dap/protocol.spl, debugger.spl, mcp/dap/mod.spl, debug.spl (both gc/nogc variants) |
| DriverClass.Block | src/lib/{nogc_async_mut,nogc_sync_mut}/driver/loader.spl | src/compiler/10.frontend/parser_types_expr.spl:441:struct; src/compiler/30.types/type_system/_StmtCheck/bindings_check.spl:27:struct |
| DriverClass.Gpu | src/lib/{nogc_async_mut,nogc_sync_mut}/driver/loader.spl | src/lib/common/gpu/device.spl:11:class |
| DriverError.IoError | src/lib/nogc_sync_mut/driver/error.spl | src/lib/common/io/types.spl:157:class; src/lib/nogc_sync_mut/src/infra.spl:28:struct |
| DriverError.NotSupported | src/lib/nogc_sync_mut/driver/error.spl | src/lib/common/ui/capability.spl:40:class |
| DType.Bool | src/lib/nogc_async_mut/df/{df_io,df_transform,mod}.spl; ndarray/{mod,ndarray_generators,ndarray_impl_ops}.spl; nogc_sync_mut/df/{df_io,df_transform,mod}.spl | src/lib/nogc_async_mut/ndarray/mod.spl:24:struct (same file as the enum + several case sites) |
| ErrorCategory.ParseError | src/lib/nogc_async_mut/mcp/error_handler.spl | src/compiler/10.frontend/treesitter_types.spl:353; src/compiler/85.mdsoc/feature/parsing/app/parse_error.spl:5; src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:84; src/lib/common/parser/parser.spl:13; src/lib/gc_async_mut/pure/parser.spl:14 |
| EventKind.Checkpoint | src/lib/nogc_sync_mut/replay/event_kinds.spl | src/lib/nogc_sync_mut/test_runner/checkpoint.spl:13:struct |
| EventKind.MemoryMap | src/lib/nogc_sync_mut/replay/event_kinds.spl | src/lib/{nogc_async_mut,nogc_sync_mut}/debug/remote/exec/types.spl:15:class |
| HeuristicOutlineKind.Export | src/compiler/10.frontend/treesitter/heuristic.spl | src/compiler/10.frontend/parser_types.spl:69:struct |
| HeuristicOutlineKind.Impl | src/compiler/10.frontend/treesitter/heuristic.spl | src/compiler/10.frontend/parser_types.spl:367:struct |
| HirTypeKind.Bool | src/compiler/20.hir/hir_lowering/async.spl; _Items/lowering_helpers.spl; 30.types/_TypeLayout/layout_core.spl; 50.mir/_MirLoweringExpr/method_calls_literals.spl; 50.mir/_MirLowering/function_lowering.spl | src/lib/nogc_async_mut/ndarray/mod.spl:24:struct |
| LeakCheckMode.Runtime | src/compiler/90.tools/leak_check/{main,types}.spl | src/lib/nogc_async_mut/async/runtime.spl:42:struct |
| MetaOp.Checkpoint | src/lib/nogc_sync_mut/db/dbfs_engine/meta_store.spl | src/lib/nogc_sync_mut/test_runner/checkpoint.spl:13:struct |
| MirTypeKind.Bool | 8 sites across 50.mir/*, 70.backend/backend/_MirToLlvm/*, 90.tools/async_integration.spl | src/lib/nogc_async_mut/ndarray/mod.spl:24:struct |
| ParserMode.Runtime | src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/cli/parser_loader.spl | src/lib/nogc_async_mut/async/runtime.spl:42:struct |
| PredicateKind.Range | src/lib/nogc_sync_mut/db/query_planner.spl | same `Range` cluster as BinOp.Range above |
| ProcessEventKind.Checkpoint | src/lib/nogc_sync_mut/replay/process/event_types.spl | src/lib/nogc_sync_mut/test_runner/checkpoint.spl:13:struct |
| ProcessEventKind.Signal | src/lib/nogc_sync_mut/replay/process/event_types.spl | src/lib/common/engine/signal/signal.spl:16:class |
| Provider.CpuBackend | src/lib/common/science_math/cuda_provider.spl | src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl:9; src/lib/skia/backend/cpu/backend.spl:114 |
| Provider.CudaBackend | src/lib/common/science_math/cuda_provider.spl | src/compiler/70.backend/backend/cuda_backend.spl:55; src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl:353 |
| QuerySymbolKind.EnumVariant | src/compiler/90.tools/query_api.spl | src/compiler/30.types/type_system/module_check.spl:24:struct |
| QuerySymbolKind.Field | src/compiler/90.tools/query_api.spl | src/compiler/20.hir/inference/types.spl:83:struct |
| QuerySymbolKind.Module | src/compiler/90.tools/query_api.spl | src/lib/common/parser/ast.spl:121; src/lib/gc_async_mut/pure/ast.spl:114 |
| QuerySymbolKind.Parameter | src/compiler/90.tools/query_api.spl | src/compiler/15.blocks/blocks/definition.spl:302:struct |
| QuerySymbolKind.Variable | src/compiler/90.tools/query_api.spl | src/compiler/90.tools/sffi_gen/specs/interpreter_hooks.spl:46; dap/hooks.spl:69 (both variants); dap/protocol.spl:164; mcp/dap/mod.spl:93 |
| ReplayTrack.ContainerCheckpoint | src/lib/nogc_sync_mut/replay/integration.spl | src/lib/nogc_sync_mut/replay/container/checkpoint_format.spl:94:struct |
| ReplayVerdict.Match | src/lib/nogc_sync_mut/replay/process/replayer.spl | src/lib/nogc_sync_mut/src/core/regex.spl:49:class |
| SemanticEventKind.OwnershipTransfer | src/lib/nogc_sync_mut/replay/semantic/trace_events.spl | src/compiler/99.loader/metadata_symbol_surface.spl:102:class |
| TypeDefault.Bool | src/compiler/20.hir/hir_lowering/types.spl | src/lib/nogc_async_mut/ndarray/mod.spl:24:struct |
| VmReplayMode.Snapshot | src/lib/nogc_sync_mut/replay/vm/vm_types.spl | src/lib/nogc_async_immut/versioned/__init__.spl:28; src/lib/nogc_sync_mut/game_net/wire.spl:72 |

Notable finding: `QuerySymbolKind` (src/compiler/90.tools/query_types.spl:28,
used by `query_api.spl`) is the **direct sibling of the fixed `SymbolKind`
bug** — it lives in the same query/LSP file family, has the same
"SymbolKind-shaped" variant set (Function/Method/Variable/Parameter/
Field/Class/Struct/Enum/EnumVariant/Trait/Module/Import), and the PTR1
rename incidentally fixed 5 of its variants (Class/Enum/Struct/Trait/Function
— because they collided with the *same* `parser_types.spl` structs that got
renamed) but **left 5 variants unfixed** (EnumVariant, Field, Module,
Parameter, Variable), which collide with unrelated structs elsewhere.

Also notable: `Checkpoint` is a single struct
(`src/lib/nogc_sync_mut/test_runner/checkpoint.spl:13`) colliding with **4
different enums** (`ArtifactKind`, `EventKind`, `ProcessEventKind`,
`MetaOp`) — one rename fixes 4 of the 36 pairs.

## 4. Empirical probe (required)

Target: `DType.Bool` vs. `struct Bool` — real code has both the enum and the
colliding struct in the **same file**,
`src/lib/nogc_async_mut/ndarray/mod.spl` (`struct Bool:` at line 24,
`enum DType:` at line 30, and `mod.spl` itself has a `case DType.Bool:` arm
at line 67), so this is the most faithful minimal-repro target available.

Probe file: `/tmp/claude-1000/enum1_probe.spl`
```
struct Bool:
    value: i32

enum DType:
    Bool
    Int32
    Float64

fn classify(d: DType) -> text:
    match d:
        case DType.Bool:
            return "MATCHED:DType.Bool"
        case DType.Int32:
            return "MATCHED:DType.Int32"
        case DType.Float64:
            return "MATCHED:DType.Float64"
        case _:
            return "FELL-THROUGH:no-arm-matched"

fn main():
    print("probe DType.Bool  -> {classify(DType.Bool)}")
    print("probe DType.Int32 -> {classify(DType.Int32)}")
    print("probe DType.Float64 -> {classify(DType.Float64)}")
```

Run:
```
env -u SIMPLE_TIMEOUT_SECONDS timeout 200 bin/simple run /tmp/claude-1000/enum1_probe.spl > /tmp/claude-1000/enum1.log 2>&1; echo "exit=$?"
```

Literal output (`exit=0`):
```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
probe DType.Bool  -> MATCHED:DType.Bool
probe DType.Int32 -> MATCHED:DType.Int32
probe DType.Float64 -> MATCHED:DType.Float64
```

**Negative result — the arm fires correctly.** Struct declared before the
enum (matching real file order) was also tried; same result. This is a
valid and valuable finding per the task brief: a same-file, 2-declaration,
15-line minimal repro of "enum variant name == struct name" is **not
sufficient** to reproduce the SymbolKind-class bug under the seed's
`bin/simple run`. The originally-fixed `SymbolKind` collision required (at
minimum) the full compiler build's global symbol/type registry — populated
by parsing hundreds of real compiler source files — to manifest; a synthetic
two-declaration script does not reach whatever registry-population or
resolution-order condition triggers the misdispatch. This means:
- The 36 real-risk pairs above are **not disproven** — they may still be
  live bugs when exercised via the actual compiler build/self-host path
  (which is what a minimal seed-run script cannot reproduce).
- But they are also **not confirmed** by this probe; each would need to be
  exercised in its real call context (e.g., actually running `simple test`
  over `nogc_async_mut/ndarray` or the LSP `query_api` path) to prove the
  arm is dead, which is out of scope for a census lane.
- The negative result narrows the "additional condition" search: it is NOT
  simply "same name, same file, no import layer" — something about scale,
  self-hosted stage, or specific registry population order (matching the
  `feedback_when_an_assumption_falls_reaudit_what_was_left` lesson) is also
  required. Recommend the next lane test `QuerySymbolKind` directly inside
  `query_api.spl`'s real build/test path, since it is the closest true
  sibling of the proven bug.

## 5. Prioritized remediation list (census only — no renames performed)

1. **QuerySymbolKind** (`src/compiler/90.tools/query_types.spl:28`) — rename
   `EnumVariant`/`Field`/`Module`/`Parameter`/`Variable`-colliding structs (or
   the enum variants) the same way PTR1 did for `SymbolKind`. Highest
   confidence: same file family, same bug precedent, 5 variants outstanding.
2. **`Checkpoint` cluster** — `ArtifactKind.Checkpoint`,
   `EventKind.Checkpoint`, `ProcessEventKind.Checkpoint`, `MetaOp.Checkpoint`
   all collide with one struct
   (`src/lib/nogc_sync_mut/test_runner/checkpoint.spl:13`). One rename
   (e.g. `TestCheckpoint`) clears 4 of 36 pairs; replay/checkpoint
   infrastructure is mission-critical-adjacent.
3. **Driver subsystem** — `DriverClass.Block`, `DriverClass.Gpu`,
   `DriverError.IoError`, `DriverError.NotSupported`; in-scope for the
   mission-critical hardening campaign (kernel/driver code), silent
   mis-dispatch here is a safety concern.
4. **`CpuException.Breakpoint`** (`src/compiler/70.backend/interrupt.spl`)
   vs. 9 different `Breakpoint` classes in the debugger/DAP subsystem —
   backend interrupt/exception dispatch silently misrouting is a compiler
   correctness risk.
5. **`HeuristicOutlineKind.Export` / `.Impl`**
   (`src/compiler/10.frontend/treesitter/heuristic.spl`) vs.
   `parser_types.spl:69` / `:367` — same file (`parser_types.spl`) already
   being edited for the PTR1 fix; natural follow-on cleanup (Field/TypeAlias
   were also explicitly deferred by PTR1's own commit message and should be
   grouped with this).

Not performed in this lane (per instructions): no struct/class renames, no
`git`/`jj` operations, no `src/` edits. Only the throwaway
`/tmp/claude-1000/enum1_probe.spl` was written.

## RK1 cross-reference (2026-08-01)

The root-cause site for this census's collision class, plus the refutation of
the "re-key by `runtime_name` is cheap" plan, is recorded in
`symbolkind_enum_match_fails_cross_module_discriminant_minus_one_2026-07-29.md`
§ "RK1 update (2026-08-01)". Summary: **three** MIR maps are bare-keyed
last-wins (`enum_variant_index`, `enum_variant_discriminants`, and
`enum_runtime_id_index` — the last was wrongly believed to be namespace-aware),
the interpreter's equivalent table is **first-wins**, and the reader answers a
miss with a silent `-1`. No `src/` change was made: the deployed binary exposes
no `test`/`lint`/`check` subcommand, so a change to enum lowering cannot be
verified at this tip.

**Correction (2026-08-01):** the RK1 section referenced above also carries a
same-day `RK1 CORRECTION` retracting two false existence claims (the
enumeration TSV and the `StyleMutation` rename **both do exist** at tip — they
were missed by surveying a stale sparse working copy instead of `git grep
<rev>`). The three-defective-maps root cause is unaffected and confirmed at
tip. Read the correction section, not the original, for the read-site counts.
