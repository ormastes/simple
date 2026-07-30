# Systematic pipeline diff: `run_file_jit` vs the whole-program native-build pipeline (2026-07-30)

Eight JIT-only defects were found this session one at a time, by hand, each
costing a full investigation. a894's shape analysis found two patterns: (1)
miscellaneous codegen bugs, and (2) **pipeline-completeness gaps**, where a
correct mechanism already exists in the whole-program (`native_project`)
pipeline and simply isn't called from `run_file_jit`'s single-file path.
Gap 8 (module-level `val` from a function call reads 0) is of this shape.

Rather than find gap 9 by bisection, this pass diffs `run_file_jit`
(`src/compiler_rust/driver/src/exec_core.rs:693-822`) against the
whole-program pipeline's per-file compile function,
`compile_file_to_object` (`src/compiler_rust/compiler/src/pipeline/
native_project/compiler.rs:317-...`), called from `NativeProjectBuilder::
build()` (`native_project/mod.rs:586-...`), stage by stage. Reading finds
candidate omissions far more cheaply than running into them.

## 1. Top-level `build()` stages — mostly deliberately inapplicable

`build()`'s own numbered comments give the skeleton: 0 (init thread pool),
1 (discover files), 2 (incremental cache setup), 3 (stage `.o` files), 4/4b
(read sources + build cross-module import map), 5 (compile dirty files —
calls `compile_file_to_object` per file, diffed in §2), 6/6b (cache objects
+ manifest), 7 (link or archive).

Stages 0, 2, 3, 6, 6b, 7 are build-system/object-file/linking concerns with
no analog for in-process JIT execution (there is no `.o` file, no cache, no
link step) — **deliberate, not gaps**. Stage 1 (discovery) and 4b (import
map) have a real analog: `run_file_jit` uses `load_module_with_imports`,
which merges the entry file and its transitive imports into one AST/HIR/MIR
compile unit, instead of compiling each file to a separate object and
linking. This different **compilation-unit granularity** (one merged
module vs. many separately-compiled-then-linked modules) is itself
deliberate and appropriate for single-process JIT — but it is also exactly
where a whole class of cross-module correctness guarantees the linker/
mangler provides could silently stop applying. §3's confirmed gap is
evidence this happened at least once.

## 2. Per-file `compile_file_to_object` stages — where the interesting differences are

| Stage in whole-program path | `run_file_jit` equivalent | Verdict | Reasoning |
|---|---|---|---|
| Bootstrap source rewrite (`apply_bootstrap_rewrite_for_target`) | none | Deliberate | Gated behind `SIMPLE_BOOTSTRAP=1`; not part of normal execution for either path |
| `strip_inactive_cfg_arch_globals` (source-text level, strips inactive `@cfg(<arch>)` **global** variants before parsing) | none — `run_file_jit` only calls `strip_inactive_cfg_arch_fns_for_host` (**function** variants, post-parse) | **Unconfirmed candidate — not verified this pass** | No global-variant stripping call exists anywhere in `run_file_jit`. If a program declares `@cfg(<arch>) val X = ...` variants, the whole-program path strips inactive ones at the text level before parse; `run_file_jit` has no equivalent, so behavior for such a program is unverified (could see multiple conflicting variants, or none). Not tested this pass for time; flagged for a follow-up repro |
| Parse, then `strip_inactive_cfg_arch_fns` (**function** variants, AST level, using `effective_target().arch`) | `strip_inactive_cfg_arch_fns_for_host` (AST level, using **host** arch) | **Deliberate** | JIT always executes on the host; using host arch instead of a possibly-cross-compiled target arch is correct for this path, not a gap |
| `wrap_entry_script_as_main` (wraps a bare top-level script with no `fn main()` into a synthetic `main`) | none — `run_file_jit`'s own `has_main` check falls back to `evaluate_module` (full interpreter) whenever no MIR `main` exists | **Deliberate, but a documented limitation worth naming explicitly**: a bare-script `.spl` file (no `fn main()`) is *never* JIT-compiled at all under `run_file_jit`, unconditionally 100% interpreted. Not silently wrong (correct answers, just never exercises JIT) but relevant context for anyone using this class of file as a JIT probe — it can't be one |
| `inject_freestanding_module_global_init` (only when `is_freestanding`, i.e. baremetal/SimpleOS targets) | none | **Deliberate** — confirmed by a894's own gap-8 attempt: wiring this freestanding-only pass into `run_file_jit` for the *hosted* case produced a segfault for `val` (the pass writes the global from a separate function, safe only for always-mutable freestanding storage, undefined for a `val` treated as an immutable constant in hosted lowering). The right hosted-side fix is inside `generate_module_init`/`__module_init` codegen (`codegen/common_backend.rs`), not this pass — this row is not itself a gap, but a documented wrong-fix trap |
| `pipeline.rewrite_hir_simd_loops(&mut hir)` | none | **Deliberate / low-risk** | Read the implementation (`pipeline/lowering.rs:700-709`): it returns immediately unless `simd_mode != SimdMode::Auto`, i.e. it is a no-op for ordinary programs under the default SIMD mode. Not pursued as a repro |
| `lower_to_mir_with_global_trait_impls(&hir, imports.trait_impls)` | plain `lower_to_mir(&hir_module)` (no trait impls) | **Genuine gap, confirmed by reading, narrow scope** | Read `with_global_trait_impls`'s only effect (`mir/lower/lowering_core.rs:1181-1188`): it seeds the **dependency-injection** container's trait→implementation registry (`self.dependency_graph.add_implementation`), consumed by `@inject`-decorated parameters/singleton resolution. `run_file_jit` never populates this, so cross-module `@inject` trait implementations are invisible to DI resolution under JIT for any multi-file program. Not empirically tested this pass (needs a DI-using multi-file repro) — flagged, not confirmed by running |
| `qualify_native_struct_layouts` / `qualify_enum_runtime_names` / mangling (`mangle.rs`) | none | **Deliberate in general, but see §3 — plausibly the root mechanism behind the confirmed gap** | These exist to prevent symbol collisions when many separately-compiled `.o` files are linked into one binary; a single merged-AST JIT compile shouldn't need object-file-level mangling in general. But §3's confirmed bug (a cross-module global import reading wrong) is exactly the shape you'd expect if some *other* piece of what mangling/qualification does — establishing that a global declared in file A and referenced via `use` in file B is the *same* storage location — doesn't have an equivalent in `run_file_jit`'s merged single-pass compile. This is the leading, well-reasoned hypothesis, not a proven root cause (the actual codegen path for cross-module global symbol resolution was not traced to a specific line) |
| Entry-file re-exported-`main` trampoline (`compiler.rs:501-522`, only fires when the entry file has no local `main` but re-exports one via `use`) | none found | **Unconfirmed candidate — not verified this pass** | Lower priority given time budget; flagged for a follow-up repro (`use other.{main}` with no local `main` in the entry file) |

## 3. Confirmed NEW genuine gap: cross-module global value import reads wrong under JIT

**PROVED by direct `simple run` reproduction, not inferred.** A plain
**literal**-initialized module-level global (`val HELPER_Y = 99`, no
function call — deliberately not gap 8's shape) declared in a **non-entry,
imported** file reads as an uninitialized/wrong value when accessed
**directly** across the module boundary via `use helper_mod.{HELPER_Y}`,
under the default (Cranelift JIT) engine — even though a function defined
in the **same file** as the global (`get_helper_y()`, called through the
import) sees the correct value.

Fixture: `test/fixtures/jit_differential/cross_module_global_import/`
(`helper_mod.spl` + `main_entry.spl`).

```simple
# helper_mod.spl
val HELPER_Y = 99

fn get_helper_y() -> i64:
    HELPER_Y
```
```simple
# main_entry.spl
use helper_mod.{get_helper_y, HELPER_Y}

fn main():
    print("Y_direct={HELPER_Y} Y_via_fn={get_helper_y()}")
```

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run main_entry.spl
Y_direct=99 Y_via_fn=99

$ SIMPLE_EXECUTION_MODE=jit bin/simple run main_entry.spl
Y_direct=<special:12> Y_via_fn=99

$ SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1 bin/simple run main_entry.spl
Y_direct=<special:12> Y_via_fn=99      # unchanged, exit 0 -- strict catches nothing
```

Reproduced 3/3 runs, plus once more under `SIMPLE_JIT_STRICT=1` (still
silent, exit 0) — matches the exact "no crash, nothing for strict mode to
catch" shape of every other gap in this family.

**`var` variant also affected, with a *different* wrong-value signature**
(tested per the coordinator's explicit caution that gap-8-shaped fixes can
behave differently for `val` vs `var`):

```simple
# helper_mod.spl
var HELPER_Z = 77
fn get_helper_z() -> i64: HELPER_Z
```
```
$ SIMPLE_EXECUTION_MODE=jit bin/simple run main_entry.spl
Z_direct=<value:0x4d> Z_via_fn=77
```

`0x4d` = 77 decimal — so for `var` the *bits* are the correct value but
displayed as a raw/untagged word (a distinct corruption shape from `val`'s
`<special:12>`, which looks like an uninitialized/nil sentinel rather than
the right bits misdisplayed). This asymmetry echoes a894's own caution
about `val` vs `var` behaving differently for this bug family, and is
recorded here rather than smoothed over — the two variants are likely
different symptoms of the same missing cross-module symbol-resolution step
(§2's mangling/qualification hypothesis), not proof of two independent
bugs, but that is not confirmed.

**Not fixed this pass** — per instruction, the enumeration is the
deliverable. This is not a minimal, self-contained fix: it plausibly
requires teaching `run_file_jit`'s single-compile-unit path some equivalent
of the whole-program path's cross-module global-symbol qualification, which
needs its own investigation into exactly what `qualify_native_struct_layouts`
guarantees that a single merged AST currently doesn't get for granted.

Added to the differential harness (`scripts/check/
check_jit_interpreter_differential.spl`, fixture `cross_module_global_import`,
`expected: "Y_direct=99 Y_via_fn=99"`, `known_good: "interpret"`) — this
converts the finding from a one-time repro into standing coverage: any
future run of the harness will re-report this as a "known JIT bug, still
present" line (or flag it if it silently starts passing, per the §3a
lesson from the companion cross-lane-contradiction investigation in
`jit_test_suite_blind_spot_2026-07-30.md` — a future "pass" here should be
treated with the same caution, not written up as fixed without
cross-checking).

## 4. Summary

| Finding | Status |
|---|---|
| Cross-module global value import (val + var) | **Confirmed genuine gap, repro'd, added to harness** |
| DI/`@inject` cross-module trait-impl registry (`lower_to_mir_with_global_trait_impls`) | Genuine gap by code reading, **not empirically repro'd this pass** (narrow scope: DI-framework users only) |
| Global `@cfg(<arch>)` variant stripping | **Unconfirmed candidate**, not repro'd this pass |
| Entry-file re-exported-`main` trampoline | **Unconfirmed candidate**, not repro'd this pass |
| Bare-script-to-`main` wrapping | Deliberate difference (documented limitation: such files never JIT at all, always correctly interpreted) |
| Freestanding module-global-init injection | Deliberate difference — confirmed wrong-fix trap by a894's own attempt (segfaults `val` in hosted lowering) |
| HIR SIMD-loop rewrite | Deliberate / no-op for default SIMD mode |
| Object cache / incremental / link / archive stages | Deliberate — no analog for in-process JIT |
| Cross-target vs. host arch fn-cfg stripping | Deliberate — JIT always runs on host |

Per instruction, none of these were fixed this pass beyond adding the one
confirmed gap to the differential harness as standing coverage. The ranked
list above, with reasoning per row (not just a verdict), is the deliverable.
