# Systematic pipeline diff: `run_file_jit` vs the whole-program native-build pipeline (2026-07-30)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

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

## 4. Summary (updated after §5 — all three "unconfirmed" rows resolved)

| Finding | Status |
|---|---|
| Cross-module global value import (val + var) | **Confirmed genuine gap (gap 9), repro'd, added to harness** |
| Global `@cfg(<arch>)` variant stripping | **Confirmed genuine gap (gap 10), repro'd, added to harness** — see §5.2 |
| DI/`@inject` cross-module trait-impl registry (`lower_to_mir_with_global_trait_impls`) | **DISMISSED — not a gap** — see §5.1 |
| Entry-file re-exported-`main` trampoline | **DISMISSED — not a gap** — see §5.3 |
| Bare-script-to-`main` wrapping | Deliberate difference (documented limitation: such files never JIT at all, always correctly interpreted) |
| Freestanding module-global-init injection | Deliberate difference — confirmed wrong-fix trap by a894's own attempt (segfaults `val` in hosted lowering) |
| HIR SIMD-loop rewrite | Deliberate / no-op for default SIMD mode |
| Object cache / incremental / link / archive stages | Deliberate — no analog for in-process JIT |
| Cross-target vs. host arch fn-cfg stripping | Deliberate — JIT always runs on host |

Two genuine, confirmed, repro'd gaps now stand in the differential harness
(§3, §5.2). Two candidates were dismissed with a shared, coherent
architectural reason (§5.1, §5.3). Gap 9's root cause was traced to a
specific line (§6) but not fixed — the fix needs an explicit architecture
decision, surfaced rather than attempted quietly, per instruction.

## 5. Follow-up pass: converting the three unconfirmed items to proved or dismissed

### 5.1 DI/`@inject` cross-module trait-impl registry — DISMISSED, not a gap

**Reframed by reading before testing.** `dependency_graph`/
`global_trait_impls` is not primarily a DI-resolution mechanism — its only
consumer is `find_trait_for_method_on_receiver` (`mir/lower/
lowering_core.rs:946-999`), which decides how to lower a trait-method call:
if the trait has **no recorded implementation anywhere**, the call lowers
to `DUCK_DISPATCH_UNSUPPORTED_SLOT`, and "codegen lowers the sentinel to a
named diagnostic + trap" — a **loud** failure by design (guarding a past
SIGSEGV, `jit_game2d_backend_method_dispatch_sigsegv_2026-07-02`), not a
silent one. This alone changes the expected shape from "silent and
structural" to "loud crash if triggered incorrectly" — worth correcting
before testing, not after.

More importantly, a comment at `lowering_core.rs:987-995` records that
feeding **project-wide** `trait_impls` into `dependency_graph` was tried
before and caused a real regression: a SimpleOS desktop framebuffer-init
triple-fault, because cross-module impls fed into `dependency_graph` made
statically-exact calls virtualize through a vtable that then faulted in a
freestanding kernel. That fix intentionally scoped `dependency_graph` to
**local, in-this-module** impls only for concrete-receiver calls.

**Empirical test, three files, two implementations, a genuinely polymorphic
`[Greeter]` array (no static devirtualization possible):**

```simple
# trait_defs.spl
trait Greeter:
    fn greet() -> text
# impl_a.spl / impl_b.spl (each imports trait_defs, defines its own struct + impl)
# main_entry.spl
use trait_defs.{Greeter}
use impl_a.{GreeterA}
use impl_b.{GreeterB}

fn greet_all(items: [Greeter]) -> text:
    var out = ""
    for g in items:
        out = out + g.greet() + ";"
    out

fn main():
    val items: [Greeter] = [GreeterA(msg: "x"), GreeterB(msg: "y")]
    print("result={greet_all(items)}")
```

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run main_entry.spl
result=A:x;B:y;
$ SIMPLE_EXECUTION_MODE=jit bin/simple run main_entry.spl
result=A:x;B:y;
```

Correct under both engines. **Why no equivalent is needed:** `run_file_jit`
merges the entry file and every transitive import into **one** HIR/MIR
compilation unit via `load_module_with_imports`, *before* lowering starts.
By the time `MirLowerer::lower_module` runs, there is no remaining file
boundary — every `impl Trait for Type` in the merged program is already
"local" to the one module being lowered, so `local_trait_impls` (the
per-module path, `lowering_core.rs:998`) already sees every impl regardless
of which source file it came from. The `global_trait_impls` side channel
exists specifically to bridge **separately-compiled units** in the
whole-program path (each file compiled to its own object, needing a
project-wide manifest to know about impls in *other* objects) — a bridge
`run_file_jit`'s single-merged-unit architecture doesn't need in the first
place. **Dismissed: not a gap, and the underlying mechanism has an
independent history of being actively dangerous to feed cross-module data
into for a different reason (the freestanding triple-fault).**

### 5.2 Global `@cfg(<arch>)` variant stripping — CONFIRMED genuine gap (gap 10)

**PROVED by direct `simple run` reproduction.**

```simple
@cfg(x86_64)
val PLATFORM_ID = 64

@cfg(riscv64)
val PLATFORM_ID = 32

fn main():
    print("PLATFORM_ID={PLATFORM_ID}")
```

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run probe.spl   # host is x86_64
PLATFORM_ID=64
$ SIMPLE_EXECUTION_MODE=jit bin/simple run probe.spl
PLATFORM_ID=8
$ SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1 bin/simple run probe.spl
PLATFORM_ID=8                                                 # unchanged, exit 0
```

Reproduced 3/3 runs. `PLATFORM_ID=8` is neither variant's literal value (not
64, not 32) — both `@cfg` blocks reach the parser unstripped under
`run_file_jit` (there is no call anywhere in `run_file_jit` analogous to
`strip_inactive_cfg_arch_globals`, `native_project/compiler.rs:355`, which
runs on the raw source text *before* parsing in the whole-program path) and
the two same-named top-level `val PLATFORM_ID` declarations collide in a
way that produces a third, wrong value rather than a parse error or either
literal. `var PLATFORM_ID` tested too (per the gap-9 val/var caution) —
same wrong value (`8`) for both, no val/var asymmetry observed here (unlike
gap 9). Not root-caused further (which exact collision path in the parser/
lowerer produces `8` specifically) — the observed behavior is enough to
confirm the gap and pin a regression fixture; root-causing the precise
collision mechanism is follow-up work, not required to confirm the gap
exists.

Added to the differential harness: fixture `cfg_arch_global_variants`,
`expected: "PLATFORM_ID=64"`, `known_good: "interpret"`.

### 5.3 Entry-file re-exported-`main` trampoline — DISMISSED, not a gap

**Empirical test:**

```simple
# real_main_mod.spl
fn main():
    print("ran-from-reexported-main")
# entry.spl (no local main)
use real_main_mod.{main}
```

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run entry.spl
ran-from-reexported-main
$ SIMPLE_EXECUTION_MODE=jit bin/simple run entry.spl
ran-from-reexported-main
```

Correct under both engines, exit 0. **Same underlying reason as §5.1:** the
whole-program path's trampoline exists to bridge the entry file's own
separately-compiled object (which has no local `main` symbol) to the
resolved **mangled** name of the re-exported `main` in another object, at
link time. `run_file_jit` never splits into separate objects — the merged
AST already contains exactly one function literally named `main` (from the
imported file), so `has_main` finds it directly with no trampoline needed.
**Dismissed: not a gap, same "single merged compilation unit doesn't need
the whole-program path's cross-object bridging" reason as §5.1.**

**Pattern worth naming:** two of the three unconfirmed candidates turned
out to be dismissable for the *same* architectural reason. `run_file_jit`'s
choice to merge all files into one compilation unit before lowering
(rather than compiling per-file and linking) makes an entire class of
whole-program-path mechanisms (mangling for symbol collision avoidance,
project-wide trait-impl registries, main-symbol trampolines) unnecessary by
construction — the merge already did that work. The one candidate that
*did* reproduce (global `@cfg` stripping) is not in that class: it is a
source-level, pre-parse concern orthogonal to compilation-unit granularity,
which is exactly why merging files later doesn't paper over it.

## 6. Gap 9 root-cause investigation (per instruction: prove or refute the hypothesis before fixing)

**Traced to a specific line, not fixed — surfaced as an architecture
question rather than patched quietly, per instruction.**

`common_backend.rs:1531`:
```rust
let is_jit_module = std::any::type_name::<M>().contains("JITModule");  // :1410
...
let is_local = is_jit_module || local_globals.contains(name);          // :1531
```

`is_jit_module` is true for every Cranelift-JIT compile unconditionally
(confirmed: it's a generic-type-name check against the module type
parameter, not gated on anything file-specific). So for **every** global,
under JIT, `is_local` is forced `true` regardless of whether
`local_globals` (the whole-program path's per-file "is this global actually
defined in the file I'm compiling" set) would say otherwise. This routes
every global reference — both the real definition in `helper_mod.spl` and
the imported reference in `main_entry.spl` — through the same branch
(`common_backend.rs:1575-1589`, "Local global: define with Preemptible
linkage"), which calls `self.module.declare_data(&local_symbol, ...)` and
separately populates the data's contents from `global_init_values.get(name)`
if present for *that lowering context*.

**The plausible mechanism (traced, not proof-of-fix-tested):** if HIR
lowering for `main_entry.spl` records `HELPER_Y` as an imported reference
without carrying its literal initializer into *that file's own*
`global_init_values` map (only `helper_mod.spl`'s own lowering context
knows the literal `99`), then two `declare_data` calls for the **same
mangled name** happen across the merged compile — one with a real
initializer, one without — and whichever the Cranelift JIT backend's
finalization treats as canonical for that symbol determines whether reads
see `99` or garbage. This is consistent with every observation: the
function-mediated read (`get_helper_y()`, compiled as part of
`helper_mod.spl`'s own context, which has the real initializer) is correct;
the direct read from the importing file (which may have declared the same
symbol without an initializer) is not.

**Why this was not fixed this pass.** The `is_jit_module` bypass at line
1531 was clearly an intentional, load-bearing design choice — JIT has no
object-file-level "Import" linkage to resolve against (there's no separate
`.o` for the imported module to link), so treating everything as locally
defined is the *only* option available in the current architecture, not an
oversight to simply flip. A real fix needs one canonical `declare_data`
call per global name across the whole merged unit — i.e. genuine cross-file
global identity within a single compilation pass, deduplicating multiple
lowering contexts' declarations of "the same" global into one. That is
**not** "just call the existing mangling pass" (a894's gap-8 lesson
applies again: the existing whole-program mechanisms are built for a
different architecture — multiple compiled objects — and don't transplant
cleanly). It is closer to a new pass specific to the merged-single-unit
case: something has to walk the merged MIR and unify every declaration of
a given global name to a single `declare_data`/init-value pair before
codegen runs, keyed by name across all merged files' lowering output, which
does not exist today.

**Per instruction: this is surfaced as an architecture decision, not
attempted as a patch.** The two candidate directions (deduplicate at
`declare_data` call time by checking `global_ids` before re-declaring
with different init-value provenance; or build an explicit cross-file
global-identity resolution pass ahead of codegen, mirroring what
`qualify_native_struct_layouts` does for the whole-program path but scoped
to the single-merged-unit case) both touch the JIT codegen's global
declaration path broadly enough that either deserves its own scoped
investigation and review, not a same-pass patch bolted onto an enumeration
pass. Gap 9 remains open, confirmed, and pinned in the differential harness
(§3).

## 7. Attempting to fix gap 10 — premise checked and found FALSE; deeper, more general defect found underneath (not fixed)

**Instruction was: fix gap 10 by reusing the whole-program path's existing
`@cfg` stripping, checking first whether it's callable from `run_file_jit`'s
position in the pipeline.** That check came back "yes, callable, and
already called" — which made the fix a non-starter for a different reason
than expected.

### 7.1 The stripping call already exists in `run_file_jit`'s path

`module_loader.rs:1655`, inside `load_module_with_imports_internal` (called,
recursively, by `run_file_jit`'s `load_module_with_imports` for the entry
file and every transitive import):

```rust
source = crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(&source, target_arch);
```

`target_arch` here is threaded from `load_module_with_imports_for_target`,
which the plain `load_module_with_imports` wrapper (what `run_file_jit`
calls) hardcodes to `TargetArch::host()`. The `cfg_strip` module's own
top-of-file doc comment confirms this is intentional, existing, shared
wiring: *"`bin/simple run` JIT + interpreter paths (driver `exec_core.rs`)
... strip against the HOST arch, since interpreted/JIT code always executes
on the host."* This directly answers the "check first" instruction: the
strip does **not** need to be invoked from a new call site — it already
runs at the right stage, before parsing, for both engines equally.

### 7.2 So gap 10's fixture still failed after confirming the call runs — the wrong value is not caused by `@cfg`

Hand-traced `strip_inactive_cfg_arch_globals`'s algorithm against
`cfg_arch_global_variants.spl`'s exact source and confirmed by hand that it
should (and, per the code, does) blank out the inactive `@cfg(riscv64)`
block entirely, leaving exactly one surviving `val PLATFORM_ID = 64`. To
verify empirically rather than trust the trace: built the hand-stripped
output myself (same blank-line structure the function would produce, zero
`@cfg` lines) and ran it directly:

```
$ SIMPLE_EXECUTION_MODE=jit bin/simple run hand_stripped.spl   # no @cfg at all, one `val PLATFORM_ID = 64`
PLATFORM_ID=8
```

**Identical wrong value to the un-stripped original.** This proves the
`@cfg` machinery is not the cause — a program with no `@cfg` construct
anywhere produces the exact same corruption.

### 7.3 Root cause is far more general: module-level globals are never tag-boxed before reaching `print`/formatting

Isolated with a two-line program, no `@cfg`, no imports, no functions
beyond `main`:

```simple
val X = 100

fn main():
    print(X)
```

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run x.spl
100
$ SIMPLE_EXECUTION_MODE=jit bin/simple run x.spl
<value:0x64>
```

Confirmed on the real deployed `bin/simple`, not just a candidate build.
Further isolation:

- `val X = 64` (instead of 100) prints `8` under JIT — `64 >> 3 == 8`, the
  same untagging shift seen in `list.get` returning `value << 3`
  (`reference-list-get-returns-value-shifted-left-3`), but in the opposite
  direction and triggered differently: here a **raw, never-tagged** value
  whose low 3 bits happen to be `000` gets misread by print's tag-dispatch
  as *already* a tagged small-int and incorrectly un-shifted.
- `val X = 100` (binary low bits `100`, not `000`) doesn't match that
  false-positive tag pattern, so print instead falls through to a raw debug
  format, `<value:0x64>` — the correct bits (100 = 0x64), just displayed
  as an unboxed word rather than a decimal int.
- A **local** `val x = 100` inside `main` prints correctly (`100`) — this
  is specific to **module-level** globals.
- Copying the global to a local first (`val y = X; print(y)`) does **not**
  fix it — `y` still prints `<value:0x64>`. The corruption travels with the
  raw value itself, not with "how directly" it's read.
- `SIMPLE_JIT_STRICT=1` is silent — same "nothing to catch" shape as every
  other gap in this family.

**This generalizes gap 9, and narrows its own framing to the wrong axis.**
Gap 9 was filed as "cross-module global value import reads wrong" because
the repro that found it happened to combine two things: a direct reference
to a global, and that reference crossing a file boundary. §7.3's finding
shows the file boundary was never the relevant variable — a **direct**
reference to a module-level global is wrong whether or not it crosses a
file boundary; what actually differed in gap 9's own repro was that
`get_helper_y()` returned the value through a **function call**, and a
function's return value convention evidently re-boxes/re-tags it correctly,
masking the defect for that one path. Gap 9's fixture and doc description
remain accurate as written (both are still true, confirmed facts) but
should be read as **one instance** of this broader defect, not a
cross-module-specific one.

### 7.4 Not fixed — this is a deeper defect than the one that was assigned

The instruction was to fix "the one genuinely contained item" — reuse an
existing, working stripping pass for a call-site gap. That gap turned out
not to exist: the call site is already correct. What's actually broken is
JIT codegen's tag-boxing of module-level global reads reaching a
print/format sink — a **codegen** defect, not a **pipeline-completeness**
defect, and outside the shape this whole sweep has been enumerating (a
missing call to an existing pass). Fixing it is not a small, self-contained
change on the order of "call this one more function"; it needs its own
investigation into where JIT-compiled global loads are supposed to be
tag-boxed and currently aren't (or aren't consistently across all four
observed call shapes: direct print, direct arithmetic-then-print, local-var
copy, and the gap-9 cross-module case) — surfaced here rather than
attempted, per the same standard applied to gap 9 in §6.

**Added to the harness** as its own fixture,
`module_global_direct_read_untagged` (`expected: "X=100"`), the cleanest,
most general repro found this pass — no `@cfg`, no cross-module import,
two lines of actual logic. `cfg_arch_global_variants.spl`'s own header
comment was corrected in place to record that its originally-filed cause
was checked and found false, and to point at this fixture as the real
explanation, rather than silently leaving a wrong diagnosis standing next
to a fixture that still (correctly) fails.

## 8. Updated summary

| Finding | Status |
|---|---|
| Cross-module global value import (val + var) — gap 9 | Confirmed, open; reframed by §7.3 as one instance of a more general defect, not cross-module-specific |
| Module-level global direct read never tag-boxed before print/format | **Root cause of both gap 9 and the original "gap 10" observation** — confirmed, open, not fixed (§7.3-7.4) |
| Global `@cfg(<arch>)` variant stripping | **DISMISSED as a distinct defect** — the stripping call already runs correctly in `run_file_jit`'s pipeline (§7.1); `cfg_arch_global_variants.spl`'s wrong value is the tag-boxing defect above, not a stripping gap |
| DI/`@inject` cross-module trait-impl registry | Dismissed — not a gap (§5.1) |
| Entry-file re-exported-`main` trampoline | Dismissed — not a gap (§5.3) |

No fix landed this pass. The differential harness now has 5 standing
fixtures (4 confirmed-open bugs + 1 correctness sentinel); all four
pre-existing fixtures were re-verified unaffected by this pass's edits
(only fixture/doc/comment changes were made — no source code was touched).
Reverse-control non-vacuity re-confirmed after every edit in this pass
(corrupt sentinel → exit 1; restore → exit 0).

## 9. Unification: gaps 8, 9, and 10 are ONE defect, bit-exact confirmation

**Result: full unification, not partial.** Per instruction, checked whether
the wrong value in each gap's original repro is arithmetically consistent
with an untagged (raw) read of the correct value misinterpreted through the
runtime's tagged-`RuntimeValue` dispatch — and whether the same theory
explains every case that *passed* in the earlier investigations, not just
the failures. It does, for all three, including gap 8 — the one flagged as
least likely to reduce.

### 9.1 The tag scheme, reconstructed empirically from five independent raw values

A properly boxed `RuntimeValue`'s low 3 bits are a type tag; a correctly
tagged small int is `(n << 3) | 0`. A **module-level global's raw,
never-boxed value** has whatever low 3 bits its own bit pattern happens to
have — and print/format code that assumes every value it receives is
properly tagged decodes those bits as if they *were* a tag, giving a
result that depends entirely on the raw value's low 3 bits:

| Raw value | Low 3 bits | Tag read as | Observed output | Consistent? |
|---|---|---|---|---|
| `64` (gap 10) | `000` | INT — unbox via `>>3` | `8` (`64>>3`) | Yes — exact arithmetic match |
| `100` (gap 10 / §7.3) | `100` | unrecognized — raw dump | `<value:0x64>` (0x64 = 100) | Yes — exact hex match |
| `99` (gap 9, `val`) | `011` | SPECIAL — payload `>>3` | `<special:12>` (`99>>3=12`) | Yes — exact arithmetic match |
| `77` (gap 9, `var`) | `101` | unrecognized — raw dump | `<value:0x4d>` (0x4d = 77) | Yes — exact hex match |
| `42` (literal control, this pass) | `010` | FLOAT — reinterpret bits as f64 | denormalized near-zero float, huge leading-zero string | Yes — matches the "raw int bits reinterpreted as float64" prediction; this is a NEW confirmation, not previously catalogued as its own gap, and is the same defect, not a sixth one |
| `9` (this pass, direct probe) | `001` | HEAP pointer — dereference `raw>>3` as an address | `<invalid-heap:0x9>` — **the runtime's own diagnostic message confirms the tag reconstruction directly**, not just consistency with it | Yes — definitional |

Five independently-chosen raw values (64, 100, 99, 77, 42) plus one
diagnostic probe (9) all land exactly where the reconstructed tag table
predicts, with no free parameters left to explain any of them after the
first two fixed the INT and SPECIAL tags. This is the "arithmetic works
out" bar the instruction asked for, met for every case, not just the
convenient ones.

### 9.2 Gap 8 reduces too — the piece assumed hardest fits once decomposed correctly

Gap 8's repro (`val X = get_value()`, `get_value()` returns `42`) prints
`X=0` and, initially, looked like it broke the pattern: `0` is not an
"arithmetic transform of `42`" under the tag table above (`42`'s own tag
is FLOAT, not INT, so a correctly-stored `42` would print as a garbled
float, matching §9.1's new confirmation — not `0`). The resolution is that
**the stored raw value is not 42 at all** — gap 8's write side (a
function-call initializer) never runs, so the slot holds its default
zeroed memory, raw `0`. That `0` is a *second*, independent instance of the
*same* read-side defect, not a special case:

- `print("X={X}")` / `print(X)`: raw `0`, tag `000` (INT), unbox `0>>3=0`
  → **`0`**. Matches.
- `X == 0`: true (raw-bit equality, unaffected by tag confusion since `0`
  is a fixed point either way). Matches — this is why the "is it truly
  zero" check doesn't itself distinguish the two hypotheses; it needed the
  next test.
- `X == nil`: **false** — ruled out the competing hypothesis that the slot
  holds the nil sentinel (raw `3`) rather than genuine `0`.
- `X * 2`: `0` — consistent with raw arithmetic on a true `0`.
- `val y = X + 1; print(y)`: **`nil`**, not `1`. This is the result that
  looked hardest to explain, and is what confirmed the raw-`0` hypothesis
  precisely: arithmetic on `X` itself is not tag-confused (`0 + 1` computes
  the correct raw `1`), but the **result** `y` is *also* an unboxed raw
  value with no tag applied before it flows into `print`. `1`'s low 3 bits
  are `001` — the HEAP-pointer tag, per §9.1's table. `1 >> 3 = 0`, a null
  address. The formatter's null-heap-pointer case resolves to `nil` rather
  than crashing or reporting `<invalid-heap:0x0>` — exactly the observed
  output.

Every one of gap 8's four independently-checked behaviors (`print`,
`==0`, `==nil`, `X+1` then `print`) is explained by exactly the same
read-side tag-dispatch-on-raw-bits mechanism as gaps 9 and 10, applied to
`0` instead of `42`, `64`, `99`, `77`, or `100`. No separate read-side
mechanism is needed for gap 8.

### 9.3 What does NOT unify: gap 8 has an extra, distinct write-side defect

Gap 8 is not *purely* the same bug as 9 and 10. There is a second,
independent defect specific to gap 8: the function-call initializer for a
module-level global apparently never executes (or its result never
reaches the global's storage slot), leaving the slot at its default `0`
rather than the computed `42`. This write-side defect is **not** present
in gaps 9 or 10 — both of those had the *correct* value sitting in the
global's slot (confirmed: `HELPER_Y`'s slot genuinely holds `99`, since a
function call that reads it via a proper return, `get_helper_y()`, reports
`99` correctly; `PLATFORM_ID`/`X`'s literal-initialized slots equally hold
their true literal values, per §9.1's exact arithmetic matches). Gap 8
therefore has **two** defects layered together: (a) the universal
read-side tag-dispatch-on-raw-global-value defect shared with 9 and 10,
and (b) a distinct, gap-8-only write-side defect where a function-call
initializer's result never lands in the slot at all.

This second point was not independently traced to a codegen line this
pass (that would start to be fix work, out of scope here) — it is
established only by exclusion (the raw value present is definitively `0`,
not `42`, and not the nil sentinel `3`), which is sufficient to establish
that a write-side failure exists without characterizing its mechanism.

### 9.4 The "passing" cases also unify — function-call *return* boundaries re-box

The instruction asked whether the same theory explains what worked, not
just what failed. It does, consistently:

- Gap 9's `get_helper_y()` (a function returning the global's value)
  prints correctly. A local, non-global `val`/`var` also always prints
  correctly (used throughout this session's other fixtures without
  incident). Both cross a **function call boundary or a fresh
  local-value-construction path** before reaching print — and both are
  observed correct. The unifying claim is: JIT-compiled function
  **returns**, and freshly-computed **local** values, get properly
  tag-boxed as part of their own codegen; a **direct module-level global
  load** does not, and nothing re-boxes it afterward, no matter how many
  local variables or arithmetic operations it subsequently passes through
  (§7.3's `val y = X; print(y)` control: still wrong, because copying to a
  local does not itself insert a box step — only a function's return
  convention, or presumably genuinely fresh local computation, does).
- Gap 8's own local-`val`-with-a-function-call-initializer case working
  correctly (from the original memory note) is consistent with this too:
  a **local** variable initialized by a function call receives the
  function's properly-boxed return value directly, with no module-global
  storage in between to strip the tag.

### 9.5 One remaining discrepancy worth recording plainly

Gap 8's own original memory note states "a module-level `val` initialized
by a **literal** → correct." §7.3 and §9.1 directly contradict this for
the general case: a module-level literal-initialized global
(`val X = 100`, `val X = 42`, `val X = 64` — none function-call
initializers) reads **wrong** under JIT when printed directly, for every
value tested this pass. The most likely reconciliation: gap 8's original
"literal is correct" check used a value whose raw bits coincidentally
survive the read-side misinterpretation unchanged or unnoticed (e.g. a
literal `0`, where `0 >> 3 = 0` is a fixed point and the wrong-mechanism
output happens to equal the right answer), or checked a different
consumption shape than a direct `print` in `main`. This is not resolved
here — it is exactly the kind of thing a coincidentally-passing control
can hide, and is flagged rather than assumed away.

## 10. Consequences for the bug tracker, memory notes, and the harness

**One defect, several presentations — not three independent bugs.** The
canonical description going forward: *a module-level `val`/`var` global's
value, once loaded from its storage slot, is never converted into a
tag-boxed `RuntimeValue` before flowing into a consumer that expects one
(print/format, and any further computation whose result is itself printed
without crossing a function-return or fresh-local-construction boundary).
The specific wrong output is fully determined by the raw value's low 3
bits against the runtime's own type-tag encoding (§9.1's table). Gap 8
additionally has a second, independent, write-side defect (function-call
initializers for module-level globals don't store their result), which
determines that gap 8's raw starting value is `0` rather than the intended
result — after which the same universal read-side defect applies.*

- `doc/08_tracking/bug/jit_drawirrendertarget_moduleresolver_gap_2026-07-30.md`
  (gap 8's original filing, not owned by this doc/pass) should be
  cross-referenced from here rather than restated; its "literal is
  correct" claim should be re-checked against §9.5 before being relied on
  again.
- Memory notes `reference_jit_module_level_val_from_function_call_reads_zero.md`
  (gap 8), `reference_jit_module_level_val_from_function_call_reads_zero`'s
  sibling for gap 9 (cross-module framing), and any note describing gap 10
  should be updated to point at this section as the unified explanation,
  rather than being treated as three separately-rooted defects. (This
  agent cannot edit user-level session memory files directly; flagging
  here for the operator/coordinator to fold in.)
- **Not to be conflated**: `reference-list-get-returns-value-shifted-left-3`
  (`xs.get(i)` returns `value << 3`, a *left*-shift/over-boxing defect on
  reads through a specific method) is the **opposite direction** of this
  defect (`>>3`/under-boxing on direct global reads) and a different
  mechanism. Keep separate.

### Harness fixtures — kept distinct, relabeled as manifestations

Per instruction, the existing fixtures are **not** collapsed into one file
(each remains an independent regression case — losing gap 9's
cross-module shape or gap 10's `@cfg` shape would lose real coverage, even
though the underlying cause is now understood to be one thing), but their
labels/comments are corrected to say so explicitly:

- `cross_module_global_import` (gap 9) — comment updated to reference this
  section as the unifying explanation instead of standing alone.
- `cfg_arch_global_variants` — already corrected in §7 to point at
  `module_global_direct_read_untagged`; that pointer now additionally
  resolves to this section's fuller unification.
- `module_global_direct_read_untagged` — the cleanest, most general
  instance of the shared read-side defect; comment updated to state this
  explicitly and cross-reference §9.
- Gap 8's `fn`-call-initializer shape is not yet in the differential
  harness as its own fixture (the earlier passes that found it predate
  this harness). Adding it is a natural follow-up so all three
  manifestations are standing regression coverage, not just two of three
  — noted, not done this pass to stay within "establish the unification,
  don't fix or over-expand" scope.

No fix attempted this pass, per instruction. The fix question is now
single and well-posed: **where should a module-level global's raw value
get tag-boxed on read under JIT, and why doesn't it currently** — a
distinct, likely larger question from gap 8's separate write-side "why
doesn't the function-call initializer's result reach the slot" question.
Both are architecture/codegen questions for a dedicated pass, not this
enumeration-and-now-unification one.

## 11. Read-side defect fixed — closes gaps 9 and 10 (and one manifestation of the shared mechanism)

**Scope, per instruction: read side only.** Gap 8's write-side defect
(function-call initializers never reaching the global's storage slot) is
untouched. Gap 8's own fixture
(`module_global_from_fn_call_reads_zero.spl`) is expected to, and does,
remain failing after this fix — it is a different mechanism, and mixing
the two would muddy both the fix and its verification, exactly as
instructed.

### 11.1 Premise checked first — and found wrong on the first attempt, then re-verified

The instruction was to check whether a boxing step exists and simply
isn't called before building on that premise — the same discipline that
caught the false `@cfg` diagnosis in §7. That discipline caught a real
mistake here too, not just confirmed a correct guess:

**First hypothesis (wrong):** `box_arg_for_any_param` (`mir/lower/
lowering_expr_call.rs`) only inserts `MirInst::BoxInt` for an `ANY`-typed
call argument when the HIR node is itself a literal `HirExprKind::Integer`
— missing the case of a `Global` reference whose static type happens to be
`ANY`. This looked promising and led to an initial fix in
`hir/lower/module_lowering/module_pass.rs`'s `Node::Static` arm (inferring
a concrete type from a const-evaluable initializer, mirroring the
already-fixed `Node::Const` arm in the same file, which has its own
comment citing an identical prior bug, `stage4_imported_const_compare`).

**That fix did not change the fixtures' behavior at all.** Rather than
conclude the theory was merely incomplete, this was checked directly:
`print("X={X}")`/`print(X)` do **not** go through `box_arg_for_any_param`
at all — string interpolation and `print` desugar during **HIR** lowering
into `HirExprKind::BuiltinCall { name: "rt_value_to_string", .. }`
(`hir/lower/expr/literals.rs`), a completely different code path from
regular function calls. `box_arg_for_any_param` was never the relevant
mechanism for this bug.

**Instrumented directly rather than continuing to theorize.** Added a
temporary, env-var-gated `eprintln!` at the real boxing site
(`mir/lower/lowering_expr_builtin.rs`'s dedicated `rt_value_to_string`
handling, which already boxes based on `arg.ty` matching a concrete
int/float/bool type — a boxing step that DOES exist and IS called, unlike
the first hypothesis) and at the edited `Node::Static` arm. Ran a fixture
with the instrumented binary: the `rt_value_to_string` print fired
(`arg.ty=TypeId(14)` = `ANY`, confirming the argument really does reach
this call still typed `ANY`), but the `Node::Static` print **never
fired at all**. The edited code path was not being executed for this test
case — the first fix targeted a real bug in a real function, but not the
one causing this symptom.

**Re-checked the parser, not just the lowering, to find the actual site.**
`val`/`var` at module scope parse to `Node::Let` (`parser/src/
stmt_parsing/var_decl.rs`'s `parse_val`/`parse_var`, calling the shared
`parse_let_impl`), not `Node::Static` — `Node::Static` is Simple's
separate, rarely-used explicit `static` keyword. `module_pass.rs` has a
**second**, independent type-inference site for `Node::Let` specifically
when it appears as a module-level item ("Register module-level variable
(var at module scope = global)"), and *that* site had exactly the same
missing-inference gap the `Node::Const`/`Node::Static` sites already had
fixed — but had never received the analogous fix.

### 11.2 The fix

`hir/lower/module_lowering/module_pass.rs`, the `Node::Let(l)` arm's type
resolution (the actual site controlling a module-level `val`/`var`'s
`self.globals` entry):

```rust
let ty = if let Some(ref t) = l.ty {
    self.resolve_type(t).unwrap_or(TypeId::ANY)
} else if let Some(ref t) = extract_pattern_type(&l.pattern) {
    self.resolve_type(t).unwrap_or(TypeId::ANY)
} else if l.value.as_ref().and_then(try_const_eval).is_some() {
    TypeId::I64
} else if matches!(&l.value, Some(Expr::String(_)) | Some(Expr::FString { .. })) {
    TypeId::STRING
} else {
    TypeId::ANY
};
```

The two new branches are copied from the pattern already established (and
already working) for `Node::Const` and the explicit `Node::Static`
keyword: infer `I64` for a const-evaluable initializer (reusing the
existing `try_const_eval`, the same evaluator those arms already call),
`STRING` for a string/fstring literal, otherwise still `ANY`. No new
boxing mechanism was written — the boxing step in `rt_value_to_string`'s
handling already correctly boxes any argument whose static type is a
concrete int/float/bool; the bug was purely that a module-level `val`/
`var`'s type never got resolved to one, so that already-correct boxing
code never triggered. This is squarely a "the mechanism exists, the call
site's input was wrong" fix, matching the shape this whole sweep has been
finding — the surprise was which mechanism, not that one existed.

The earlier (harmless, and independently correct) `Node::Static` change
was kept — it fixes the same class of gap for the explicit `static`
keyword construct, a distinct, real, if rare, path — with its comment
corrected to point at the `Node::Let` arm as the fix for `val`/`var`
specifically. The temporary debug instrumentation was removed before
landing.

### 11.3 Architecture check: independent of gap 9's unpatchable mechanism, as hoped

Per instruction: if the fix needed the same cross-file global-identity
machinery gap 9's own write-side turned out to need, that would have been
surfaced rather than attempted. It doesn't. This fix is a **pure, local,
per-file HIR-lowering type-inference change** — it decides the static
`TypeId` recorded for a name in `self.globals` while lowering ONE module
(which, for `run_file_jit`, is the single merged AST covering the entry
file and every transitive import — see §6's discussion of that merge).
It does not touch `declare_data`, Cranelift symbol linkage, or any notion
of "is this global's storage the same object across two separately-
compiled units" — the question §6 left as an open architecture decision
for gap 9's *own*, separate, still-unfixed defect (multiple `declare_data`
calls for the same global name colliding). This fix and that open
question are unrelated: this fix makes the *type* of a global correct
before codegen ever runs; §6's open question is about codegen's *symbol
identity* for globals once their MIR is already correct. Confirmed by the
fix landing cleanly with a small, self-contained diff and no interaction
with the codegen files §6 discusses.

### 11.4 Non-vacuous proof — before/after, via `simple run`, all six fixtures plus reverse control

Built two binaries from this pass's own worktree (before: `Node::Let`
arm unmodified; after: the fix in §11.2 applied), ran every harness
fixture directly via `simple run` under both engines against each:

| Fixture | Before (JIT) | After (JIT) |
|---|---|---|
| `chained_to_i64_twice` | `pw=480 ph=360` (contested, unaffected) | `pw=480 ph=360` (unaffected) |
| `module_level_val_from_call` | `X=0` (gap 8, write-side) | `X=0` (unchanged, correctly untouched) |
| `struct_field_compound_assign` | `n=2` (unrelated bug) | `n=2` (unaffected) |
| `list_get_shifted` | `idx=5 get=5` (contested, unaffected) | `idx=5 get=5` (unaffected) |
| `sentinel_basic_arithmetic` | `sum=30` (already correct) | `sum=30` (unaffected) |
| `cross_module_global_import` | `Y_direct=<special:12> Y_via_fn=99` | **`Y_direct=99 Y_via_fn=99`** |
| `cfg_arch_global_variants` | `PLATFORM_ID=8` | **`PLATFORM_ID=64`** |
| `module_global_direct_read_untagged` | `X=<value:0x64>` | **`X=100`** |
| `module_global_from_fn_call_reads_zero` | `X=0` (gap 8, write-side) | `X=0` (unchanged, correctly untouched) |

Interpreter-mode output re-checked unaffected for every fixture (the
interpreter does not go through this HIR→MIR→Cranelift path at all).
Full harness run against the fixed binary: `known open JIT bugs
reproduced: 3` (down from 6 before this pass's earlier work started at
6 total non-sentinel fixtures — 2 remain the unrelated, unresolved
cross-lane-contested pair, 1 is `struct_field_compound_assign`'s own
distinct bug, and 2 are gap 8's write-side, correctly left alone),
`unexpected failures (regressions): 0`.

**Reverse control re-run after the fix**, per this pass's standing
practice: corrupted `sentinel_basic_arithmetic`'s pinned expected value,
confirmed `REGRESSION` + exit 1; restored it, confirmed exit 0. The
harness still actually observes the fixed binary rather than reporting
green unconditionally.

The three now-fixed fixtures' `known_good` field was updated from
`"interpret"` to `"both"` in the harness (§10's earlier framing), since a
future JIT regression on these three is now a real regression to catch,
not an ambiguous "did it get fixed or is the check wrong" situation.

### 11.5 Summary

Three of gaps 8/9/10's manifestations (the ones sharing the read-side
tag-boxing-on-global-read mechanism unified in §9) are fixed: gap 9 itself
(`cross_module_global_import`), the originally-misdiagnosed "gap 10"
(`cfg_arch_global_variants`), and the cleanest general instance
(`module_global_direct_read_untagged`). Gap 8's write-side defect remains
open by design (out of this pass's scope). The two cross-lane-contested
fixtures (`chained_to_i64_twice`, `list_get_shifted`) remain unresolved
and untouched — this fix does not bear on that contradiction.

## 12. Gap 8's write-side defect — investigated, NOT fixed: this is a missing feature, not a pipeline gap

**Re-ran gap 8's repro first, on the read-side-fixed binary, per
instruction, before theorizing.** Still `X=0` under both plain JIT and
`SIMPLE_JIT_STRICT=1`; interpreter still correctly gives `42`. The
read-side fix changed nothing about gap 8's presentation — confirming
gap 8's remaining defect is a genuinely separate, write-side mechanism,
not a compound symptom the read-side fix would have altered. Established
today's actual behavior with a real run before building any theory on it,
exactly the discipline this whole chase has needed repeatedly.

### 12.1 Ruled out: `record_function_init` is for bare function references, not calls

The obvious next place to look, `record_function_init`
(`module_pass.rs:300-319`, populating `global_init_functions`), turned out
not to apply: it requires `types.get(ty)` to itself be a `HirType::Function`
(i.e. the *global's own type* is "function", as in `val handler =
some_function` assigning a function *reference*) and requires the
initializer expression to be a bare `Expr::Identifier`/`Expr::Path`. Gap
8's `val X = get_value()` is a `Expr::Call`, matching neither condition —
this map and its consumer never see gap 8's case at all. Read before
building on it, matching the discipline that caught the wrong `@cfg` and
`Node::Static` premises earlier in this document.

### 12.2 The actual write-side mechanism: there isn't one, for any non-trivial initializer

Traced `generate_module_init` (`codegen/common_backend.rs:2150`), the
function that emits the actual Cranelift IR for the runtime module-init
function every JIT compile calls (via `run_module_init_once`, established
in the §6 gap-9 investigation). Its parameters:

```rust
fn generate_module_init(
    &mut self,
    init_strings: &HashMap<String, String>,
    init_arrays: &HashMap<String, HirGlobalArrayInit>,
    init_functions: &HashMap<String, String>,   // bare fn REFERENCES only, §12.1
    init_structs: &HashMap<String, HirGlobalStructInit>,
) -> BackendResult<()>
```

and the set that decides which globals even get visited by it
(`common_backend.rs:1937-1941`):

```rust
let mut runtime_init_globals = HashSet::new();
runtime_init_globals.extend(mir.global_init_strings.keys().cloned());
runtime_init_globals.extend(mir.global_init_arrays.keys().cloned());
runtime_init_globals.extend(mir.global_init_functions.keys().cloned());
runtime_init_globals.extend(mir.global_init_structs.keys().cloned());
```

There is no fifth category. A module-level global's initializer is
handled in exactly one of two ways anywhere in this codegen:

1. **Const-evaluable** (`try_const_eval`/`try_const_float_eval`, integer
   and float literals and simple literal arithmetic): baked directly into
   the global's static `.data` bytes at `declare_data` time — no runtime
   code at all, correct and fast.
2. **String / array / struct-literal / bare-function-reference**: handled
   by dedicated runtime-init code generated in `generate_module_init`.

**Anything else — any expression requiring genuine runtime evaluation
that isn't one of those four recognized shapes — has no code path.** The
global's `.data` slot is declared but never written by any generated
code, so it silently keeps its zero-initialized default forever. This is
not specific to function calls: confirmed with a second, independent
repro using no function call at all —

```simple
val BASE = 10
val DERIVED = BASE + 5   # not const-evaluable: try_const_eval doesn't resolve
                          # a reference to another global, only literal operands

fn main():
    print("BASE={BASE} DERIVED={DERIVED}")
```

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run derived.spl
BASE=10 DERIVED=15
$ SIMPLE_EXECUTION_MODE=jit bin/simple run derived.spl
BASE=10 DERIVED=0
```

Identical shape to gap 8's own repro: `BASE` (a plain literal) is
correct; `DERIVED` (an expression that needs runtime evaluation to
produce a value) silently reads `0`. Per the explicit instruction to
verify a candidate premise with a second form before escalating: this
second, function-call-free repro confirms the gap is general — "any
non-const module-level initializer" — not narrowly about function calls.

### 12.3 Not a JIT-only defect

`generate_module_init` lives in `codegen/common_backend.rs`, shared by
the Cranelift JIT backend and (per its surrounding code, referenced
throughout this file for the whole-program native-build path too) the
AOT/native-build codegen. This is not a "the whole-program pipeline does
X and `run_file_jit` skips it" pipeline-completeness gap — the shape
every other gap in this document has been. **It is a genuine missing
codegen feature, present identically in both compilation modes**: no
code anywhere lowers a general (non-literal, non-string/array/struct/
bare-fn-ref) module-level initializer expression into real "evaluate
this and store the result" runtime code. Whole-program native builds
were not independently re-tested this pass (out of scope — the
differential harness's fixtures target `run_file_jit`), but the absence
of any relevant call to `generate_module_init` with additional
parameters, and the absence of any other module-init-generating function
in this codegen file, makes it very unlikely the native build path
somehow handles this case through a different mechanism this pass missed.
Flagged as an inference worth a direct native-build check in a future
pass, not verified here.

### 12.4 Not attempted as a patch — stopped and surfaced, per instruction

**This is a companion to gap 9's open architecture question, not a
patch.** Implementing correct behavior needs: for a module-level
initializer that isn't const-evaluable and isn't one of the four
recognized dynamic shapes, lower the initializer *expression itself* as
real code inside the generated `__module_init` function body (the same
general expression-lowering machinery an ordinary function body already
uses for a local `val`'s initializer — calls, binary ops, arbitrary
expressions), then emit a `GlobalStore` of the result. That is a new
codegen capability (teaching `generate_module_init` — or a MIR pass
feeding it — to walk an arbitrary `HirExpr`/MIR initializer, not just
recognize four closed-form shapes), not a call-site fix on the order of
§11's. It is comparable in scope to gap 9's still-open question (§6),
though structurally unrelated: §6 is about cross-file symbol identity for
already-correct init values; this is about the module-init generator's
initializer-shape coverage being fundamentally incomplete, in a single
compilation unit, for both JIT and native builds alike.

**Disposition:** left open. `module_global_from_fn_call_reads_zero.spl`
and `module_level_val_from_call.spl` remain in the differential harness
exactly as before (`known_good: "interpret"`), correctly still failing.
No source change made this pass for the write side, per instruction.

## 13. AOT/native-build confirmation — PROVED, not inferred: this affects shipped binaries, not just `simple run`

**§12.3's "very unlikely... not verified here" inference is now resolved
empirically, per explicit instruction not to reason from shared-code-path
alone.** Both repro forms were built through the real AOT compile path
and the produced standalone executables were run directly, with no
`simple run`, no interpreter, and no JIT involved at any point.

### 13.1 Finding a working AOT compile path

`native-build --entry`/`--entry-closure` (the whole-project builder this
document has been diffing against `run_file_jit` throughout) turned out
to be **independently broken in this environment** for reasons unrelated
to gap 8: every invocation attempted (varying `--source`, `--entry-closure`,
scratch directory vs. in-worktree, deployed binary vs. a freshly built
candidate) failed with `native-build worker exited with code 1`, tracing
(with `--verbose`) to parse/lint errors in unrelated compiler-internal
files (`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`,
`src/compiler/80.driver/shb/shb_writer.spl`) that this document's
two-line repro has no connection to — the worker appears to pull in a
large, unintended slice of `src/compiler/*` regardless of `--source`/
`--entry-closure` scoping. This is a real, reproducible tooling defect,
distinct from and unrelated to gap 8; flagging it here rather than
silently routing around it, since it blocks the more "canonical" whole-
program path this document otherwise uses for comparison.

**Routed around it via a different, working command:** `simple compile
<file.spl> --native --backend cranelift -o <output>` — a genuine
single-file AOT compiler distinct from `native-build`, unaffected by the
above. Produced real, standalone, stripped, position-independent ELF
executables (confirmed via `file`) for both repro forms.

### 13.2 Results — both forms, PROVED

Compiled with this pass's own fixed candidate binary (carrying §11's
read-side fix), then ran the produced executables directly, no interpreter
in the loop at all:

```
$ simple compile aot_test1/main.spl --native --backend cranelift -o aot1
Compiled ... -> aot1 (11496 bytes, opt-level=aggressive)
$ file aot1
aot1: ELF 64-bit LSB pie executable, x86-64, ... stripped
$ ./aot1
BASE=10 DERIVED=0
```

```
$ simple compile aot_test2/main.spl --native --backend cranelift -o aot2
Compiled ... -> aot2 (11304 bytes, opt-level=aggressive)
$ ./aot2
X=0
```

Both reproduced 3/3 repeat runs, fully deterministic (this is a
compile-time codegen omission, not a runtime race — no reason to expect
otherwise, and confirmed rather than assumed).

**`BASE=10` is correct — §11's read-side fix extends cleanly to AOT.** A
useful bonus confirmation: `generate_module_init`/`declare_data` and the
HIR type-inference fixed in §11.2 are shared between the JIT and
native/AOT codegen paths (as §11.3 already established for the
architecture question), so the read-side fix benefits both compilation
modes, not just `run_file_jit`. This was not separately claimed before
this pass verified it directly.

**`DERIVED=0` and `X=0` are wrong — the write-side defect is confirmed in
real, shipped, standalone binaries.** Not a `simple run` artifact, not a
JIT-only defect, not an inference from `generate_module_init` being
"shared code" — a real executable, run with no Simple toolchain present
at runtime at all, silently produces a zeroed global exactly as `run_file_jit`
does.

### 13.3 Independent corroboration already on record

`test/01_unit/compiler/lint/module_init_literal_spec.spl` and
`src/compiler/35.semantics/lint/module_init_literal.spl` (MODINIT001,
already landed, pre-dating this pass) exist specifically to catch this
class of declaration via static text-heuristic analysis ahead of a real
build. The lint's own file header states directly: *"On `native-build
--entry`, a module-level `val`/`var` whose initializer is not a bare
literal may need runtime init code."* Its test spec's header is more
direct still: *"the bug class where native-build --entry silently skips
the initializer and the global reads a zero/nil default."* This pass's
§13.2 result is the first *build-and-run* confirmation of what that
lint was already written to defend against — the two records now
corroborate each other rather than one merely assuming the other.

### 13.4 Severity — escalated, explicitly

Every other JIT-only finding in this whole session's chase (all eight
originally-named gaps, and every candidate this document's sweep
enumerated) was scoped to `simple run`'s JIT engine: a real defect, but
one that a compiled, shipped artifact would not carry, and one
`SIMPLE_JIT_STRICT`/differential-harness-style tooling could in principle
catch pre-ship. **This one is different in kind.** A module-level global
whose initializer needs genuine runtime evaluation — any function call,
any reference to another global, any non-trivial expression — silently
compiles to a zeroed value in a **shipped, standalone binary**, with no
interpreter fallback available (native/AOT binaries have no interpreter
to fall back to) and no runtime signal that anything went wrong. This
applies to every native/AOT-compiled target this codegen backend serves,
which per this document's and the wider session's own references
includes SimpleOS and other compiled targets, not only the interpreter-
adjacent `run_file_jit` path this whole document otherwise concerns
itself with.

### 13.5 Still not attempted as a fix

Per instruction, unchanged from §12.4: this needs a new codegen
capability (lowering an arbitrary initializer expression as real code
inside the generated module-init function, for both the JIT and
native/AOT backends that share `generate_module_init`), not a patch, and
sits alongside gap 9's cross-file-identity question as a second, separate,
now more clearly consequential architecture decision for whoever picks
this up next.

## 14. Correction, follow-up pass: `native-build --entry` is not "unrelated files failing to parse" — it dispatches to a different compiler entirely

The follow-up investigation into "why does `native-build` fail in this
environment" (requested after §13) found the initial impression wrong and
filed the real result separately:
`doc/08_tracking/bug/native_build_self_hosted_mir_infer_type_crash_2026-07-30.md`.
Summary, since it bears directly on how to read §§1-13 above:

- **`native-build`, on the deployed/self-hosted binary, dispatches to the
  pure-Simple self-hosted compiler (`src/compiler/**.spl`), not the Rust
  seed's `native_project` module** this document spent §§1-12 diffing
  `run_file_jit` against. The `src/compiler/*.spl` warning noise seen in
  earlier attempts was the self-hosted compiler itself being loaded to do
  the compile, not unrelated files swept in by mistake. §§1-12's
  Rust-seed-vs-Rust-seed comparison remains a valid, self-consistent
  characterization of the Rust seed's own behavior (relevant to
  bootstrap-stage builds the seed drives itself), but is not what an
  ordinary `bin/simple native-build` invocation executes.
- The actual failure is a real, reproducible, minimal-repro'd crash in the
  self-hosted compiler's own MIR lowering (`HirTypeKind::Infer` unhandled
  in `function_lowering.spl`) on module-level globals with a
  binary-expression initializer — not stale cache (ruled out with
  `--clean --no-incremental` + a fresh cache dir), not the same defect as
  §13's.
- **Correction to §13.3/§13.4's framing:** those sections' "shared
  codegen backend, therefore affects AOT uniformly" claim holds for
  `simple compile --native` (which shares the Rust seed's
  `generate_module_init` with `run_file_jit`, both giving `X=0`), but
  **not** for `native-build`'s actual self-hosted-compiler pipeline, which
  handles the exact same function-call-initializer case *correctly*
  (`X=42`) via its own, independent implementation. Two separate compiler
  implementations, two separate (and differently-shaped) defects for two
  different initializer forms — not one shared defect uniformly affecting
  "AOT" as a single concept. §13's core claim — shipped binaries can
  silently carry zeroed globals — remains true and proved for `simple
  compile --native`; it is not established for `native-build` specifically,
  which instead hard-crashes rather than silently zeroing, for a related
  but distinct initializer shape.

## 15. Re-run of the original web showcase repro — still blocked, and it is this document's own write-side defect

The web showcase repro (`examples/06_io/ui/web_render_file_gui.spl`,
`web_standards_showcase status=fail reason=blank-or-uniform pixels=0
nonzero=0 checksum=0`) is the repro that launched this entire chase —
attributed in turn to gap 7, then gap 8, then gap 9. Re-run after §11's
fix landed, per instruction, rather than assuming a fix landing means the
blocker cleared (the exact lesson gap 7→8 already taught this chase
once). **Still blocked, byte-identical output before and after the fix.**
Full evidence, binary identity (sha256 for both the deployed-unfixed and
freshly-built-fixed binaries, confirmed by behavior not just hash),
environment preconditions (57-file `assets/fonts` worktree, 0-timeout,
protected binary paths), and an isolated minimal repro pinning the exact
mechanism: `doc/08_tracking/bug/
web_showcase_repro_rerun_after_read_side_fix_2026-07-30.md`.

**Not a new gap.** The cell's own `RW`/`RH` resolve through
`SHOWCASE_DIMS = showcase_resolution_dims()` — a function-call
initializer, exactly this document's own §12 write-side defect, which
this pass's read-side fix (§11) was explicitly scoped not to touch. This
confirms the write-side defect (already proved to affect real AOT
binaries in §13) is not just a synthetic-fixture concern — it is the
actual, real-world blocker in the code that motivated the whole
investigation.

## 16. Gap 8's write-side defect — FIXED, commit `48af531ce0e`

§12.4 scoped the write-side fix out as an architecture decision. Revisited
under explicit authorization once it was the sole remaining blocker: "a
bounded feature addition, not an open-ended redesign."

### 16.1 The fix

`hir/lower/module_lowering/module_pass.rs` (both `lower_module` and
`lower_module_with_warnings` — there are two independent, near-duplicate
copies of the whole pass structure in this file; the first attempt landed
only in the one `run_file_jit` does *not* call, see 16.2) synthesizes a
`__module_init_dynamic` HIR function: one `HirStmt::Assign` per
module-level `val`/`var`/`const` whose initializer isn't one of the five
const-foldable shapes (checked by testing membership in
`global_init_values/strings/arrays/functions/structs`), built by calling
the ordinary `lower_expr` on the initializer's raw AST expression, in
source declaration order. It is pushed into `self.module.functions` like
any real function — no new HIR/MIR expression-lowering machinery, no
synthetic AST. `common_backend.rs`'s `generate_module_init` looks up
`__module_init_dynamic` in `self.func_ids` and, if present, emits one
`call` to it at the end of `__module_init`'s body — so it runs wherever
`__module_init` already does (JIT's `run_module_init_once`, and the AOT
binary's startup code), with zero changes to that dispatch mechanism.

Ordering: declaration order sufficed for every case tested (the two
fixtures, and the real `SHOWCASE_DIMS` → `RW`/`RH` chain). No topological
sort was needed — a const-foldable global is already resident in static
`.data` before any code runs, so it's never a dependency-order problem;
a dynamic global that depends on another dynamic global is only correct
if the producer is declared first in source, which held in every case
encountered. This is the bounded case the scope-change instruction asked
for, not the open-ended one.

### 16.2 Two premise-check misses along the way (both caught by testing, not assumed)

1. **Wrong function edited first.** `module_pass.rs` has two independent
   `lower_module*` methods with near-duplicate bodies (`lower_module`,
   called by `run_file_jit`'s `hir::lower_with_context_lenient_and_project_hint`,
   and `lower_module_with_warnings`, called only by tests and
   `gen_lean.rs`). The first attempt landed the pass into the latter;
   `SIMPLE_WRITEFIX_DEBUG=1` trace showed the new debug line never fired.
   Fixed by adding the identical block to the actually-used function too.
2. **Two follow-on defects, not one clean pass.** Once the function
   synthesized and got called: (a) a raw int stored into an ANY-typed
   global (`val X = get_value()`, X never explicitly typed) misread as a
   pointer on next read — fixed by boxing in `lowering_stmt.rs`'s
   `HirExprKind::Global` assign arm, mirroring the existing
   `needs_boxing` pattern from builtin-call-arg and struct-field lowering.
   (b) writing to a purely-dynamic global segfaulted — `gdb` showed the
   write target address in the same memory region as JIT *code*, not
   data: `runtime_init_globals` (which controls whether a global's data
   is declared writable) only unions the four const-foldable maps, so a
   global with no other init shape was declared read-only. Fixed with a
   fifth field, `dynamic_init_globals` (`HirModule` and `MirModule`,
   mirroring the existing four), unioned into `runtime_init_globals`.

### 16.3 Non-vacuous proof, in the required order

1. `scripts/check/check_jit_interpreter_differential.spl`, all 9
   fixtures + reverse control: 2 flip from known-bug to
   "APPEARS FIXED" (`module_level_val_from_call`,
   `module_global_from_fn_call_reads_zero`), 0 regressions, 1 known
   unrelated bug (`struct_field_compound_assign`) still present as
   expected.
2. `val BASE = 10; val DERIVED = BASE + 5` and `val X = get_value()`:
   correct (`10`/`15`, `42`) under `run_file_jit` AND under
   `simple compile --native` (standalone AOT binary, exit 0).
3. The isolated struct-return + field-derivation repro from
   `doc/08_tracking/bug/web_showcase_repro_rerun_after_read_side_fix_2026-07-30.md`
   (`DIMS = resolve_dims(); RW = DIMS.w; RH = DIMS.h`): JIT now matches
   interpret exactly (`RW=480 RH=360 product=172800` both engines).
4. Real web showcase (`examples/06_io/ui/web_render_file_gui.spl`,
   `SHOWCASE_RESOLUTION=480x360`, `SIMPLE_TIMEOUT_SECONDS=0`, 57-file
   `assets/fonts` worktree): no longer fails at
   `reason=blank-or-uniform pixels=0 nonzero=0 checksum=0`. It now
   proceeds past global init into actual rendering and fails at a
   **different, later, unrelated** check:
   `reason=vector-font-evidence ... expected_pixels=100 pixels=16`. This
   is real progress (the write-side defect no longer blocks this cell)
   but not a fully green run — the vector-font-evidence mismatch is a
   separate, out-of-scope defect for a follow-up pass.

`native-build` (the pure-Simple self-hosted compiler) was not touched —
confirmed earlier in this campaign to already lower these initializers
correctly via its own, independent pipeline.

Landed via git plumbing (fresh SSH `ls-remote`, exact-SHA `read-tree`,
6-file scoped commit, conflict-tree and marker guards clean) at
`48af531ce0eca62c47787394016aa73d55294d5c`, parent
`ef90c16b1949f393068e64be2da9a5c5661262a9`.

### 16.1 Follow-on: `vector-font-evidence` -- three-pass narrowing, then a correction

After 16 landed, the web showcase no longer failed at
`reason=blank-or-uniform pixels=0` (confirmed non-vacuous: the write-side
fix works). It advanced to a new, different, later failure:
`reason=vector-font-evidence expected_identity=...;axes=static
identity=...;axes=wght=100 expected_pixels=100 pixels=16`. Three
instrumented passes against the real, working showcase pipeline (not a
synthetic probe, per the "instrument the real pipeline" correction after
an earlier probe hit an unrelated JIT crash) narrowed this:

1. Identity mismatch traced by exact sha256 comparison against the font
   candidate table: the renderer picked candidate #0 ("Noto Sans SC", a
   CJK variable-weight sans face, `wght=100` default instance) instead of
   the requested candidate #9 ("Bungee", `category=display`, the only
   display-category candidate). `font_pixel_size=16` matched the
   `Style` struct's hardcoded default (`font_size: 16, font_family:
   "sans-serif"`) exactly.
2. A level-gated trace (`SIMPLE_TRACE_FONT_STYLE`, added permanently,
   default off, at the exact `resolve_font_metrics_with_language` call
   site in `simple_web_html_layout_renderer_core.spl`) confirmed: all 59
   traced `#text` nodes on the real page, including the marker
   (`index=152 text=Simple Web 300 DPI`), read `font_family=sans-serif
   font_size=16` -- the struct defaults, not the marker's own
   `style='font-family:Bungee;font-size:100px'`.
3. A second trace extension pinned this further: the marker DIV's own
   post-cascade `font_family`/`font_size` (`index=151`, stored into
   `styles[151]` before its child text node inherits from it) were
   *also* the defaults -- and `attr_value(nd.attrs_raw, "style")`,
   the same helper already working for other attributes in this file,
   returned empty for every one of the 153 nodes on the page, including
   the marker div. This was reported as "declarations never parsed,
   upstream of the cascade" -- outcome 1 of three the coordinator asked
   to distinguish.

**Correction (still within the same pass): outcome 1 was itself a JIT
read-side artifact, not the real defect.** Testing the same minimal
input (`<div id='marker' style='font-family:Bungee;font-size:100px'>hi
</div>`) through the pre-existing `simple_web_layout_debug_attr_by_id`
debug entry point, side by side under both engines:

```
interpreter: style_val=[font-family:Bungee;font-size:100px] len=34   (correct)
jit:         style_val=[] len=0                                       (wrong)
```

The HTML attribute parser is correct -- proven directly, not inferred.
The defect is JIT's struct-field reads on `[HNode]` array elements for
non-`#text`-tagged nodes: reading `tag`/`id_attr`/`style_attr`/
`attrs_raw` off an element-shaped `HNode` returns empty/corrupt under
JIT while the identical interpreter call is correct, reproduced with a
2-line HTML input, no rendering pipeline involved (see the new
`simple_web_layout_debug_dump_nodes` permanent debug helper).

**Disposition: this is a JIT engine correctness defect (struct-field/
array-element read reliability for this class shape), not a bounded
browser-engine attribute-parsing fix.** It is a materially larger and
different category than the "small, specific, falsifiable" fix the
outcome-1 framing suggested -- consistent with several other "silently
wrong under JIT" struct-field defects already on record this session
(see the memory index: struct-field compound-assign, list.get shift,
nested-array element read, etc.). Not attempted as a fix in this pass.
The web showcase cell remains BLOCKED; scoreboard remains 2 GREEN.

Evidence commits (all in this pass, `origin/main`):
`0e3176a9810a8b9957addc14c97c3d062d204826` (first trace, #text call
site), `86c0202b897a1ffb865844cd351c19de7d20ac4d` (second trace,
parent-element cascade + raw attrs), `3fa408bcc3ab6ca32746700f26ac90cd20bf0697`
(dump-nodes helper + the correcting JIT-vs-interpreter control).

### 16.2 Root cause found and fixed: `BeDomNode.element` overload collision -- but the web showcase is still blocked

Authorized to chase the JIT struct-field-read defect into codegen,
since (per instruction) it's the same subsystem worked in all session
("more bounded than the module-init fix ... a 2-line repro with no
rendering pipeline"). Reduced first, per instruction, before reading
codegen:

- A from-scratch synthetic class matching `HNode`'s exact field shape
  (text/Dict/`[T]`/i64, `me` mutating methods, nested-struct-returning
  helper) read correctly under both engines -- ruled out struct shape,
  array storage, and mutating methods as the trigger on their own.
- Bisecting the *real* pipeline instead: `html_tree_builder_flat_projection`
  (bypasses `HNode` entirely) reproduced it. `html_tree_builder_build`
  walked recursively via `.children[i]` (bypasses the stack-pop
  traversal too) also reproduced it. Constructing `BeDomNode` by hand
  via its own `.element`/`.text_node` static constructors + `set_attr`/
  `add_child`, with **zero tokenizer involvement**, still reproduced it
  -- pinning the defect to the `BeDomNode` type/constructors themselves,
  not tokenizer volume or traversal style.
- The isolating difference from the synthetic reproduction that finally
  worked: `BeDomNode` has **two `static fn element` definitions in the
  same `impl` block**, differing only in arity (`element(tag_name)` vs
  `element(node_id, tag_name)`). A synthetic class with the identical
  overload -- nothing else changed -- reproduced the corruption; renaming
  the overload to a unique name and nothing else fixed it, in the same
  15-line file, both directions confirmed.

**This is a JIT overload-dispatch defect, not a new, disconnected bug.**
It's the same mechanism already surfacing all session as the
`compiler_cross_module_private_symbol_collision` warning ("2
co-compiled definitions with 2 differing signatures ... falling back to
the last definition when types are ambiguous") seen on every test run
against `_apply_multiple`/`_clamp_byte`/`_coverage`/`_validate_context`
in the font-shaping code -- just for same-class static methods rather
than cross-module private functions, and manifesting as silent struct
corruption (no warning printed) rather than a printed warning. It is
also, now that it's found, the mechanism behind every layer of the
`vector-font-evidence` misdiagnosis in 16.1: blank pixels (write-side,
unrelated) -> wrong font -> "computed style never populated" -> "style
attribute never parsed" were four masks worn by this one JIT defect,
observed through JIT at every layer.

**Fix**: `dom.spl`'s 2-arg `static fn element(node_id, tag_name)`
renamed to `element_with_id` (the rare form, ~15 call sites) rather than
the 1-arg `element(tag_name)` (~250+ call sites across the app and
tests) -- minimizing blast radius, not correctness-relevant which side
was renamed. All call sites updated (`html_tree_builder.spl`,
`browser_renderer.spl`, `html_string_parser.spl`, 3 test spec files, and
the new debug helper below).

**Non-vacuous proof**: `scripts/check/check_jit_interpreter_differential.spl`
gained a 10th fixture, `bedom_overload_style_attr.spl` -- the isolated,
tokenizer-free repro, using a new permanent debug helper
`be_dom_debug_manual_tree_dump()` (`dom.spl`). All 10 fixtures green, 0
regressions. The real pipeline's `simple_web_layout_debug_attr_by_id`
and `simple_web_layout_debug_dump_nodes` (from 16.1) now match
interpreter exactly under JIT for the marker `<div>` case
(`style_val=[font-family:Bungee;font-size:100px] len=34`).

**Web showcase re-run: the CSS-level fix is confirmed live in the real
pipeline, but `vector-font-evidence` still fails identically.** The
`SIMPLE_TRACE_FONT_STYLE` trace against the real showcase now shows the
marker `#text` node correctly resolving `font_family=Bungee
font_size=100` (previously `sans-serif`/`16`) -- the CSS cascade fix is
proven live, not just in isolation. But the showcase's printed result is
**byte-for-byte identical to before the fix**:
`reason=vector-font-evidence expected_identity=...;axes=static
identity=sha256=a3041811a7...;axes=wght=100 expected_pixels=100
pixels=16` -- still Noto Sans SC, still pixel size 16. This means the
Draw-IR/glyph-rendering layer's font identity and pixel size
(`Engine2dDrawIrAdvResult.font_identity`/`vector_font_pixel_size`) are
**not** simply reading the now-correct `Style.resolved_font_identity` --
there is a second, separate, not-yet-root-caused defect between CSS
style resolution and Draw-IR text-command generation. Not chased further
in this pass, given the scope already covered; a same-technique
bisection (isolate the Draw-IR font-selection call with a synthetic
repro, check for another overload/cross-module-name collision given the
`_apply_multiple`/`_coverage`/`_validate_context` warnings already
observed in that exact subsystem) is the natural next step.

**Disposition, per instruction: do not report the cell green.** The
`vector_fixture` overload fix is real, proven, and landed -- but
`vector-font-evidence` still fails, unchanged in its exact values.
Scoreboard remains 2 GREEN. A separate JIT run also hit the
already-documented, unrelated `duck-typed virtual method call ... no
vtable` crash (`bug jit_game2d_backend_method_dispatch_sigsegv_2026-07-02`)
nondeterministically (2 of 3 attempts); the one clean completion is the
result quoted above.

Commit: `8ddaf9f40e1850f87a5c80400ef2c1cbafc57ba4`.

### 16.3 Sweep for the same pattern elsewhere, before the next reduction pass

Per instruction, swept for the `BeDomNode.element` collision pattern
before chasing the second `vector-font-evidence` defect further.

**Static impl-block arity-overload sweep -- no trustworthy count.** Wrote
an indentation-aware scanner over `.spl` files. It flagged 11
candidates; hand-checking the top hit showed the scanner cannot tell an
impl-block-level method from a nested local/extern declaration inside a
*different* method body (`RecordingSession`'s two `rt_time_millis` hits
are `extern fn` declared locally inside two separate methods, not two
definitions at the impl block's own level). That failure mode
invalidates all 11 by the same mechanism. Not reporting a count --
building a reliable one needs real block-nesting awareness, not
text-column heuristics, which is the case for item 1 below rather than
a hand-rolled script.

**Item 1 -- detector gap (file as an enhancement, `BeDomNode.element` as
motivating case).** `compiler_cross_module_private_symbol_collision`
(`src/compiler_rust/compiler/src/pipeline/module_loader.rs`, ~line 1299)
only checks bare top-level private functions across co-compiled
modules; its own comment states methods are excluded "because
qualified methods... cannot collide on a bare name." Today's bug
disproves that assumption directly: `BeDomNode.element`, two
`static fn element` in one `impl` block differing only in arity,
corrupted every subsequently constructed/stored instance's struct
fields under JIT, with zero warning at compile time (see section 16.2).
Enhancement: extend this detector (or add a sibling pass) to flag
same-name, differing-arity methods within a single `impl` block --
same diagnostic shape, same fix (rename), but a compile-time warning
instead of silent corruption. Motivating case: `dom.spl`'s
`BeDomNode.element`/`element_with_id` split, commit
`8ddaf9f40e1850f87a5c80400ef2c1cbafc57ba4`.

**Item 2 -- 4 font-shaping collisions, noted as known-live, not fixed
here.** `_apply_multiple`, `_clamp_byte`, `_coverage`,
`_validate_context` all have 2 co-compiled definitions with differing
signatures in `src/lib/skia/feature/shaper/` (`ot_layout_context.spl`,
`ot_layout_apply.spl`, `selected_arabic.spl`, `ot_layout_gpos.spl`) --
real, printed on every run that touches this subsystem, and the same
class of hazard as `BeDomNode.element` (cross-module bare-function
collision rather than same-impl-block overload). Judged out of scope
for this task: checked directly (not assumed) whether they sit on the
web showcase's marker-text code path -- they don't. They're reached
only via `_resolve_selected_shaped_glyph_run`, gated by
`if complex_script != 0`; the marker's text ("Simple Web 300 DPI") is
plain ASCII/Latin, so `complex_script` is 0 and this path does not
execute for this bug. Recorded here so they are not rediscovered as if
new; the fix, when picked up, is the same rename pattern used in 16.2.

### 16.4 Reduction pass on the font-identity path -- capped at one pass

The remaining `vector-font-evidence` defect: CSS style resolution is
now confirmed correct (16.2 -- the marker resolves `Bungee`/`100` live
in the real pipeline), but `Engine2dDrawIrAdvResult.font_identity`/
`vector_font_pixel_size` still report Noto Sans SC / 16, unchanged from
before the fix. Checked directly (16.3) that this is not the same
impl-block overload pattern in the direct code path
(`font_renderer.spl`, `draw_ir_adv.spl`,
`simple_web_layout_engine2d_fast.spl`, `font_registry.spl` -- zero
scanner hits). Treated as new territory, not an instance of the same
bug, per instruction.

**Step 1 -- isolate `resolve_font_metrics_with_language` itself.** Added
a permanent debug wrapper (`font_renderer_debug_resolve`,
`font_renderer.spl`) and called it directly with the correct input,
bypassing the whole HTML/CSS pipeline:

```
font_renderer_debug_resolve("Bungee", "Simple Web 300 DPI", 100, "en")
jit:         valid=true family=Bungee identity=sha256=c4f5361ce1...axes=static reason=resolved
interpreter: valid=true family=Bungee identity=sha256=c4f5361ce1...axes=static reason=resolved
```

Identical, correct, under both engines. **The font-resolution function
itself is not the defect** -- ruling out font loading/caching
(`_browser_default_for_family_cached`) as the cause.

**Step 2 -- trace the value at the point Draw-IR consumes it.** Added a
gated trace immediately before `eng.select_font_identity(font_identity)`
in `draw_ir_adv.spl` (the `font_identity` read from the text command's
own `computed_style`, via `_engine2d_draw_ir_style_value(command.
computed_style, "font-identity")`). Re-ran the real showcase (3 of 4
attempts hit the unrelated flaky `duck-typed virtual method call`
crash noted in 16.2; one clean run):

```
[draw-ir-font-trace] font_identity=sha256=a3041811a7...;axes=wght=100   <- still Noto Sans SC
web_standards_showcase status=fail reason=vector-font-evidence ... (unchanged)
```

**The wrong identity is already present in the Draw-IR command's
`computed_style` before font selection runs at all.** This localizes
the defect precisely: not `eng.select_font_identity`'s own lookup (ruled
out -- the value handed to it is already wrong), and not
`resolve_font_metrics_with_language`/CSS style resolution (ruled out in
step 1 and in 16.2's live trace of this exact marker). The value comes
from `draw_ir_style_prop("font-identity", st.resolved_font_identity)`
in `simple_web_html_layout_renderer_paint_layout.spl:1152` -- meaning
the specific `Style` object feeding *this* Draw-IR-generation call
(reached via `simple_web_layout_engine2d_fast.spl`'s fast/no-mirror
Draw-IR path, not necessarily the same call site instrumented in 16.2)
still holds the pre-fix value, despite `compute_styles`/
`compute_styles_with_material` being one shared implementation.
`compute_styles(...)` has roughly a dozen call sites across
`simple_web_html_layout_renderer.spl`, each computing its own `styles`
array for a different render entry point; which one specifically feeds
the fast Draw-IR path, and why its result still differs from the one
traced live in 16.2, was not identified.

**Stopping here, per instruction.** This is the fifth mask of the day
and the returns on continuing were explicitly capped at one pass. The
boundary: confirmed CSS resolution and the standalone font-metrics
function are both correct; confirmed the wrong value is already baked
into the Draw-IR command before font selection; not yet identified
which of the ~12 `compute_styles` call sites (or which distinct code
path through `simple_web_layout_engine2d_fast.spl`) produces that
specific `Style` object, or why it differs from the correctly-computed
one.

### 16.5 Named the call site by static read alone -- refutes the "different Style computation" hypothesis

Per instruction: a pure call-graph read (no new instrumented run) to
name which of the ~12 `compute_styles` call sites feeds
`paint_layout.spl:1152`.

Traced upward from the consumer: `_html_draw_ir_style_props` (defines
line 1152) has one plural-form caller, `_html_draw_ir_commands`
(`simple_web_html_layout_renderer.spl:1235`); that function's sole
caller is `_simple_web_layout_compose_retained`, called at line 1534
from `_simple_web_layout_render_html_draw_ir_result_at_time` (defined
line 1390). Every `pub fn simple_web_layout_render_html_draw_ir_result*
_with_images` wrapper the fast Draw-IR path
(`simple_web_layout_engine2d_fast.spl`) imports and uses funnels into
this one private function, with `vector_fonts=true` threaded through
from the wrapper. It has exactly one style computation:
**`simple_web_html_layout_renderer.spl:1482` --
`compute_styles_with_material(nodes, rules, child_index, false,
vector_fonts, material_entries, material_counts, cpu_material_nodes,
solid_material_nodes)`.**

**This is the same shared implementation already instrumented and
proven correct in 16.2/16.4 step 1** (the one whose live trace showed
the marker resolving `Bungee`/`100`), not a different one. The "a
different Style computation feeds paint" hypothesis from 16.4 does not
survive this read -- refuted by the call graph, the same discipline
applied to hypotheses all session.

**Revised next-step hypothesis, precise but not confirmed:** since the
single named style-computation call site is proven correct, the
divergence must happen *after* correct style computation and *before*
`paint_layout.spl:1152` consumes it -- most plausibly an index/ordering
mismatch between `styles[]` and the filtered/reordered draw-command
list (`_html_draw_ir_visible_nodes`, `_html_draw_ir_append_context_
paint_order`, `_html_draw_ir_node_paint_order` all reorder/filter nodes
for paint purposes), associating the marker's draw command with a
*different* node's `Style` entry -- one that legitimately resolved to
Noto Sans SC via real CSS elsewhere on the page (e.g. a `lang="zh"`
element matching Noto Sans SC's language coverage). Confirming this
needs one more instrumented run: compare the node index actually used
to fetch `st` at `paint_layout.spl:1152` (or in
`_html_draw_ir_command`) against the marker's real index (150, per the
16.4 trace) for the *same* run. Not run in this pass -- past the cap,
next owner's instrumented pass.

**Disposition: web showcase cell stays BLOCKED. Scoreboard: 2 GREEN.**
Diagnostics landed this pass (`font_renderer_debug_resolve`, the
`draw_ir_adv.spl` trace point); the call site named this step by read
only; no fix attempted, per the cap.

**Handoff summary for the next owner:**
- Ruled out: font loading/caching (`_browser_default_for_family_cached`
  / `resolve_font_metrics_with_language`, correct under both engines in
  isolation); `eng.select_font_identity`'s own lookup (the wrong value
  is already in its input); a *different* Style computation feeding
  paint (refuted by call-graph read -- it's the same one, proven
  correct).
- Ruled in / named: `simple_web_html_layout_renderer.spl:1482`
  (`compute_styles_with_material`) is the sole style source for the
  showcase's Draw-IR path; `simple_web_html_layout_renderer_paint_
  layout.spl:1152` (`draw_ir_style_prop("font-identity", st.
  resolved_font_identity)`) is the consumer with the wrong value.
- Next instrumentation, one hop, already gated and ready to extend:
  print the node index and `st.resolved_font_identity` immediately
  around `paint_layout.spl:1152` (and/or inside `_html_draw_ir_
  commands`'s node/style pairing) using the existing
  `SIMPLE_TRACE_FONT_STYLE` gate, in the same run, and compare against
  index 150's known-correct value from 16.4.

### 16.6 Consumption-site instrumentation landed; hypothesis NOT yet tested (run exceeded budget)

Per the 16.5 handoff, the next step was one instrumented run comparing the
index/style actually consumed at `paint_layout.spl:1152` against the
marker's known-correct index 150.

**Instrumentation landed and verified compilable** — a level-gated trace
(default off) at the *definition* of `_html_draw_ir_style_props`
(`simple_web_html_layout_renderer_paint_layout.spl`), so it covers **all
four** call sites (1380, 1544, 1716, 1806) rather than one. It joins the
existing `SIMPLE_TRACE_FONT_STYLE` family per the log-retention rule and
prints, for the marker node or any node whose style claims `Bungee`:

```
draw_ir_style_props_pairing tag=… id=… class=… marker=… font_family=… font_size=… identity=…
```

`HNode` carries no index field, so the node is identified by `id`/`class`;
that is sufficient to answer the actual question — whether the **marker
node** receives a wrong `Style`, or a **different node's** `Style` entry
(the index/ordering mismatch hypothesis).

Two corrections made while landing it, both worth keeping:
- the marker is an **`id`** (`id='simple-web-vector-font-evidence'`), not a
  class — an initial class-based predicate would never have fired;
- `paint_layout.spl` does **not** import `env_get`; the trace needs
  `use std.gc_async_mut.io.mod_stub.{env_get}`, the same import
  `simple_web_html_layout_renderer_core.spl:3` uses.

**Result: the hypothesis is neither confirmed nor refuted.** Two runs were
made and neither reached the consumption site:

1. first run — killed at the 10-minute harness cap, still in style
   computation;
2. second run (detached, 3000 s budget) — **~30 minutes, log frozen at 522
   lines**, of which 514 are the pre-existing font traces. It never
   emitted a `draw_ir_style_props_pairing` line.

**The second run's zero hits are NOT evidence of anything**: it was
launched *before* the `env_get` import was added, so its copy of
`paint_layout.spl` could not have compiled that trace had it reached it.
Recorded explicitly so nobody reads "0 pairing lines" as a refutation.

What both runs *did* reproduce, consistent with 16.4: index 150 resolves
correctly right up to the end of style computation —
`[font-style-trace] index=150 font_family=Bungee font_size=100 language=en
text=Simple Web 300 DPI` and `final_font_family=Bungee final_font_size=100`.
So the correct-computation half of 16.5 is re-confirmed on today's binary.

The blocker is cost, not correctness: this path is the documented 48-min+
web-module compile class, and the marker's paint phase sits behind it.

**Next owner: one command, no further derivation needed** (from a worktree
with `find assets/fonts -type f | wc -l` = 57, using a protected binary
name so `kill_simple_monitor.shs` does not SIGTERM it at 60 s):

```sh
SIMPLE_TRACE_FONT_STYLE=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
SIMPLE_TIMEOUT_SECONDS=0 \
  build/tmp/claude_simple run examples/06_io/ui/web_render_file_gui.spl \
  2>&1 | grep -E 'draw_ir_style_props_pairing|index=150'
```

If the marker line shows `identity=` Noto Sans SC while `font_family=Bungee`,
the Style was computed correctly and corrupted after — not an index
mismatch. If instead the marker line never appears but a *non-marker* node
prints `font_family=Bungee`, the marker's draw command was paired with
another node's entry, confirming the index/ordering mismatch and naming the
filter that reordered it.

**Disposition: web showcase cell stays BLOCKED. Scoreboard: 2 GREEN.** No
fix attempted; no fifth mask chased.

## 17. Re-audit (2026-07-31): §16's write-side fix is confirmed landed on origin/main and independently re-verified; the module-level-`val` framing of the cell's blocker is STALE

A separate task described the cell's primary blocker as "a module-level
`val` whose initializer is a function call never executes, so the global
reads as 0" (i.e. exactly §12/§16's `SHOWCASE_DIMS = showcase_resolution_dims()`
defect) and asked to pin it down fresh, without assuming §16 already
covered it. It does. This section records independent re-confirmation,
not a new finding.

**Pipeline established first, per instruction (PROVED, not inferred):**
the deployed/default Rust-seed binary dispatches `bin/simple run
<file>` (and the bare env-less invocation) to JIT — checked directly by
running the minimal repro three ways against the same binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, sha256
`ea4af9a4498297e3c4f31ca74082c20ebb10d7d2cc65218cea022960e15e597d`):
`SIMPLE_EXECUTION_MODE=jit` and no env var both print `RW=0 RH=0
product=0`; `SIMPLE_EXECUTION_MODE=interpret` prints the correct `RW=480
RH=360 product=172800`. The no-env-var run matching the explicit-JIT run
byte-for-byte is what proves JIT is the default, not an assumption from
the command name. This also cross-checks against the authoritative cell
table in `doc/09_report/showcase_matrix_census_2026-07-30.md`, which
records cell 3 as explicitly "compiled-lane-gated" (i.e. JIT/native, not
interpreted) for this exact reason.

**Ancestry of the two named commits, checked by `git merge-base
--is-ancestor` against a fresh SSH `ls-remote` tip, never by comparing
dates:**

```
$ GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" \
  git ls-remote git@github.com:ormastes/simple.git refs/heads/main
cba4abb304c3735861c5ebfac2af9a41d7e9c3ca  refs/heads/main

$ git merge-base --is-ancestor 26a0c4ad9ef cba4abb304c3735861c5ebfac2af9a41d7e9c3ca && echo yes
yes
$ git merge-base --is-ancestor 48af531ce0e cba4abb304c3735861c5ebfac2af9a41d7e9c3ca && echo yes
yes
$ git merge-base --is-ancestor 8ddaf9f40e1 cba4abb304c3735861c5ebfac2af9a41d7e9c3ca && echo yes
yes
```

Both named commits (the read-side fix and §16's write-side fix), plus
§16.2's follow-on `BeDomNode.element` overload fix, are ancestors of the
current true origin/main tip. **PROVED.**

**Does the defect still reproduce? Re-tested empirically against
multiple binaries, not inferred from the commit being an ancestor**
(a landed commit does not by itself prove which binary on disk contains
it — the deployed binary is a separate artifact):

| Binary | sha256 (short) | Contains §16 fix? | `RW RH product` under JIT |
|---|---|---|---|
| `bin/release/x86_64-unknown-linux-gnu/simple` (== `bin/simple`, currently deployed) | `ea4af9a449…` | No (pre-dates it) | `0 0 0` — reproduces |
| `build/tmp/claude_simple_fixed` (read-side fix only, `26a0c4ad9ef`) | `dde638a7b3…` | No (built before §16 landed) | `0 0 0` — reproduces |
| `src/compiler_rust/target/debug/simple` | (built 2026-07-31 01:38 UTC) | Yes | `480 360 172800` — correct |
| `src/compiler_rust/target/bootstrap/simple` | (built 2026-07-31 06:28 UTC) | Yes | `480 360 172800` — correct |

No cargo build was run to produce this table — all four binaries already
existed on disk from prior sessions; the debug/bootstrap binaries were
picked because their mtimes postdate §16.3's landing timestamp, then
their *behavior* (not their date) was what was checked against the
probe. This satisfies the task's "no cargo builds" constraint while
still being a behavioral, non-vacuous check rather than an inference
from dates.

**Conclusion: the module-level-`val`-zeroed framing of the cell's
blocker is STALE, exactly as §16 already found.** It is fixed at
`48af531ce0e`, that commit is on origin/main, and a binary built after
it behaves correctly on both the isolated probe and (per §16.3 item 4)
the real `SHOWCASE_DIMS` chain in `examples/06_io/ui/web_render_file_gui.spl`.

**New information this pass adds, not previously on record: a
deployment gap, distinct from the source-level fix.** The binary at
`bin/release/x86_64-unknown-linux-gnu/simple` — the one `bin/simple` and
therefore any ordinary showcase invocation actually runs — is still the
pre-fix `ea4af9a449…` build (matching the `showcase_matrix_census`
report's "canonical binary: `ea4af9a4498297e3…`" as of 2026-07-30, still
current as of this check). Anyone re-running the *real* showcase via
`bin/simple run` today, without first redeploying a freshly-built
binary, will still observe `pixels=0 nonzero=0 checksum=0` — not because
the write-side defect is unfixed, but because the fix has not been
redeployed to the binary the default tool resolves to. This is a
deployment/redeploy-lane task, not a source defect, and is exactly the
kind of gap `.claude/rules/code-style.md`'s "production wrappers should
execute cached compiled artifacts, not raw source" warns can go stale
silently.

**Current actual blocker for the cell (unchanged from §16.6, still
open):** with a post-fix binary and 57-file `assets/fonts`, the real
showcase clears `blank-or-uniform` and reaches the font-identity/Draw-IR
pairing defect — `Style` computation is proven correct at
`compute_styles_with_material` (§16.4/16.5/16.6) but the wrong
(Noto-Sans-SC/16px) identity is already present in the Draw-IR command's
`computed_style` before font selection runs, localized to somewhere
between `simple_web_html_layout_renderer.spl:1482` (correct producer)
and `simple_web_html_layout_renderer_paint_layout.spl:1152` (consumer
with the wrong value), with the `draw_ir_style_props_pairing` trace
already landed and ready but not yet run to completion (§16.6's cost
wall: the module compiles in the 48-minute-plus class). Not chased
further here — out of scope for this pass, which was diagnosis of the
module-level-`val` framing only, per instruction not to attempt a fix.
