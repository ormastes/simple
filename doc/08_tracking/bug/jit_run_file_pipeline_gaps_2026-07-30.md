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
