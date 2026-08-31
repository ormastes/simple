# Self-hosted Stage-2 reads a garbage `HirType` from the symbol table — three reader fixes were all treating a symptom

- **Filed:** 2026-08-31
- **Status:** OPEN — root cause localised, not fixed
- **Blocks:** Stage-2 admission (`bootstrap_stage2_positional_stage3_route`), therefore Stages 3/4/5
- **Platform:** aarch64-apple-darwin. NOT shown to be macOS-specific.

## Symptom

The Stage-2 struct-receiver gate's positional arm fails with, repeatedly:

```
error: bootstrap MIR lowering: E-MIR-TYPE-Unknown: unreachable HirTypeKind
       disc=-1: 0 while lowering 'compiler.common.module_path_naming.*'
```

No crash — `rc=1`, clean and attributed. Arm 1
(`bootstrap_stage2_struct_receiver`) PASSES.


## CORRECTION 2026-08-31 — the title is REFUTED, and two more hypotheses are dead

**"Garbage at rest" is wrong.** A two-sided tag probe read the `HirType` graph
at both the start and the end of lowering, in the very runs that emit the error,
and found it INTACT and byte-identical on both sides in 10/10 runs. The type is
well-formed at rest; it is corrupted DURING lowering. That reclassifies this from
a bad store/bad read to a **use-after-free**, and it explains why five separate
reader-side fixes all measured inert — they were reading a value that was fine
until something else freed it.

**Refuted: `rt_core_transient_classify` fail-open.** The mechanism was real and
looked like an exact fit — `rt_core_transient_classify` returns 0 for any heap
value that is not registered-immortal, and `rt_core_transient_add` maps 0 to
success WITHOUT adding the object to the promotion plan, so a promoted parent
could keep pointing at a child the transient scope frees. Instrumented with a hit
counter and measured: **zero hits**. The path never fires on this workload. The
instrumentation was reverted rather than left in as scaffolding.

**Refuted: the count is converging.** It is not a convergence signal at all —
see the measurement below.

## Measurement 2026-08-31 (N=10, protocol-compliant)

Per-run TMPDIR and per-run cache dir, non-vacuity checked on every run
(`lines=131` and `rc=1` in all 10 — a run that compiles nothing yields ~4 lines
and would read as a false `disc=0`).

| outcome | count |
|---|---|
| `emirtype=1` | 10/10 |
| `lines=131` | 10/10 |

The error COUNT is now deterministic at exactly 1 (it was 4/8/20). What varies is
**which function** trips:

| function | runs |
|---|---|
| `module_logical_name_from_path` | 5 |
| `_module_path_naming_strip_numbered_dirs` | 3 |
| `_module_path_naming_text_index_of` | 2 |

All three are in `compiler.common.module_path_naming`, the single module the
fixture imports. Lowering that one module trips on exactly one of its three
functions, and which one depends on heap state — consistent with the
use-after-free reading: whichever function's `HirType` happens to land in freed
memory loses.

## Two vacuous-run traps caught (methodology, not incidental)

Both would have been reported as a fix if the non-vacuity check had not been
mandatory:

1. The Stage-2 gate reported `emirtype=0` in 10/10 runs. It was **`status 124`,
   a 180s timeout on arm 2** — the compiler was killed before MIR lowering
   emitted anything. Zero errors because nothing ran.
2. A 30-minute-timeout rerun reported `emirtype=0` with `lines=4`. The fixture
   `build/xfx/entry_typed.spl` had been swept — `build/` is gitignored — so the
   entry collected zero source files.

`build/` is the wrong home for a repro fixture for exactly this reason; the
durable copy now lives outside it.

## What the diagnostic still cannot say

`unreachable_hir_type_kind` guards with `type_ == nil`, but **the nil sentinel in
this runtime is raw 3**, so a ZEROED slot (raw 0) passes that test and lands in
the generic arm rendering as `disc=-1: 0` — indistinguishable from a genuine
unhandled variant. Those two have opposite fixes (repair the producer of a dead
object vs add a `lower_type` arm). `rt_heap_ref_wellformed` is the formation
probe for this raw-0-vs-sentinel class and reads only the object header, never a
field of the suspect object — which is what made an earlier attempt's five extra
field reads unsafe. Added as `E-MIR-TYPE-DeadType`; result pending a Stage-2
rebuild.

## Localisation

Every `lower_type` call site in `mir_lowering_stmts.spl` was labelled with a
module-scalar id, printed at the error site. Result was unambiguous:

```
8 occurrences, ALL site=1
```

Site 1 is the Let handler's read of the binding's declared type, originally
`self.symbols.get_symbol_type_raw(symbol_value_id)`.

## The decisive measurement

Discriminant probed immediately before and after the unwrap at that site:

```
2 runs   pre=-1            post=1984125491 / 3031551406
2 runs   pre=3031551406    post=3031551406
```

**`pre` is already garbage.** Note also that 3031551406 is not a plausible
`HirTypeKind` discriminant (the enum has on the order of tens of variants), so
the "pre valid" rows are garbage too — `-1` and a 3-billion value are just two
renderings of the same corruption.

The value is therefore corrupt BEFORE any unwrap, i.e. as it comes out of the
symbol table.

## What this refutes

Three reader-side fixes were landed against this defect on this branch. **All
three were treating a symptom** and none can have addressed the cause:

| attempt | commit | result |
|---|---|---|
| `case Some` -> `.?`/`.unwrap()` | 6d3856e6b4b | E-MIR-TYPE 20->0 **on the seed**; unrelated to the self-hosted path |
| `.unwrap()` -> `??` | 0f2bc5e6e34 | removed a SIGSEGV (real), did not touch disc=-1 |
| typed rebinds + de-box | c0bc07223ee | measured inert, A/B N=10 each |

A fourth attempt — rerouting the call site through `get_symbol_raw` so the
`HirType?` never crosses a method boundary — also measured **identical** and was
reverted rather than landed.

## Why the boundary hypothesis was attractive, and why it is not sufficient

`hir_symbol_table_methods.spl:485-491`, on the SIBLING accessor
`get_symbol_named_type_raw`, states:

> This keeps both `HirType?` and `SymbolId?` inside SymbolTable; neither
> value-type optional is safe across the staged-native method boundary used by
> nested field lowering.

`get_symbol_type_raw` returns exactly a `HirType?` across that boundary, so it
violates a constraint its own neighbour documents. That remains a real latent
defect worth fixing on its own merits. It is NOT the cause here: routing around
it changed nothing, measured.

## Where the defect must be

Between the HIR writer storing `HirSymbol.type_` and the MIR reader observing it,
in the SELF-HOSTED binary only. The Rust seed does not reproduce it: with the
seed, the same source measured E-MIR-TYPE = 0 across N=10. So this is a
stage-2-codegen defect in how a `HirType` aggregate is stored in or retrieved
from the symbol table, not a logic error in either endpoint.

## Measurement protocol note — READ THIS BEFORE CHASING COUNTS

The disc=-1 COUNT is bimodal and heap-layout dependent. Ten runs of ONE unchanged
binary produced 22 (x4), 8 (x3) and 4 (x3). A sequence of single-run counts
across builds is NOT a progress signal, and was twice misread as one on this
branch. Any claim about this defect needs per-run TMPDIR, N>=10, and COUNTS
reported rather than sequences.

## Reproduce

```sh
C=<stage2 binary>   # the lane deletes it on rejection; capture it as it is linked
RTD=build/bootstrap/stage3/aarch64-apple-darwin/stage2-runtime-authority
sh scripts/check/check-bootstrap-stage2-struct-receiver.shs "$C" "$RTD" \
   aarch64-apple-darwin cranelift
# arm 1 PASS; positional arm rc=1 with E-MIR-TYPE-Unknown disc=-1
```

---

## Session 2 (2026-08-31): a 150ms reproducer, and three more refutations

### The repro does NOT need a bootstrap. It is one command, ~150ms.

The gate script's positional arm is a single `native-build` of a **two-file**
program. Extracted, it runs in ~150ms, so N>=10 costs under two seconds and the
bimodal-count protocol is cheap to honour. Harness:
`scripts/check/check-bootstrap-stage2-struct-receiver.shs:86-105` — copy the
`env ... "$stage2_compiler" native-build ...` block verbatim. Inputs are
`scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl` (entry)
and `src/compiler/common/module_path_naming.spl` (imported).

A rebuild is needed ONLY to change compiled-in probes. Cold stage2 build is
~22 min; warm/incremental was ~90s.

Measured on a freshly captured stage2, `--backend=llvm`,
sha256 `cf46fa9474ac98daae705c5da020d0ae52a01af8d4dbb664e69b464359576651`,
139,448,872 bytes, 2026-08-31 09:20:45, per-run TMPDIR, N=12:
counts **{4 x6, 8 x3, 20 x3}** — reproducing the documented bimodality, and the
full gate on the same binary gives arm 1 PASS + 20 occurrences.

### The error message names the function. Use it.

`E-MIR-TYPE-Unknown ... while lowering '<module>.<fn>'` attributes every
occurrence. Across 12 runs the offenders were, without exception, the **three
functions of the IMPORTED module** `compiler.common.module_path_naming`
(`_module_path_naming_text_index_of` 64, `_module_path_naming_strip_numbered_dirs`
32, `module_logical_name_from_path` 12). The entry module never appeared.

### REFUTED (7): the "extra module" cross-module parameter transport

`driver_bootstrap.spl:184-190` passes each non-entry `HirModule` as a
cross-module function ARGUMENT to
`bootstrap_lower_extra_hir_module_to_mir_for_target`, while the entry module is
read from a module-global with a typed rebind. That asymmetry looks exactly like
the documented struct-argument miscompile class, so it was probed with ungated
`print` on both sides of the call plus a typed-rebind read.

**The probes never fired.** They are compiled into the binary (4 format strings
present under `strings`), so this is not muteness: that code path is not
executed at all. The bootstrap takes the **flat** path
(`bootstrap_lower_flat_hir_modules_to_mir_for_target`,
`bootstrap_globals.spl:481`), confirmed by `[bootstrap-flat-entry] index=0
modules=2 functions=1` in every log. Entry and non-entry modules go through the
*same* function there, `bootstrap_lower_flat_hir_module_to_mir(module_index, ...)`,
differing only by index and an `is_entry` flag.

### PARTLY REFUTED (8): the transient-heap promotion — streaming path only

**Scope correction (do not read this as a full refutation).** The A/B below
refutes the *streaming-surface* route. It would refute the transient-heap
mechanism outright only if the `STREAMING=0` arm ran with **no transient scope
at all**, and it does not: `rt_transient_array_scope_begin`/`_pause` are also
called from `driver_source_pipeline_parsing.spl:88,93` and
`_FlatAstBridge/module_assembly.spl:108,113`. Both arms therefore plausibly
carried the same lifetime hazard, which would make the experiment inert by
construction. Treat the transient-heap hypothesis as **open on the
non-streaming path**.

A concrete fail-open in that machinery is confirmed and still live:
`rt_core_transient_add` (`src/runtime/runtime_native.c:1987-1996`) maps
`classify == 0` to `return 1` — "not a transient node, nothing to do". A value
that fails to classify therefore has its **children never walked** while the
overall promotion still reports success. `rt_core_transient_classify` returns 0
for anything that is neither a registered raw allocation nor a registered
immortal heap object, so an unregistered aggregate silently takes its whole
subtree out of the promotion plan. That is exactly a "garbage at rest" shape.
It is not yet shown to fire here, but it is not excluded either.

#### What the streaming A/B did establish

The flat store (`_bootstrap_hir_module_functions: [[HirFunction]]`,
`lowering_helpers.spl:53`) is published per file and handed to
`_sffi_transient_heap_promote` (`:208-215`). A shallow promotion would leave
nested `HirType`s dangling — "garbage at rest", heap-layout dependent, bimodal:
a perfect fit. Two findings weaken it:

- `rt_transient_heap_promote` (`src/runtime/runtime_native.c:1998`) is **deep** —
  it builds a transitive plan across array/dict/enum/closure/raw nodes.
- Its result is checked and **fails closed** at
  `driver_hir_pipeline_lowering.spl:88-91`.

Neither is conclusive, given the `classify == 0` skip documented above: a
promotion can report success having silently walked nothing.

Empirically: A/B on `SIMPLE_STAGE3_STREAMING_SURFACES`, N=10 each, same binary,
per-run TMPDIR. `=1` -> {20,4,4,8,8,4,20,8,20,4}; `=0` -> {8,20,4,8,8,8,8,4,20,4}.
Same distribution. The toggle demonstrably took effect (12 `phase2:surface:`
lines vs 0), so this is a real negative, not a no-op experiment.

### REFUTED (9): the `Dict` bracket-read of a `HirFunction`

`entry_functions[fn_keys[fki]]` was a candidate given the recorded native-Dict
gaps — but the **entry path uses the identical bracket-read** and is clean.

### The sharpest discriminator found, and the one to attack next

"The entry module escapes because its `main()` declares no types" was the
obvious deflationary explanation. It is **wrong, and tested**: an entry module
written with fully annotated params, returns and `val`s
(`fn entry_local_helper(value: text, n: i64) -> i64` plus annotated locals),
importing the same module, produced **0 occurrences attributed to the entry
module across N=20**, while the imported module failed in **20 of 20** runs
(exactly 1 occurrence each: `_module_path_naming_strip_numbered_dirs` 9,
`module_logical_name_from_path` 6, `_module_path_naming_text_index_of` 5).
Note this fixture makes the failure **deterministic at 1/run** rather than
bimodal — further evidence that the 4/8/20 spread is a layout artefact of the
original fixture, not a property of the defect.

**Vacuous-run trap, recorded because it nearly landed in this doc.** A first
N=20 attempt reported a clean 20/20 zero. It was measuring a **deleted
binary**: the capture directory had been cleared before a rebuild, and
`timeout` reported "No such file or directory" per run while the count grep
dutifully returned 0. A zero count is only evidence if the run actually
executed a compiler — check for `[bootstrap-flat-entry]` in the log, and
`test -x` the binary, before believing any count.

So the defect is not "declared types" and not "the Let handler". It tracks
**module identity in the flat store**: `module_index == entry_index` is clean,
`module_index != entry_index` is corrupt, through the same code.

Next probe, in `bootstrap_lower_flat_hir_module_to_mir` (one build, both
questions): for each module index, print a *tag* for every function's
`return_type` and `params[i].type_` via a `match` on `HirTypeKind` (needs no
extern), and separately probe `bootstrap_flat_symbol_table(module_index)`. That
separates "row 1 of the flat store is corrupt" from "the non-entry symbol table
is". Note the entry row is published LAST but lowered FIRST — ordering between
publication and use is the untested variable.

### Protocol note

`jj restore --ignore-working-copy` silently reports "Nothing changed" against
uncommitted edits (it skips the working-copy snapshot). Remove probes by editing,
and verify with `git diff --stat` before committing.

### LOCATED (negatively): the flat store's function SIGNATURE types are healthy

A two-sided tag probe was built into stage 2 — at **publication**
(`bootstrap_hir_modules_add`, `lowering_helpers.spl`) and at **consumption**
(`bootstrap_lower_flat_hir_module_to_mir`, `bootstrap_globals.spl`), each
printing a `match`-derived tag for every function's `return_type` and every
`params[i].type_`. No extern or discriminant ABI is needed for this, which is
why it is safe to read on a possibly-corrupt object: an unrecognised kind
prints `OTHER` instead of faulting.

Binary sha256 `98dc8eb0a95f6b20...`, `--backend=llvm`, per-run TMPDIR, N=10:

```
counts   {4 x3, 8 x5, 20 x2}
OTHER    0 in every run
xpub vs xcon   byte-identical in every run
```

Representative (identical on both sides):

```
idx=0 entry=true  fn=main                                  ret=Unit
idx=1 entry=false fn=_module_path_naming_strip_numbered_dirs ret=Str p0=Str
idx=1 entry=false fn=module_logical_name_from_path           ret=Str p0=Str
idx=1 entry=false fn=_module_path_naming_text_index_of       ret=Int p0=Str p1=Str
```

So in the very runs that emit 4-20 `disc=-1` errors, every function-signature
`HirType` of the offending module is **intact at rest and intact on read-back**.

This is a strong negative and it redirects the search. The corrupt `HirType` is
not a signature type and not the flat store's `HirFunction` graph. It is
reached from inside a function BODY, or from the symbol table
(`bootstrap_flat_symbol_table(module_index)`, built from
`bootstrap_hir_module_symbol_at`) — which is where the original localisation
pointed before the reader-side fixes moved the call site. The next probe in
this series extends both sides to `HirSymbol.type_`.

### The symbol table is ALSO healthy at rest — so "garbage at rest" is the wrong frame

The probe was extended to `HirSymbol.type_` on both sides
(`[xpubsym]` in `bootstrap_hir_modules_add`, `[xconsym]` reading
`bootstrap_hir_module_symbol_at` in `bootstrap_lower_flat_hir_module_to_mir`).
Binary sha256 `258505a515c226ec...`, `--backend=llvm`, per-run TMPDIR, N=10:

```
counts                {4 x3, 8 x4, 20 x3}
xpubsym vs xconsym    byte-identical in ALL 10 runs
xpub   vs xcon        byte-identical in ALL 10 runs
```

Every symbol of the offending module carries a stable, sensible tag on both
sides — `path Str`, `value Str`, `needle Str`, `part typenil`, the three
function symbols, and the un-annotated locals (`value_len`, `start`, `offset`)
tagging `OTHER`, which is expected: they are `Infer`, and the Let handler has an
explicit `HirTypeKind.Infer` arm for exactly that.

**This is the session's most important result, and it contradicts the title of
this bug.** In the very runs that emit 4-20 `disc=-1` errors, the symbol table
and the function signatures are intact both at publication AND at the moment
MIR lowering picks them up. The value is therefore *not* garbage at rest.

That leaves one shape consistent with everything measured: the `HirType` graph
is correct when the module's lowering BEGINS and becomes garbage WHILE that
lowering runs — a use-after-free / reuse during MIR lowering, not a bad store
and not a bad read. This fits every otherwise-puzzling property: the bimodal
4/8/20 counts, per-process variation on an unchanged binary, immunity of
whichever module is lowered first (the entry), and the failure of every
reader-side fix.

It also re-opens item 8 rather than closing it, and raises the priority of the
`rt_core_transient_add` `classify == 0` fail-open recorded above, which is
precisely a mechanism for "live graph, silently never promoted".

**Next probe (designed, not yet run):** re-read the `[xcon]`/`[xconsym]` tags a
SECOND time immediately AFTER `lowering.lower_function(hir_fn)` returns for each
function, in the same run. Tags that were clean before lowering and read `OTHER`
after it localise the corruption to a specific function's lowering, and the
first index at which they flip names the culprit.

### Lane note: the rejected stage-2 binary IS preserved — no watcher needed

The advice to race a watcher against the lane is unnecessary. On rejection the
lane preserves the full candidate at
`build/bootstrap/stage2-rejected/<triple>/simple` (mode 0400) alongside
`rejection.env`; only `build/bootstrap/stage2/<triple>/simple` is removed. Copy
it and `chmod +x`. A watcher was used for the first two builds here and DIED
during the third, which is how this was found.
