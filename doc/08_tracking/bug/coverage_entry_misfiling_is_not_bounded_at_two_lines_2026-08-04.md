# Coverage `<entry>` misfiling is not bounded at "<=2 lines (<=0.9%) per module" — it swallows method bodies too, up to 21 points

- **Filed:** 2026-08-04
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Direction:** under-reports. A published number is a floor, never flattering.
- **Supersedes:** the RESIDUAL note in `src/app/test_runner_new/test_runner_single.spl`,
  which states the residual is "module-level recordable statements ... <=2 lines
  (<=0.9%) in each of the eight browser-engine campaign modules".

## Summary

`span_to_location` (fixed by `27f864e35e8` to stamp `CURRENT_EXEC_MODULE` on each
recorded line) falls back to the `"<entry>"` sentinel whenever the owning module
is unknown. The residual was documented as affecting only *module top-level*
statements, which the flatten path hoists into the entry program.

It also affects **ordinary instance-method bodies**, and the amount is not
small. The reporter deliberately refuses `<entry>` hits for a target file — the
right call, since accepting them would re-pool every module and reintroduce
defect D — so those executed lines read as uncovered.

## Proof (airtight, single module in the run)

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_node_mutation_spec.spl`
loads exactly one product module, `dom.spl`. Its coverage dump records only two
file keys: the absolute path of `dom.spl`, and `<entry>`. Lines recorded under
`<entry>` in that run:

```
<entry> 375   set_attr        if name == "src":
<entry> 384   remove_attr     if name == "src":
<entry> 399   set_style       val p = prop.trim().lower()
<entry> 400   set_style       val v = value.trim()
<entry> 402   set_style       self.style.display = v
<entry> 404 406 408 410 412 414 416 418   set_style   the other eight arms
```

There is no other module in the run those lines could belong to. All of them
are `me` method bodies inside `impl BeDomNode:` — none is a module top-level
statement. Line 375 is recorded under **both** keys in the same run, so the
attribution is not even stable per line.

Independent confirmation that the lines really execute and really are tested:
sabotaging line 402 (`self.style.display = v` -> `= "SABOTAGE"`) turns the spec
RED with

```
✗ sets every named inline style property
  expected SABOTAGE to equal flex
✗ ignores an unrecognised style property
  expected SABOTAGE to equal block
```

A line that a mutation test can kill is, by definition, covered. The reporter
says it is not.

## Measured size, full-corpus union, 273 specs

`floor` is what the reporter prints. `ceiling` adds back every uncovered line
whose enclosing function WAS called and whose line number appears under
`<entry>`; it is an upper bound, since an `<entry>` hit at line N could in
principle have come from another file in a multi-module run.

| module | floor | ceiling | lines lost |
|---|---|---|---|
| `dom_limits.spl` | 0% (0/2) | 100% (2/2) | 2 |
| `dom.spl` | 79% (63/79) | 100% (79/79) | 16 |
| `..._paint_tiles.spl` | 93% (139/149) | 100% (149/149) | 10 |
| `..._declarations.spl` | 79% (575/725) | 88% (642/725) | 67 |
| `..._engine2d_presenter.spl` | 86% (283/327) | 93% (307/327) | 24 |
| `..._decl_apply.spl` | 70% (1313/1870) | 75% (1408/1870) | 95 |
| `..._style.spl` | 64% (250/386) | 71% (277/386) | 27 |
| `dom_identity_index.spl` | 94% (222/234) | 99% (232/234) | 10 |
| `html_tokenizer.spl` | 97% (377/386) | 99% (383/386) | 6 |
| `style_block_parse.spl` | 97% (478/488) | 99% (485/488) | 7 |

21 points on `dom.spl` and 100 points on `dom_limits.spl`, against a documented
bound of 0.9%. `dom_limits.spl` is the extreme case: its only two recordable
lines are the module-level `val HTML_MAX_TREE_DEPTH` / `val HTML_MAX_NODES`, so
the module is **not measurable at all** by this instrument and reports 0%
however thoroughly it is used. Any past claim that `dom_limits.spl` was at 100%
came from defect D's cross-file pooling, not from a real measurement.

## Consequences

1. Every browser-engine coverage figure published today is a floor with a real
   band above it, and the band is up to 5 points on the large renderer modules
   and 21 points on `dom.spl`. Single-figure reporting is false precision.
2. A module can be pushed from "below 90%" to "above 90%" purely by fixing this,
   with no test written. `dom.spl` is exactly that case: 79% measured, 100%
   real, verified line by line.
3. The fix is the one the existing note already names — carry the owning module
   through the flatten path into execution — and the note's warning still
   stands: do NOT "fix" it by accepting `<entry>` hits for a target file, which
   would re-pool every module and reintroduce defect D.

## Where to look

`CURRENT_EXEC_MODULE` is saved/restored around `execute_function_body`
(`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`) and
read by `span_to_location`
(`src/compiler_rust/compiler/src/interpreter/coverage_helpers.rs`). Methods
reached through the `impl` dispatch paths appear not to have an owner set, and
line 375 being filed under both keys in one run suggests the owner is restored
to `None` while a body is still executing rather than never being set at all.
