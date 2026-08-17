# Bootstrap LLVM string-constant accumulator is never reset on the bootstrap object-emitter path: unit two redefines unit one's `@.str.0`

- **Date:** 2026-08-01
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Component:** `src/compiler/70.backend/backend/_MirToLlvm/class_def.spl`
  (accumulator declared in
  `src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl`)
- **Severity:** High — under `SIMPLE_BOOTSTRAP=1`, the second compilation unit
  emitted by `bootstrap_emit_real_llvm_object` /
  `bootstrap_emit_real_llvm_module_object` in one process produces LLVM IR that
  `llc` rejects outright.
- **Family:** sibling of
  `llvm_bootstrap_ir_buffer_not_reset_2026-08-01.md` (fixed
  `d5c65c647922da089a92f7048f36e7ac98d1a4d7`). Same defect class: *a
  module-level mutable global used as an accumulator, mirroring a per-instance
  field, never reset where the per-instance mirror is initialised.*

## Symptom

Unit two's emitted module carries unit one's string-constant definitions ahead
of its own. Because the naming counter `MirToLlvm.string_counter` is
**per-instance** and starts at `0` in `create()`, both units name their first
constant `@.str.0`, so the merged module defines the same global twice:

```
llc-18: error: out_mod_b.ll:14:1: error: redefinition of global '@.str.0'
@.str.0 = private unnamed_addr constant [13 x i8] c"BBB_UNIT_TWO\00"
^
```

Unit one compiles fine. Only unit two onwards is affected — which is exactly
why no single-unit test and no isolated spec could ever see it.

## Root cause

`asm_constraints_helpers.spl` declares the module-level accumulator:

```
var _llvm_bootstrap_string_global_text: text = ""
```

`MirToLlvm.add_string_global()` appends to it whenever `SIMPLE_BOOTSTRAP=1`,
alongside the per-instance mirrors `self.string_globals`,
`self.string_global_text` and `self.string_counter`. All three per-instance
mirrors are freshly initialised in `MirToLlvm.create()` and
`MirToLlvm.create_baremetal()` (`string_globals: []`, `string_global_text: ""`,
`string_counter: 0`). The global was not.

A reset *did* exist — `llvm_bootstrap_string_globals_reset()` at the top of
`MirTextCodegen::translate_module` (`core_codegen.spl:166`) — but the bootstrap
object emitters never go through `translate_module`. Both
`bootstrap_emit_real_llvm_object` (`driver_bootstrap.spl:334`) and
`bootstrap_emit_real_llvm_module_object` (`driver_bootstrap.spl:443`) drive
`emit_module_header()` + `emit_runtime_declarations()` +
`translate_function()` directly and then call `bootstrap_emit_llvm_trailer()`,
which reads `llvm_bootstrap_string_globals_text()` unconditionally. On that path
the reset never runs.

This is the identical mistake as the IR-text buffer: the reset was attached to
*one* code path rather than to the object lifecycle it mirrors.

## Fix

Reset the accumulator in `MirToLlvm.create()` and
`MirToLlvm.create_baremetal()` — the same place the per-instance
`string_global_text` / `string_counter` mirrors are initialised, so the two can
no longer drift apart. `translate_module`'s existing reset is left in place: it
is now redundant but harmless, and removing it would re-create the
"reset lives on one path only" hazard from the other direction.

Bare metal is unaffected: `emit_baremetal_attributes()` queues into the
per-instance `pending_baremetal_attrs`, never into a string global.

## Evidence

Two-unit harness, `SIMPLE_BOOTSTRAP=1` set in-process via `rt_env_set`, both
units built through `MirToLlvm.create` + `add_string_global` +
`bootstrap_emit_llvm_trailer`-equivalent trailer + `builder.build()`.

**Lane: interpreter.** The JIT declined the module
(`unresolved external symbol 'MirToLlvm_dot_create': whole module dropped to
the interpreter`) and fell back, so this evidence covers the pure-Simple source
executed by the tree-walking interpreter. JIT and native lanes are **not**
covered by this probe.

Reverted (defect present):

```
after_b_decls=2            unit two's buffer holds TWO decls
after_b_has_AAA=true       unit two carries unit one's constant
instance_b_decls=1         per-instance mirror is CORRECT
instance_b_has_AAA=false
llc-18 mod_a  rc=0   nm: 0000000000000000 T mod_a
llc-18 mod_b  rc=1   error: redefinition of global '@.str.0'   nm: no T mod_b
mod_b IR size 398 bytes
```

Applied (defect fixed):

```
after_b_decls=1
after_b_has_AAA=false
after_b_has_BBB=true
llc-18 mod_a  rc=0   nm: 0000000000000000 T mod_a
llc-18 mod_b  rc=0   nm: 0000000000000000 T mod_b
mod_b IR size 329 bytes
```

The verdict is `llc` **rc=0 plus `nm` showing `T mod_b`** — a positive artifact,
not a clean exit.

## Regression test

`test/unit/compiler/backend/llvm_bootstrap_accumulator_reset_spec.spl`

Every case builds **two** translators in one process; a single-unit test cannot
detect this class of defect. The spec also pins the per-instance mirror as
unit-local, so a future change cannot make the global right by making the
instance field wrong, and re-covers the already-fixed IR-text accumulator
(`source_filename` / `target triple` must appear exactly once in unit two).

Non-vacuity for the IR-text case was shown the same way: with the landed
`d5c65c647922` reset removed, unit two reports
`source_filename=2, target triple=2, contains mod_a3=true`; with it restored,
`1, 1, false`.

## Enumeration note

A mechanical sweep of `src/compiler/**` and `src/runtime/**` found **644**
module-level `var` declarations, of which **3** are text-typed self-appending
accumulators:

| global | file | verdict |
|---|---|---|
| `_llvm_bootstrap_ir_text` | `70.backend/backend/llvm_ir_builder.spl` | defect — fixed `d5c65c647922` |
| `_llvm_bootstrap_string_global_text` | `70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl` | defect — fixed here |
| `cg_output` | `10.frontend/core/compiler/cg_helpers.spl` | correct — `cg_reset()` is called by its single consumer `c_codegen.spl:751` before it emits, and `cg_output_get()` reads at `:771` in the same function |

The text-accumulator subfamily is therefore closed.
