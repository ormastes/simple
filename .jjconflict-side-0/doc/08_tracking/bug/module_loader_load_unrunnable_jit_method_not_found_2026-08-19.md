# `ModuleLoader.load` is unrunnable on the deployed binary — `load_smf_metadata` not found

Status: OPEN (pre-existing, NOT introduced by the aspect-pack wiring change)
Date: 2026-08-19

## Symptom

Any call to `ModuleLoader.load(path)` (`src/compiler/99.loader/module_loader_compat.spl:~276`)
aborts with:

```
semantic: method `load_smf_metadata` not found on type `object`
  (receiver value: JitInstantiator(...))
```

The receiver IS a `JitInstantiator`; the interpreter simply cannot resolve a
class method on a value imported from another module. The same weakness makes
`SmfWriter`'s `me` methods unreachable (`method `add_code_section` not found on
type `object``), which is why
`compiler.backend.linker.smf_writer.smf_build_aspect_pack_image` builds the SMF
image with free byte helpers instead of driving `SmfWriter`.

## Proof it is pre-existing

With `module_loader_compat.spl` reverted to its committed content
(`git stash push src/compiler/99.loader/module_loader_compat.spl`), the
untouched existing spec fails identically:

```
bin/simple test test/01_unit/compiler/loader/module_loader_spec.spl
  -> semantic: method `load_smf_metadata` not found on type `object`
```

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59645008 bytes,
2026-08-18 10:12:23 UTC (the Rust bootstrap seed).

## Blocked specs

`test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl`
- REQ-APKW-03 (line ~108): `ModuleLoader.load` registers the aspect pack it found
- REQ-APKW-04 (line ~117): a facet routes through the catalog into the pack `load()` opened
- REQ-APKW-05 (line ~132): a module with no aspect-pack section registers nothing

These three are LEFT RED deliberately. They assert correct behaviour of the
wiring in `ModuleLoader.load`; they cannot pass until `load()` itself can run.
Their non-`ModuleLoader` counterparts REQ-APKW-06 / REQ-APKW-07 exercise the
same bridge (`smf_register_aspect_pack` -> `apk_load_facet`) and are GREEN, and
they go RED when the registration is deleted — verified by mutation.

## Unblock condition

Cross-module class-method dispatch in the interpreter (or a deployed
self-hosted `bin/simple` where it works). Re-run the spec; no spec change
should be needed.

---

## RESOLVED 2026-08-19 — root cause: duplicate type name across co-compiled modules

Status: FIXED in Simple source. **No Rust seed change needed.**

### Not a general dispatch defect

Cross-module instance-method dispatch on a `class` receiver is fine. Two
minimal fixtures both PASS on the deployed seed:

- module A `class Holder` with a `me put()` + `fn count()`, module B imports and
  calls through a field -> `count=1`, exit 0.
- module A `class Box` + separate `impl Box` block, module B imports and calls
  -> `g=7`, exit 0.

So `doc/08_tracking/bug/seed_rebuild_10_12_breaks_instance_method_dispatch_object_receiver_2026-08-18.md`
does not exist in this tree and this is **not** that defect class.

### Actual root cause

`JitInstantiator` (and `JitInstantiatorConfig`, `JitStats`, `LoadedMetadata`,
`InstantiationRecord`, `PossibleInstantiation`, `JitInstantiationResult`) were
each defined **twice** in co-compiled modules:

| name | `src/compiler/99.loader/jit_instantiator.spl` | `src/compiler/99.loader/loader/jit_instantiator.spl` |
|---|---|---|
| `JitInstantiator` | `class` + inline methods (:157) | `struct` (:147) + separate `impl` (:163) |

The interpreter's type/method registries are keyed by bare type NAME, not by
module. The constructor `JitInstantiator.new(...)` resolved to the **class** in
the top-level module (proven by the receiver dump: it shows that class's field
set, `jit_mapper: JitMapper()`), while `classes["JitInstantiator"]` had been
overwritten by the shadow module's **struct**, which carries no methods.
`impl_methods` / `GLOBAL_IMPL_METHODS` / `TRAIT_IMPLS` did not cover it either,
so the `Value::ClassInstance` arm in
`src/compiler_rust/compiler/src/interpreter_method/mod.rs:1249` fell through to
the generic tail error at `:1723`, which renders `ClassInstance` as `object`.
Hence `method X not found on type object` for **every** method, `me` and plain
`fn` alike.

Minimal reproduction (6 lines, no test runner):

```
use compiler.loader.jit_instantiator.{JitInstantiator, JitInstantiatorConfig}
fn main():
    val j = JitInstantiator.new(JitInstantiatorConfig(update_smf: false, max_depth: 4, enabled: true, verbose: false))
    print(f"stats={j.stats().cached_count}")
```
-> `error: semantic: method 'stats' not found on type 'object' (receiver value: JitInstantiator(...))`, exit 1.
Backtrace via `SIMPLE_INTERP_OOB_DEBUG=1` confirms the fall-through path.

`src/compiler/99.loader/loader/` is a stale shadow duplicate of
`src/compiler/99.loader/`. Its `jit_instantiator.spl` has **zero** external
importers (only three relative `use .jit_instantiator.*` siblings inside the
same shadow directory) — it was pure dead weight poisoning the live names.
The same hazard is already documented in `src/compiler/99.loader/object_mapper.spl:1-25`.

### Fix

Renamed the seven colliding type names in the shadow tree only, prefix `Ldr`
(`LdrJitInstantiator`, ...), across 4 files:

- `src/compiler/99.loader/loader/jit_instantiator.spl`
- `src/compiler/99.loader/loader/module_loader.spl`
- `src/compiler/99.loader/loader/module_loader_services.spl`
- `src/compiler/99.loader/loader/module_loader_lib_support.spl`

No public API changes: nothing outside that directory referenced these names by
the shadow path.

### Verdicts (binary 59695432 bytes, 2026-08-19 00:53:46 UTC, Rust seed)

- minimal repro: was exit 1 -> now `stats=0` / `ok`, exit 0
- `test/01_unit/compiler/loader/module_loader_spec.spl`: **22/22 pass**, exit 0 (was fully blocked)
- `test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl`: **7/7 pass**, exit 0 — REQ-APKW-03/04/05 now GREEN

### On the `SmfWriter` sibling symptom

`SmfWriter` is defined exactly once (`src/compiler/70.backend/linker/smf_writer.spl:201`
`class` + `:209` `impl`) — no duplicate. That shape is proven working by the
`class Box` + `impl Box` fixture above, so the `SmfWriter` report is **not** the
same root cause and needs its own reproduction. Not investigated here.
