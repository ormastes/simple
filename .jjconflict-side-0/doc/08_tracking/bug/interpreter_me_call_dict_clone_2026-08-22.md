# Seed interpreter: every `me` call deep-copies each Dict field the method writes

**Date:** 2026-08-22
**Area:** Rust seed interpreter — `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`,
`interpreter/expr/calls.rs`, `interpreter_method/special/execution.rs`
**Status:** FIXED (MECALL-OWNED) — pinned by
`test/01_unit/compiler/interpreter/me_call_dict_field_write_cost_spec.spl`
**Filed from:** the enum-lowering target of the run7 stage1 HIR profile
(`enums = 22,168 ms / 163 lowerings = 136 ms each`; `tokens.spl` at 130.9 s vs an
11.5 s/module mean; HIR cost degrading 11 s -> 79 s per module as the run proceeds)

## What was measured

Synthetic enum module (N enums x 10 unit variants, `native-build --threads 2`,
`SIMPLE_HIR_PHASE_PROFILE=1`, deployed seed `bin/release/x86_64-unknown-linux-gnu/simple`
of 2026-08-21 22:35): N=40 -> `enums=1828ms` (46 ms/enum), N=160 -> `enums=8269ms`
(52 ms/enum), `ARR_MUT_COW_ELEMS_CLONED` 10,993 -> 139,753 (12.7x for 4x N).

A `bin/simple run` probe calling the REAL `SymbolTable.define` 4000 times in
one process (blocks of 1000): 2431 / 4522 / 6534 / 8326 ms. Per call cost is
linear in the table already built, and `VT_OBJECT_FIELD_CLONES` = 1 per call.
Nothing in `define` is algorithmically O(n) — `SCOPEIP` (d954bcf0d5d) already
writes the scope row in place — so the term had to be in the interpreter.

Bisected with a four-shape probe, all interpreted (3000 inserts each):

| shape | ms |
|---|---|
| `t.ints[i] = i` directly in the caller | 10 |
| `t.put(i)` — one `me` call per insert | 535 |
| 3000 inserts inside ONE `me` call | 10 |
| `via_fn(t)` then `t.put(i)` per insert | 391 |

And per block of 1000 `me` calls writing a `Dict<i64,i64>` field: 33 / 89 /
155 ms. The write is free; the CALL BOUNDARY costs O(|dict|).

## Root cause

For a `Value::Object` receiver (every user `class` and `struct` in the
interpreter — `Value::ClassInstance` is only produced by the value bridge) a
`me` call binds `self` as an Object sharing the receiver's field-map `Arc`.
`find_and_exec_method_with_self_owned` was added to move the map in with
refcount 1, but its only caller (`patterns.rs`, statement context) had to
RE-INSERT a clone of the receiver into `env` so that argument expressions such
as `me.field` could resolve inside `bind_args` (bug 2026-06-11). That clone put
the refcount back to 2, so the first `self.dict[k] = v` in the body hit the
copy-on-write path (`Arc::make_mut` on a shared Dict = full deep copy), after
which the env-local `self` was unique and later writes in the same call were
in place. Expression-context calls (`val x = obj.m(..)`) and field receivers
(`self.symbols.define(..)`) never had an owned path at all: they evaluated the
receiver to a clone, or copied the field into a temp binding.

`SymbolTable.define` writes `symbols`, `exact_symbols` and the scope row per
call; `lower_variant` calls it once per variant; `register_imported_symbol`
and the field/method/payload materializers are all `me` methods writing
dicts. Every one of them paid a copy of the dict it touched, per call, which
is why HIR cost grows with everything accumulated so far.

## Fix (MECALL-OWNED)

`exec_function_with_self_return_values` / `find_and_exec_method_with_self_owned_values`
(`execution.rs`): same as the existing owned path but take PRE-EVALUATED
argument values (`bind_args_with_values`), so nothing needs the receiver to
stay bound while the callee runs. Four call sites evaluate the args with the
receiver in place, then MOVE the receiver (or the field Object) into the
callee and store the returned self back:

- statement `obj.m(..)` — `patterns.rs` (the re-insert is gone)
- expression `obj.m(..)` — `interpreter/expr/calls.rs` identifier receiver
- statement `parent.field.m(..)` — `patterns.rs`
- expression `parent.field.m(..)` — `interpreter/expr/calls.rs`

Each site checks `object_method_exists` BEFORE taking the receiver, so lambda
fields, `method_missing` and UFCS keep their existing paths. Value semantics
are preserved: a receiver that genuinely has a second owner (another variable,
a shared-layer global) still has refcount > 1 and still copies on write; only
the interpreter's own temporary was removed. Losing the binding when the callee
returns `Err` is unobservable — `TryError` unwinds to the enclosing function
boundary (`extract_block_result`) and every other `CompileError` aborts the run.

## After

(filled in below from the rebuilt seed)

Same probes, seed rebuilt from this tree (`cargo build --release --bin simple -j2`):

| probe | before | after |
|---|---|---|
| 3000 `me` calls each inserting one key (stmt ctx) | 535 ms | 30 ms |
| same via a fn-arg receiver | 391 ms | 49 ms |
| real `SymbolTable.define`, blocks of 1000 | 2431 / 4522 / 6534 / 8326 ms | 1469 / 1539 / 1705 / 2833 ms |
| real `lower_enum` (10 variants), blocks of 100 | 2686 -> 12265 ms (grows 4.6x) | 950-1600 ms, flat |
| synthetic N=160 module, `[hir-prof] enums=` | 8269 ms | 1957 ms |
| synthetic N=160 module, HIR `total=` / wall | 38,131 ms / 225 s | 14,425 ms / 106 s |

The growth law is gone (block 8 of `lower_enum` costs what block 1 does); the
remaining ~1.3 ms per `define` is flat interpreter overhead, not a copy.
`test/01_unit/compiler/interpreter/me_call_dict_field_write_cost_spec.spl`
(mirrored in `test/unit/`) fails on the old seed (block 4 = 7x block 1) and
passes on the new one.

Regression sweep, one file at a time on the new seed: all 23 files under
`test/01_unit/compiler/interpreter/` plus `class_reference_semantics_spec.spl`
and the two HIR cost specs — 66 PASS / 26 FAIL, and every one of the 26 also
FAILs on the pre-change seed from the same tree (pre-existing, not introduced
here).

## Still open

The real-closure `[hir-prof]` numbers (136 ms/enum, 402 s imports) are owed a
re-measure once this seed is deployed; the mechanism (one deep copy per
`me`-call per dict written) applies to every HIR `me` method, so the import
registration sub-phases should move too.
