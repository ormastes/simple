# Stage 3 self-host: `rt_clear` had no Dict branch, so every `Dict.clear()` was inert

- **Status:** FIXED 2026-08-17 (both runtimes), guarded.
- **Guard:** `scripts/check/check-dict-clear-receiver-dispatch.shs`
- **Layer:** native runtime receiver dispatch (NOT Dict bracket-read codegen).

## Root cause (measured)

The native codegen dispatch tables (`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1811`,
`codegen/instr/calls.rs:3491`) route **every** `.clear()` to the single symbol
`rt_clear`, keyed on the method NAME with **no receiver type**. `rt_clear` was
receiver-dispatched for Array and text only — it had **no Dict branch**:

- `src/runtime/runtime_native.c:7867` (C runtime, the `core-c-bootstrap` bundle the bootstrap links)
- `src/compiler_rust/runtime/src/value/collections.rs:3207` (Rust runtime, JIT + native-all)

A dict receiver therefore fell through to `rt_refuse_non_text_receiver`
(`exit 70`, "str.clear was called on a receiver that is not text … a
code-generation dispatch gap"). Before that loud refusal was added it was a
**silent no-op**.

## Why it decided symbol resolution compiler-wide

`SymbolTable.reset_module()` (`src/compiler/20.hir/hir_types.spl:242`) is the
per-module reset: **eight `Dict.clear()` calls plus two scalar resets**
(`next_symbol_id = 0`, `next_scope_id = 1`). The dict clears did nothing; the
scalar resets took effect. So symbol **names** from every previously-lowered
module survived into the next module while symbol **ids** restarted at 0, and
`lookup_or_invalid(name)` returned a **stale** id the new module had already
reused for an unrelated symbol. That is the entire Stage 3 "enum payload
dependency `X` resolved to non-type binding `Y`" family.

`HirLowering.begin_module()` (`20.hir/hir_lowering/types.spl:283`) is built out
of 15 further `Dict.clear()` calls and was inert for the same reason.

## The trace that localised this, and the inference that was wrong

The stage-3 diagnostic trace showed **133 (key,id) pairs for 132 keys** (step 1
is a function) against **1,136 (id,sym_name) pairs for only 120 distinct ids**
(~9.5 records per id), in a narrow low id band 1..1873. That was read as
"the id is right, the FETCH is wrong ⇒ native Dict bracket-read defect".

**That inference does not hold.** A third explanation was not considered: the
table is legitimately reset per module, so id 1 belongs to a *different* symbol
in every module. Aggregating a whole-run trace across ~1,500 modules produces
exactly the observed statistics — including the narrow low band (ids restart at
0) and the foreign `compiler.driver.*` names (other modules' symbol #1). The id
was **stale**, not the fetch.

The bracket read was **measured correct**: a native ELF built from a class with
a `Dict<i64, SomeClass>` field, read as `obj.field.dict[k]` through two chained
`self`-style hops, returned all 8 key-differentiated records correctly under
native, JIT, and interpreter. `hir_payload_kind_is_type` and the owner-conflict
test are likewise not implicated.

## Reproduction (small)

Any `.clear()` on a dict, local or class-field, text- or int-keyed:

```
fn probe_local():
    var d: {text: i64} = {}
    d["x"] = 1
    d.clear()
    print("LOCAL_TEXTKEY len=" + d.len().to_text())
```

Built with `SIMPLE_NATIVE_BUILD_RUST=1 bin/simple native-build --backend
cranelift --entry clr2.spl -o clr2` — the same Rust native-build handler
bootstrap stages 2 and 3 use.

## Ablation (distinct binaries, md5-proven)

| arm | md5 | result |
|---|---|---|
| reverted | `1abd9ef76214a06acaf0a281c81c6be4` | `exit 70`, `str.clear was called on a receiver that is not text` — no probe line printed |
| applied | `fc9a0700d7ad4ed1498e23f1944f0ea1` | `exit 0`, `LOCAL_TEXTKEY len=0 / LOCAL_INTKEY len=0 / FIELD_INTKEY len=0 / FIELD_TEXTKEY len=0` |

And on the exact `reset_module()` shape (aliased root-scope dict + `Dict<i64,
Scope>` + `Dict<i64, Scope>`), reverted `545f52b6e2eea4ba962691368a07bd11`
vs applied `a81d60e83e098444357310494e58ba1f`:

```
M1    root_len=1 scope0_len=1 has=true
AFTER root_len=0 scope0_len=0 has=false symlen=0
```

The guard's own `--selftest` reproduces the same ablation on the C runtime and
is fatal; its verdict line today is verbatim:

```
PASS — 3 case(s) checked, Dict.clear() empties the dict and the array control still holds
```

## Prior art

The pure-Simple MIR lowering
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1620`) had
already reached this exact diagnosis and fixed its half by emitting
`rt_dict_clear` directly. That fix does not reach the bootstrap, which runs the
**Rust** native-build handler (`SIMPLE_NATIVE_BUILD_RUST=1`,
`src/compiler_rust/driver/src/main.rs:160`) and so still routed `.clear()` to
`rt_clear`. Both runtimes now carry the Dict branch, following the three-way
receiver-dispatch pattern `rt_index_get` (immediately below `rt_clear` in the C
runtime) already used.

## Not verified

The full stage-3 replay was **not** re-run for this change. The free regression
oracle (a deterministic 2,723,463-byte log with 7,069 errors) should shift; that
is a prediction, not a measurement.
