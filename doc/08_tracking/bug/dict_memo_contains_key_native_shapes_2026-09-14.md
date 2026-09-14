# Dict memo `contains_key` under-reporting: what the native lanes actually show (2026-09-14)

- Status: OPEN — premise of PR #987 PARTLY CORRECTED; the Stage-2 candidate
  cannot answer the question because it SEGVs on any class-with-a-method.
- Lane: F77 (`work/f77-dict-contains-native-2026-09-14`)
- Scope: this doc answers "is `rt_dict_contains` under-reporting?" with measurements.
  It does not touch `src/compiler/20.hir/**` (owned by a sibling lane).

## What PR #987 asserted

Stage 3 SEGVs at 13,415 recursion levels in the four-symbol cycle
`register_imported_symbol -> register_imported_symbol_inner ->
register_materialized_enum_payload_dependencies ->
register_materialized_payload_named_dependency -> register_imported_symbol`.
Since `hir_payload_terminal_identity` is pure and the memo
`materialized_payload_origins` marks ON ENTRY, the ceiling should be 2,546
distinct identities; 13,415 > 2,546 was read as proof that
"keys that were set are reading back absent", i.e. `rt_dict_contains`
under-reporting.

## Correction 1 — there are TWO gates on that cycle, not one

Read at `c56dd5004af`:

- `module_reexport_materialization.spl:563-566`
  (`register_materialized_enum_payload_dependencies`) is genuinely
  mark-on-entry. #987's arithmetic applies to it.
- `module_reexport_materialization.spl:~524-537`
  (`register_materialized_payload_named_dependency`) is **not** a gate at all:
  it computes `val expanded = self.materialized_payload_origins.contains_key(identity)`,
  then calls `self.register_imported_symbol(...)` — the recursive edge —
  **unconditionally and before** `self.materialized_payload_origins[identity] = true`.
  Read-then-recurse-then-set.
- `module_import_registration.spl:363-367` carries a **second, independent**
  gate that #987 does not mention:
  `if materialize_enum and not self.imported_enums.contains_key(local_name):`
  ... `self.imported_enums[local_name] = ...` ...
  `self.register_materialized_enum_payload_dependencies(...)`.

For 13,415 levels, BOTH surviving gates must read absent ~11k times. Both are
`{text: X}` **class fields of `HirLowering`, written inside a `me` method,
immediately before the recursive descent** — the same shape as the probes in
`stage2_native_class_field_text_dict_owner_lost_2026-09-14.md`. That narrows
the hypothesis from "text hashing" to "a method-scoped class-field write is not
visible to a later read".

## Correction 2 — the seed and the interpreter are clean on every shape tried

Six shapes, now pinned as
`test/01_unit/lib/common/dict_native_shape_differential_spec.spl` and driven by
`config/check/native_interp_differential_dict_shapes.txt`:

| row | shape | interpreter (seed) |
|---|---|---|
| a | module-`var` `{text: bool}`, set+`contains_key` in a plain loop, 2000 keys (past the 8/16/64/1024 rehash thresholds), plus a full re-read pass | PASS, 0 misses |
| c | key by concatenation vs interpolation vs a pure `(text,text,text)` fn — the `hir_payload_terminal_identity` shape | PASS, one identity, 300 entries |
| b | module-`var` mark-on-entry memo + recursion | PASS, visits == memo.len() == 7 |
| e1 | class-field memo written inside a `me` method + recursion through methods | PASS, visits == memo.len() == 7 |
| e2 | class-field `{text:text}` / `{text:i64}` / `{text:Struct}` value read-back after a method write, then 1500 keys | PASS, 0 misses, 0 bad values |
| f | dict passed as an argument: callee sees caller's entries, caller sees callee's write | PASS |

Measured on the Rust seed `build/cargo-r2/release/simple` (v1.0.1-beta.1,
2026-09-14) under `SIMPLE_EXECUTION_MODE=interpreter`. **No divergent row was
found on the interpreter oracle.** The native half of the differential is
unmeasured here: the seed's `native-build --mode=dynload` of the spec did not
complete inside 25 minutes on this host, and is left to
`check-native-interp-differential.shs` running the curated file above.

## Correction 3 — the Stage-2 candidate cannot be used as evidence at all

The pinned Stage-2 candidate
(`.claude/worktrees/agent-a61ab2c0a64b5f2cf/.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple`,
139,504,312 bytes, 2026-09-13 22:45) **SEGVs while COMPILING** every program
that declares a class with a method. Measured, rc read into a variable on the
line after the invocation, never through a pipe:

| fixture | content | `native-build` rc |
|---|---|---|
| `m5.spl` | `fn main(): print("m5=ok")` | **0** (and the binary runs) |
| `m4.spl` | `class Box: n: i64` + `me get() -> i64: return self.n` — no dict anywhere | **139** |
| `m3.spl` | class with a dict field, method touches only the `i64` field | **139** |
| `m2.spl` | class-field dict, method only READS it | **139** |
| `m1.spl` | class-field dict, method reads and WRITES it | **139** |

`m4.spl` verbatim — nine lines, no dict, rc 139:

```simple
class Box:
    n: i64

    me get() -> i64:
        return self.n

fn main():
    var b = Box(n: 7)
    print("m4=" + b.get().to_text())
```

Invocation (rc captured on the next line, never through a pipe):

```
SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 timeout 600 \
  <stage2-candidate> native-build m4.spl -o m4_s2 >/tmp/m4.log 2>&1
echo "M4_RC=$?"      # -> 139
```

So the companion record's attribution ("method-scoped dict field write
segfaults") is too narrow by a wide margin: nine lines with no dict at all are
enough. This binary cannot compile the Dict reproducer, and therefore cannot
testify about `rt_dict_contains` either way.

### Root cause of that compile-time SEGV — fixed here

Identical crash site for `m1`..`m4`, under lldb:

```
stop reason = EXC_BAD_ACCESS (code=1, address=0x48)
frame #0: simple`compiler__mir___MirLowering__module_lowering__MirLowering
            .record_external_layout_reference + 204
->  0x1002d6970 <+204>: ldr  x0, [x26, #0x48]
    0x1002d6974 <+208>: bl   rt_native_neq
```

`code=1` at the small address `0x48` is a field read off a **nil** receiver, not
a stack overflow. `src/compiler/50.mir/_MirLowering/module_lowering.spl:438`:

```
val symbol_info = self.symbols.get_symbol_raw(symbol.id)
if not symbol_info.?:
    return
val info = symbol_info.unwrap()
var owner = mir_layout_canonical_module_name(info.defining_module ?? "")   # <- faults
```

`Option<...>`'s nil case does not survive the staged native ABI — `.?` reads
PRESENT for an absent symbol, so `unwrap()` yields nil. This is a hazard the
repo has already documented twice, in this very file (`mir_struct_symbol_name`,
~40 lines below, guards `if info != nil and info.name != ""` and explains that
`canonical_mir_type_symbol` mints ids `get_symbol_raw` knows nothing about) and
in `module_import_registration.spl` ("it builds an `Option<SymbolId>`, and that
Option's nil case does not survive the staged native ABI -- it reads as PRESENT
even when the name is unbound"). `record_external_layout_reference` is the one
call site that never applied it.

**Fix:** the same `if info == nil: return` guard, at the defect's layer
(`50.mir`), before any field read. Pinned by
`test/01_unit/compiler/mir/external_layout_reference_nil_info_guard_source_spec.spl`
(GREEN on the seed interpreter, 1 example). Not a workaround in a caller: the
callee is what fails to apply its own file's documented mitigation.

**Not verifiable natively from here.** Confirming the fix clears the rc-139
requires a rebuilt Stage-2 candidate, which is a bootstrap run this lane did not
have. The RED evidence above is exact and reproducible with the five fixtures.

## Standing conclusion on `rt_dict_contains`

Nothing measured in this lane implicates the C runtime or its Rust twin. The
seed and the interpreter agree on all six shapes, and the binary that produced
the 13,415-level stack cannot be interrogated because it dies earlier, for an
unrelated reason now fixed. The honest state is: **the `rt_dict_contains`
under-reporting premise is unproven, and the two prior records cited for it
(`dict_class_field_contains_key_after_insert_2026-08-08.md`, CLOSED as not
reproducible; `stage3_register_imported_type_methods_infinite_recursion_2026-08-17.md`,
a different cycle) do not carry it either.** The next measurement that would
settle it is `check-native-interp-differential.shs --specs-file
config/check/native_interp_differential_dict_shapes.txt` on a host where the
native lane completes, and a re-run of the five rc-139 fixtures against a
Stage-2 candidate rebuilt from this fix.

## PR #987's breaker

**Keep it.** It is the only guard on that cycle that is NOT shaped like the
suspect construct — a plain `[text]` stack, not a class-field dict — and it is
cheap. It is not redundant on any evidence gathered here, and would only become
so once a native lane demonstrates that the two class-field gates read back
correctly.
