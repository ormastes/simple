# `native-build` MIR lowering fails to resolve `FileHandle` instance methods for `rt_io_file_roundtrip` — new blocker after the `File` symbol ordering/collision fix

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Summary

Follow-up to
`doc/08_tracking/bug/native_build_mir_lowering_undefined_file_symbol_2026-08-08.md`,
which is now RESOLVED (the `undefined variable: File` failure was a
Dict-method-name collision in `lower_method_call`'s dict-receiver probe, not a
cross-module lowering-order bug; fixed in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`).

With that fix landed, the `rt_io_file_roundtrip` native-build repro (same
recipe as the resolved doc, ~18 minutes to a definitive result) gets past
every `File`-class call (`File.delete`, `File.exists`) and now fails later,
on `FileHandle` INSTANCE methods instead:

```
[ERROR] MIR error: MIR lowering error: undefined variable: h
[ERROR] MIR error: MIR lowering error: unresolved method call: write_text
[ERROR] MIR error: MIR lowering error: unresolved method call: close
[ERROR] MIR error: MIR lowering error: undefined variable: h
[ERROR] MIR error: MIR lowering error: unresolved method call: read_text
[ERROR] MIR error: MIR lowering error: undefined variable: c
[ERROR] MIR error: MIR lowering error: unresolved method call: size
[ERROR] MIR error: MIR lowering error: undefined variable: n
[ERROR] MIR error: MIR lowering error: unresolved method call: close
[ERROR] MIR error: MIR lowering error: unresolved method call: merge
...
error: MIR lowering error: undefined variable: h
```

`h`/`c`/`n` are the `match ...: case Ok(h): h` / `case Ok(c): c` /
`case Ok(n): n` bindings in `main.spl` (lines 18, 43, 48) — real local
variables, not classes, so this is a different mechanism than the resolved
`File`/`Dict`-collision bug. The `write_text`/`close`/`read_text`/`size`/
`read_all`/`write_all`/`merge` unresolved-method-call errors are `FileHandle`
INSTANCE methods called on those locals (plus internal cross-method calls
inside `file.spl`'s own 31 lowered functions).

## Likely mechanism (not yet root-caused this session — filed for follow-up)

`lower_method_call`'s `Unresolved` arm (`method_calls_literals.spl`, doc
comment "Bug #138/#156 keystone") already documents this exact class of gap:
native-build never runs the HIR type-inference pass (30.types), so
`receiver.type_` is nil for ordinary locals, and instance-method dispatch
falls back to `struct_value_syms` (populated at construction/copy sites) to
recover the receiver's struct NAME. A `FileHandle` obtained via `case Ok(h):
h` from `FileHandle.open(...)`'s `Result` payload is exactly the kind of
non-construction-site binding that fallback may not cover — `struct_value_syms`
is set at explicit `StructName(...)` construction and at a few known
propagation sites (global reads, method-call results via
`remember_call_hir_return`/`remember_method_return_provenance`), but a value
extracted through a `match`/`case Ok(h)` binding on a `Result<FileHandle, E>`
is a different provenance path and may not be threaded through.

## Why this matters for the `rt_io_file_*` AOT stub question

Still genuinely UNDETERMINED under true AOT/LLVM codegen — the build now
fails one layer later (at `FileHandle` instance methods) instead of at
`File` static methods, but still never reaches codegen for this fixture.

## Next steps

1. Root-cause why `struct_value_syms` (or the `Ok(h)` match-binding's HIR
   provenance) doesn't carry the `FileHandle` struct name through to the
   instance-method dispatch site. Compare against a fixture that calls an
   instance method directly on a `FileHandle.open(...).unwrap()` chain vs.
   the `match`-destructured `Ok(h)` binding form used here, to see if the
   binding form specifically is the gap.
2. Once fixed, re-run the exact repro (or the fence script's
   `RUN_AOT_LEG=1` leg) to get the actual stub/no-stub verdict for
   `rt_io_file_*`.

## Evidence

Two independent full closure-source (`src/compiler`+`src/app`+`src/lib`)
native-build runs of `rt_io_file_roundtrip/main.spl`, both ~18 minutes,
both stopping at this exact error set after the `File`-symbol fix landed.
Not attached (large trace logs); reproducible via the recipe in the
resolved doc above.

## RESOLVED 2026-08-09b — the `undefined variable: h`/`c`/`n` half of this
## doc — root cause was a seed-interpreter bare-value-to-Option coercion bug,
## NOT a `struct_value_syms`/provenance gap

The "Likely mechanism" section above (guessing at `struct_value_syms`/
`Ok(h)` match-binding provenance) is **falsified**. Root-caused instead with
a fast, fully self-contained repro (no stdlib import, seconds not minutes):
a minimal `class FileHandle: ... static fn open(...) -> Result<FileHandle,
text>: ...` fixture reproduced `undefined variable: hh` for `case Ok(hh):
hh.fd` in ~5s under the exact same `native_build_worker.spl
--entry-closure` recipe.

Bisecting via marker-liveness `print` diagnostics through the whole
HIR->MIR pipeline (HIR pattern construction -> `HirMatchArm` push ->
`build_match_expr` -> `flatten_enum_match_arm` -> MIR's
`lower_enum_match`/`enum_pat_binding_syms`) traced the loss to a single
line in `src/compiler/20.hir/hir_lowering/expressions.spl`,
`lower_pattern`'s `Enum` arm: assigning a **bare** enum-variant value into a
`var hir_payload: HirPatternPayload? = nil` slot —
`hir_payload = HirPatternPayload.Tuple(hir_patterns)` — relies on implicit
bare-to-`Some` coercion. Under the seed interpreter
(`SIMPLE_EXECUTION_MODE=interpret`, the engine `native-build`'s own MIR
lowering runs under), that implicit coercion silently drops the payload for
an enum variant carrying an **array**-typed field: `hir_payload.?` reads
`false`/nil on the very next line, immediately after the assignment that
just built it.

**Fully isolated with a standalone, compiler-free repro** (no MIR/HIR code
involved at all):
```
enum Payload:
    Tuple(items: [i64])
fn build() -> Payload?:
    var hir_payload: Payload? = nil
    hir_payload = Payload.Tuple([1, 2, 3])
    print "{hir_payload.?}"   # prints nil/false -- WRONG, value was just set
    hir_payload
```
Replacing the assignment with an explicit `Some(...)` wrapper
(`hir_payload = Some(Payload.Tuple([1, 2, 3]))`) makes `.?` read `true`
correctly. This is a genuine seed-interpreter defect (implicit
bare-enum-to-Option coercion for an array-payload variant); per the
project's `src/compiler_rust/**` edit ban this session did not touch the
interpreter itself, only worked around it at the `.spl` call site.

**Fix**: `lower_pattern`'s `Enum` arm now wraps both payload-construction
assignments in explicit `Some(...)`:
`hir_payload = Some(HirPatternPayload.Tuple(hir_patterns))` and
`hir_payload = Some(HirPatternPayload.Struct(hir_fields))`.

**Verification**:
- Minimal fixture (`case Ok(hh): hh.fd`) now compiles clean (`EXIT=0`)
  through the full `native_build_worker.spl --entry-closure` pipeline.
- A combined regression fixture exercising BOTH this fix and the sibling
  `f33ed64bddba645c0ac0e027bfecc405e4944c5a` Dict-collision fix in the same
  program (`Thing.delete(path)` static call colliding with a real
  `Dict.delete(k)` call, plus a `match Thing.open(...): case Ok(t): t`
  instance binding) shows zero `undefined variable` errors — both fixes
  coexist without regressing each other.
- Full 18-minute `rt_io_file_roundtrip/main.spl` closure re-run (real
  `src/compiler`+`src/app`+`src/lib` source, `--entry-closure`): **zero**
  `undefined variable` errors anywhere in the log (previously the failure
  mode this whole doc is about). The build now progresses to a distinct,
  later blocker — see below.

## Progressed further, not fully resolved — the `unresolved method call`
## half is a SEPARATE, still-open issue

With the binding bug fixed, the same full 18-minute closure run now reaches
a new failure set, one layer past pattern-binding: instance-method
dispatch is still unresolved for the `FileHandle` locals the (now-working)
pattern bindings produce:
```
[ERROR] MIR error: MIR lowering error: unresolved method call: write_text (x3)
[ERROR] MIR error: MIR lowering error: unresolved method call: close (x7)
[ERROR] MIR error: MIR lowering error: unresolved method call: read_text (x2)
[ERROR] MIR error: MIR lowering error: unresolved method call: size (x1)
[ERROR] MIR error: MIR lowering error: unresolved method call: read_all (x1)
[ERROR] MIR error: MIR lowering error: unresolved method call: write_all (x1)
[ERROR] MIR error: MIR lowering error: unresolved method call: merge (x3)
error: MIR lowering error: unresolved method call: write_text
```
This matches the doc's own minimal repro too (`h.write_text(...)` /
`h.close()` on a match-bound `FileHandle` local, once binding itself
works). This is a genuinely different mechanism from the payload-binding
bug fixed above (that one was "the local doesn't exist at all"; this one is
"the local exists but its declared/erased type can't be resolved to an
`impl` owner for instance-method dispatch") and is **not fixed by this
session's change**. Filed as a fresh, narrower follow-up:
`doc/08_tracking/bug/native_build_instance_method_dispatch_unresolved_after_match_bind_2026-08-09.md`.

## Why this matters for the `rt_io_file_*` AOT stub question

Still genuinely UNDETERMINED under true AOT/LLVM codegen. The build
progressed one layer further (past pattern-binding, into instance-method
dispatch) but still never reaches codegen for this fixture.
