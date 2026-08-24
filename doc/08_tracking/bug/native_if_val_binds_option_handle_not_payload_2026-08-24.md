# `if val x = opt:` binds the Option HANDLE, not the payload (native lane)

**Date:** 2026-08-24
**Status:** RESOLVED 2026-08-24 — fix landed in `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`; gate GREEN (see "Resolution")
**Severity:** Critical — silent-wrong values, escalating to SIGSEGV in the self-hosted compiler
**Lane:** V

## Symptom

479 of 760 compiler files in the lane-Q sweep ledger
(`/mnt/data/goal-logs/laneq/results.tsv`, column 3 = `rc`) exit **139
(SIGSEGV)** when compiled by the stage2 binary. The task framing named 152
files (136 slice A + 16 slice B); the ledger read here shows 479 rc=139 rows.
Both numbers are reported; the reproducer below is drawn from the rc=139 set.

Every crash is at the same instruction:

```
#0 compiler__hir__hir_lowering___Items__declaration_lowering__HirLowering.lower_function
#1 ...module_build__HirLowering.lower_module
#2 ...module_build__HirLowering.lower_parser_module_unstub
#3 ...driver_hir_pipeline_lowering__CompilerDriver.lower_and_check_impl
```

## Mechanism (verified in gdb, not inferred)

Crash site disassembly (`lower_function+4194 .. +4251`):

```
call  SymbolTable.get_symbol_type      ; -> rbx  (declared HirType?)
call  rt_is_some                       ; -> TRUE, branch taken
call  rt_enum_payload                  ; -> 3 (RT_NIL): the arg is NOT an enum
and   $0xfffffffffffffff8,%rax         ; 3 & ~7 == 0
mov   (%rax),%rbx                      ; <-- SIGSEGV, deref NULL
```

Probed live: `rt_enum_id(rbx) = -1`, `rt_enum_discriminant(rbx) = -1`,
`rt_enum_payload(rbx) = 3`. So the value handed to `.unwrap()` was neither a
valid Option nor nil — it was garbage that `rt_is_some` cannot reject (it is
neither the nil sentinel nor an enum-id-1 `None`).

Where the garbage is produced — `SymbolTable.get_symbol_type_raw`
(`src/compiler/20.hir/hir_symbol_table_methods.spl:391`):

```
val sym = self.get_symbol_raw(raw)
if val found = sym:          # <-- `found` is bound to the OPTION HANDLE
    if found != nil:
        found.type_          # <-- reads a field off the enum header
```

`if val` on the native lane emitted a verbatim copy of the subject into the
binder. That is correct for the raw "migration form" of `T?` (the bare value,
nil when absent) but wrong for the CANONICAL boxed `Some(v)` enum, which is
what `Some(...)` construction and every `T?`-typed field initialised with
`Some(...)` produce. The binder therefore held the Option object, and
`found.type_` read the enum header instead of the payload.

## Minimal reproducer (4 relevant lines, silent-wrong — no crash needed)

`bin/simple native-build` of:

```
struct Payload:
    tag: i64

fn main():
    val p = Payload(tag: 99)
    eprint("0 direct tag={p.tag}\n")       # 99   correct
    val d: Payload? = Some(Payload(tag: 33))
    eprint("4a is_some={d.is_some()}\n")   # true correct
    if val e = d:
        eprint("4 local tag={e.tag}\n")    # 4    *** WRONG, expected 33 ***
    eprint("5 unwrap tag={d.unwrap().tag}\n")  # 33 correct
    match d:
        case Some(m): eprint("6 match tag={m.tag}\n")   # 33 correct
```

`.unwrap()` and `match ... case Some(x)` are BOTH correct — they carry the
dual-representation handling added by
`native_optional_tuple_payload_extraction_broken_2026-07-29`
(`hir/lower/stmt_lowering.rs:1400`). Only the `if val` binder was missed. The
tree-walking interpreter was always correct, so this reproduces only on a
native build.

The compiler-scale crash is the same defect one hop later: the garbage value is
returned as a `T?`, the caller's `rt_is_some` accepts it, and its `.unwrap()`
lowers to a bare `rt_enum_payload` whose non-enum result is dereferenced.

## Correction: which compiler emits this

The first fix attempt patched the **Rust seed**'s HIR lowering
(`hir/lower/stmt_lowering.rs`). That was wrong, and the error is worth
recording because it is easy to repeat: `bin/simple native-build` does NOT use
the seed's Rust codegen. It runs the **pure-Simple compiler**
(`src/compiler/**`) under the seed's interpreter — the build log names
`src/compiler/70.backend/backend/mir_to_llvm.spl`, and a seed rebuilt WITH the
Rust fix produced a **byte-identical** output binary (`cmp` says identical, 7
`rt_is_some` call sites either way) and the same wrong values. The Rust change
was reverted rather than landed unverified; the analysis is kept here because
the seed's `if val` binder has the same shape and is a candidate defect on
whatever lane does use it.

## Where the payload extraction is actually lost

The parser marks an `if val` binding with a dedicated AST flag:
`stmt_if_val_decl` sets `stmt_if_val_marker[idx] = true` /
`stmt_i64_set(idx, "IF_VAL", 1)` (`src/compiler/10.frontend/core/ast_stmt.spl:328`),
readable via `stmt_is_if_val_decl`. `if val v = opt:` is desugared to a plain
binding plus `v != nil` — the binder holds the OPTION, and the marker is what
says "unwrap this one".

The **interpreter honours the marker** and is therefore always correct:

```
# src/compiler/10.frontend/core/interpreter/eval_stmts.spl:191
if stmt_is_if_val_decl(sid):
    init_val = eval_option_binding_value(init_val)
```

`/usr/bin/grep -rn stmt_is_if_val_decl src/` returns FOUR consumers: its own
definition, the export line, `ast_clone.spl` (preserves it across a clone), and
that single interpreter site. **`src/compiler/20.hir/**` and
`src/compiler/50.mir/**` contain zero references** — the native lowering never
reads the marker, so the payload extraction the interpreter performs simply
does not happen, and the binder keeps the Option.

The one place MIR does compensate is a narrow special case:
`src/compiler/50.mir/mir_lowering_stmts.spl:1952-1991` re-detects the
`x != nil` desugar shape and rebinds via `enum_payload_value` — but **only when
the payload is a float** (`has_if_val_float_binding`). Every other payload type
falls through with the raw Option still bound. That gate is the narrowest form
of the correct fix, and generalising it (or threading the `IF_VAL` marker into
HIR `Let` and unwrapping with the `rt_unwrap_or_self` dual-representation
helper, as `option_payload_or_self` in
`50.mir/_MirLoweringExpr/method_calls_literals.spl:416` already does) is the
landing this record is still waiting on.

## Not this bug

Distinct from the concurrent `dict.values()` miscompile: that one crashes in
`build_signature`, in a different phase, via a corrupt `.values()` loop.
Established by backtrace before any work here.

## Measured pre-fix evidence

`bin/simple native-build test/fixture/native_optional/if_val_option_payload.spl`
then running it (rc read directly into a variable, not through a pipe):

```
if_val=4  unwrap=99  match=99  field=4  raw=4  int=(false, 0)  none=ABSENT
```

Expected `if_val=99 unwrap=99 match=99 field=77 raw=55 int=55 none=ABSENT`.
Four of seven probes are wrong, and every wrong one is an `if val` binding:

- `if_val`, `field`, `raw` all report **4** — the binder holds the Option
  object and the field read lands on the enum header, so the payload value
  (99 / 77 / 55) never appears. Note `raw=4` too: even the bare "migration
  form" is boxed by the time it reaches the binder.
- `int=(false, 0)` leaks the raw nullable-ABI tuple for an `i64?` payload
  instead of a number.
- `unwrap` and `match` are correct, confirming the defect is the binder alone.

## Pin

`scripts/check/check-native-if-val-option-payload.shs` (fail-closed, verdict
line last on stdout, `ERROR`/exit 2 when nothing was checked) over
`test/fixture/native_optional/if_val_option_payload.spl`, which probes six
shapes: boxed `if val`, `.unwrap()`, `match Some`, an optional STRUCT FIELD
(the `get_symbol_type_raw` shape), the raw migration form, and a boxed `None`
that must NOT read as present.

## Known remaining

- `hir/lower/expr/mod.rs:1143` still lowers `.unwrap()` to a bare
  `rt_enum_payload` when `enum_payload_type_for_builtin_method` resolves,
  with no non-enum passthrough. `rt_unwrap_or_trap` (declared in
  `codegen/runtime_sffi.rs:681`, defined in both runtimes) has exactly the
  right contract. Not changed here because it did not reproduce standalone;
  it is the amplifier that turns this bug's silent-wrong value into a SEGV
  rather than a wrong answer.
- `unwrap_err` has the same shape and no `rt_unwrap_err_or_trap` exists.


## Resolution (2026-08-24)

**Fix:** `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`, the
`STMT_VAL_DECL` arm of the flat-AST -> `StmtKind` bridge.

The parser DOES record the provenance (`stmt_if_val_decl` sets the `IF_VAL`
marker, `ast_stmt.spl:328-331`) and the interpreter DOES honour it
(`eval_stmts.spl:191` -> `eval_option_binding_value`). Everything downstream of
this bridge consumes `parser_types.StmtKind`, which carries no marker field, so
the provenance died at exactly this line — `StmtKind.Val(name, type_,
init_expr)` was constructed without ever consulting `stmt_is_if_val_decl`. That
was verified empirically, not inferred: an instrumented build printed
`[IFVAL-PROBE] bridge val decl name=a if_val=true` for every `if val` binder in
the fixture, proving both that this bridge is the live frontend for
`native-build` and that the marker is intact and readable at that point.

The fix carries the provenance forward as SEMANTICS rather than as a new flag:
when the marker is set, the initialiser is wrapped in `ExprKind.ExistsCheck`
(`.?` — "value if present, nil if absent"), which is precisely
`eval_option_binding_value`'s contract and is already lowered correctly on every
lane. The parser-desugared `x != nil` test then stays correct for a boxed `None`
too, because the binder is now nil in that case. An initialiser that is already
an `ExistsCheck` (the user wrote `if val v = opt.?:`) is not double-wrapped.

Deliberately NOT a blanket unwrap at the MIR seam: at that seam `if val v = e:`
and a hand-written `if v != nil:` are indistinguishable, so unwrapping there
would change semantics repo-wide. No `StmtKind`/`HirStmtKind` enum shape churn
was needed, so nothing had to be threaded through `hir_codec` (generated) or the
monomorphiser's Let reconstruction.

### Correction to the earlier "Correction"

The gate script header attributes the defect to the Rust seed
(`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`,
`build_pattern_binding_stmts`). That attribution is **wrong for this lane** and
should be read as aspirational. A `build_if_let_binding_stmts` routing fix was
implemented there, built, and measured: the gate output was **byte-identical**
(`if_val=4 ... int=(false, 0)`), and an `eprintln!` probe inside the new function
fired **0 times** during the fixture's `native-build`. The Rust HIR lowering is
not on the default `native-build` path at all; the pure-Simple frontend is.
Those Rust edits were reverted and are not part of this fix.

### Verdict lines (measured, exit status read directly into a variable)

Before:

```
FAIL — 7 probe(s) checked, got: if_val=4 unwrap=99 match=99 field=4 raw=4 int=(false, 0) none=ABSENT  (expected if_val=99 unwrap=99 match=99 field=77 raw=55 int=55 none=ABSENT)
```

After:

```
PASS — 7 probe(s) checked across 1 native-built fixture, 0 mismatches
```

Neighbour gates, same working tree, both green after the change:

```
PASS — 4 engine(s) executed, 0 crashes, unwrap-then-field holds        (check-optional-class-unwrap-field.shs)
PASS — in-process positional native-build: exit 0, 27736 B binary, ran and printed 'RESULT=42'
```

### Known remaining (separate defect, NOT introduced here)

`bin/simple run` on the same fixture prints `if_val=103079215111`,
`field=103079215111`, `int=<enum@0x...>`. That path is the **Rust seed's own
interpreter**, which does not go through this bridge. Verified pre-existing by
stashing the fix and re-running: the output is byte-identical with and without
the change. It is a distinct seed-interpreter defect and is out of scope for
this record.
