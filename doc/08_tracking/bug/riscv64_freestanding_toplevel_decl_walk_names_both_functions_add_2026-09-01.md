# riscv64 freestanding: the top-level declaration walk yields the SAME function twice

- Status: **OPEN** — the current blocker for goal item 1 row 2 (SimpleOS riscv64
  in-guest build-and-run sanity).
- Date: 2026-09-01
- Lane: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`,
  row 2 (`buildrun`)
- Measured under real OpenSBI v1.4 `-bios fw_payload`, nonce
  `f75425f438b6c00b`, gate selftest OK (23 fixtures).

## This is a NEW defect, not either of the two just fixed

Row 2 was blocked by two defects that are now FIXED and separately verified:

1. the baremetal `rt_value_unbox_int` missing its tagged-bool arm (parser hang,
   reboot loop, heap exhaustion) —
   `riscv64_freestanding_bool_in_collection_always_true_2026-09-01.md`;
2. the Cranelift inline `.len()` not recognising baremetal `HEAP_DICT=11`,
   answering the `-1` sentinel —
   `riscv64_freestanding_len_eq_zero_guard_never_fires_2026-09-01.md`.

With both fixed, row 2 boots ONCE, parses, lowers to HIR and MIR, and reaches
the run stage. It now fails on this third, independent defect.

## Symptom, measured

The program built in-guest has exactly TWO top-level functions, `add` and
`main`. In-guest probes report:

```
[probe] parsed-fns=1
[probe] parsed-fn-order=[add]
[probe] parsed-fn-order=[add]     <- the SAME name twice
[probe] parsed-order-listed
[probe] hir-fn-count=1
[probe] mir-fn-count=1
[probe] hir-fn-name=[add] len=3
[probe] sym-add-id=0
[probe] sym-main-id=-1
[probe] sym-add-valid=YES
[probe] sym-main-valid=NO
[buildrun] FAIL run error: module has no main function
```

`parsed.function_order` has **two entries and both are `add`**. Since
`module_assembly.spl:336-347` does

```simple
val fn_: ParserFunction = convert_decl_fn(idx)
functions[fn_.name] = fn_
function_order.push(fn_.name)
```

the second iteration overwrote the first under the same key, leaving
`parsed.functions.len() == 1`. `main` therefore never existed downstream, which
is why `lookup_or_invalid("main")` answers the invalid id `-1` and the
interpreter reports "module has no main function". Both lowering stages report
ZERO errors — the loss is completely silent.

## What this rules IN and OUT

- **Not** the `.len()` `-1` defect: `.len()` now answers correctly (1), and it
  answers 1 because the dict genuinely holds one entry.
- **Not** the `SymbolId` key-collision at `module_build.spl:462-465` that the
  prior-art comments there describe: only one function ever reaches HIR
  lowering, so there is no second insert to collide. That was the leading
  hypothesis and the measurement refutes it.
- **Not** a skip in HIR lowering: the loss is already present in `parsed`.

So the defect is inside `parse_and_build_module_scoped`'s top-level declaration
walk (`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:336-347`),
and it is one of exactly two things, NOT yet discriminated:

- **(a)** `module_decl_at(di)` returns the same flat index for both `di = 0` and
  `di = 1`, so `convert_decl_fn` converts declaration 0 twice; or
- **(b)** the index differs but `decl_get_name(idx)`
  (`src/compiler/10.frontend/core/_Ast/decl_nodes.spl:896`) answers `add` for
  both. That function has three layered sources — an arena array
  (`decl_name[idx]` when `ast_decl_prefer_arena()`), an SFFI env lookup
  (`_sffi_env_get(ast_decl_name_key(idx))`), then `ast_decl_text_get(idx,
  "NAME")` — and which one is live in freestanding has not been established.

Do not assume either without measuring; the last three assumptions on this row
were all wrong.

**Ruled out already:** the baremetal `rt_env_get`
(`baremetal_runtime_core.inc.c:2302`) does key correctly on its key argument via
`simpleos_env_find`, so a key-ignoring env stub is NOT the mechanism.

## Reproduce / next probe

Re-apply this probe to
`examples/09_embedded/simple_os/arch/riscv64/buildrun_sanity_entry.spl`,
immediately after `parse_and_build_module(...)`:

```simple
serial_println("[probe] parsed-fns=" + parsed.functions.len().to_string())
for pname in parsed.function_order:
    serial_println("[probe] parsed-fn-order=[" + pname + "]")
```

Then add, inside the walk at `module_assembly.spl:336-347`, a print of BOTH
`di` and the `idx` returned by `module_decl_at(di)`, plus the name. Equal `idx`
for successive `di` proves (a); distinct `idx` with equal name proves (b).

Cycle cost: full gate rebuild + both boots ~12 min.

## Note on the probe values

Print RAW values, never comparison results. A `.len()` on a Dict was answering
-1 on this lane until today, and a boolean answer would have hidden it.
