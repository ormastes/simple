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

---

## MEASURED 2026-09-01 (second lane): candidate **(a)** — and the mechanism is
## NOT the one that was predicted

One boot, real OpenSBI v1.4 `fw_payload` (`-bios` only, no `-kernel`, no
`isa-debug-exit`), nonce `a1aaa9eb6ed791ec`, gate selftest OK (23 fixtures),
freshly built Rust seed (`cargo build --release --bin simple`, exit 0).
Verbatim guest serial:

```
[probe] decl-count=2
[probe] slots-len=2
[probe] slot0=0
[probe] slot1=1        <- the slot ARRAY is CORRECT
[probe] declat0=0
[probe] declat1=0      <- module_decl_at(1) DISAGREES with slot_get(1)
[probe] name0=[add]
[probe] name1=[add]
[probe] prefer-arena=
[probe] parsed-fns=1
[probe] order-len=2
[probe] parsed-fn-order=[add]
[probe] parsed-fn-order=[add]
[buildrun] FAIL run error: module has no main function
```

### This settles (a) vs (b)

`module_decl_at(0)` and `module_decl_at(1)` both answer **0**, so
`convert_decl_fn` converts declaration 0 twice. That is candidate **(a)**.
Candidate (b) is refuted: `decl_get_name` is innocent — it is asked about index
0 both times and correctly says `add` both times.

### And it refutes the leading mechanism for (a)

The predicted mechanism was dropped writes to the `module_decl_slots` global
(the shape of the historic defect the comment at `decl_nodes.spl:1418-1426`
describes), which would have left the pristine 128-zero initializer. It did
not happen: `slots-len=2` and `slot0=0 / slot1=1` are exactly right, so
`module_add_decl`'s writes landed and the array is the correct truth. The
same-module-accessor fix recorded in that comment is still holding.

The defect is therefore INSIDE `module_decl_at`
(`src/compiler/10.frontend/core/_Ast/module_state.spl:433-443`), between its
guard and the array it is supposed to fall back to. Enumerating the branches
that can return 0 for `index = 1` while `ast_module_decl_slot_get(1)` is 1:

- the `index < 0 or index >= count` guard returns `-1`, not 0 — and
  `decl-count=2` rules it out anyway;
- the `SIMPLE_NATIVE_ARENA_DECLS == 1` branch returns `slot_get(index)`, which
  is measured as 1 — so it cannot be the branch taken;
- **only** `return ast_parse_i64(env_value)` on the ENV-FIRST path can answer 0.

So the env-first mirror is answering for index 1 with something that parses to
0 — i.e. the env crutch is serving index 0's entry (or garbage) for index 1,
and it takes precedence over the array that is right there and correct.

### Note on `prefer-arena=`

It printed EMPTY, not `true`/`false`. `bool.to_string()` in freestanding
riscv64 yields the empty string. That is a separate reporting defect, harmless
here (nothing branches on it), but it is exactly why this record insists on RAW
values: a probe that had rendered this as a comparison would have read as
`false` and misled again.

### Open, being measured next

Whether the wrong env answer is a KEY collision (`int_to_str` — which contains a
`for k in 0..20`, on a lane with a live `for`-in defect,
`freestanding_riscv64_for_in_array_yields_nil_after_first_element_2026-08-31.md`
— producing the same key text for 0 and 1) or a VALUE defect. Second probe adds
`int_to_str(0)`, `int_to_str(1)`, the composed key, and the raw `rt_env_get` of
both the composed and the literal key.

---

## RESOLVED 2026-09-01 — root cause measured, fixed, and the row moved on

**Root cause:** `module_decl_at` chose between its env mirror and its slot array
with `if env_value != "":`, and on this target that comparison is **TRUE for a
zero-length text**. An in-memory branch trace inside the real function
(nonce `919b943728da5c1c`) recorded, for a MISSING env entry:

```
trace=900    entered the env-first tail with index 0
trace=800    env_value.len() == 0      <- the text IS empty
trace=700    the `!= ""` arm was taken ANYWAY
```

So every call returned `ast_parse_i64("") == 0`: `module_decl_at` answered
declaration **0 for every index**, the walk converted decl 0 twice, and `main`
never existed downstream. Candidate **(a)**, as the earlier measurement said —
but not for any of the reasons anyone predicted.

**Every cheaper explanation was refuted by measurement, not by argument:** the
slot array is correct (`slots-len=2, slot0=0, slot1=1`); `decl_get_name` is
innocent (asked about index 0 both times, so (b) is out); the env mirror is
EMPTY (`env0/env1/envlit1` all `<NIL>`, `SIMPLE_BOOTSTRAP` unset) so the env
branch should never have been reachable at all; a **verbatim replica** of the
function body compiled into the same image answers CORRECTLY (`v1-1=1`), as do
explicit-return, snapshotted-index and no-env variants; `nm` shows exactly one
definition of each symbol, so the duplicate-definition trap did not apply; and
the row-2 `kernel.elf` disassembly is correct at all three `slot_get` sites.
Only instrumenting the real function's branch decisions found it.

**Fix:** `if env_value.len() > 0:` — `.len()` is measured correct on the same
path in the same boot. Hosted semantics unchanged: a present entry is still
non-empty and still outranks the array.

**Pinned by** `scripts/check/check-decl-index-lookup-not-empty-text-compare.shs`
(RED against this fix's own parent, GREEN at the fix; fatal `--selftest`, 5
fixtures including must-FAIL replays of both spellings; wired blocking).

**The comparison itself is NOT fixed** and is filed as
`riscv64_freestanding_text_neq_empty_literal_true_for_zero_length_2026-09-01.md`.

### Row 2 status: still RED, on a DIFFERENT and later defect

Measured after the fix (nonce `41d7bd8ce8c848bd`, real OpenSBI fw_payload):

```
[buildrun] phase=hir-ok
[buildrun] FAIL mir lowering error: E-MIR-TYPE-ZeroKind: lower_type received a
  well-formed HirType whose `kind` field is raw 0 (never written) while
  lowering 'main' -- fix the PRODUCER that left kind unset, not lower_type
```

`main` now EXISTS, is lowered to HIR, and reaches MIR — which is exactly the
progress this defect was blocking, and is the first time `main` has ever been
seen downstream on this row. The new blocker is unrelated: `fn main():`
declares no return type, and the producer of its implicit return HirType leaves
`kind` at raw 0. Filed as
`riscv64_in_guest_mir_lower_type_zero_kind_on_main_2026-09-01.md`.
