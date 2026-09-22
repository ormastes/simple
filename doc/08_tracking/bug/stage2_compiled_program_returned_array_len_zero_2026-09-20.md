# Stage-2-compiled programs: `.len()` of a function-returned array is 0

- **Filed:** 2026-09-20
- **Status:** OPEN. Reduced; the lowering site is not located.
- **Found by:** lane `work/stage2-nil-guard-miscompile` while probing the SCV
  inventory sort (`src/lib/scv/compile_source_inventory.spl`
  `compile_source_inventory_sort_v1`).
- **Compiler:** Stage 2, Linux aarch64, built receipt-free from `origin/main`
  `0c25d5eef60` plus this lane's two source fixes (sha256 `ae06cc25e5c048246bfb…`).
  Command: `env SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1
  SIMPLE_PACKAGE_INDEX_COLD_INIT=1 <stage2> native-build --backend llvm
  --threads 1 --mode dynload -o out main.spl`.

## Reduction (builds rc=0, runs rc=0, prints wrong values)

```simple
fn param_len(values: [text]) -> i64:
    values.len()
fn ret_lit() -> [text]:
    ["x", "y"]
fn ident(values: [text]) -> [text]:
    values

fn main():
    val xs = ["a", "b", "c"]
    print("local={xs.len()} param_len={param_len(xs)}")   # local=3 param_len=3   (correct)
    val r = ret_lit()
    print("ret_lit={r.len()}")                            # ret_lit=0            (WRONG, want 2)
    val i = ident(xs)
    print("ident={i.len()}")                              # ident=0              (WRONG, want 3)
    print("ret_lit[1]={r[1]} ident[2]={i[2]}")            # y c                  (correct)
    val typed: [text] = ret_lit()
    print("typed_len={typed.len()}")                      # typed_len=0          (WRONG, even with an annotation)
```

Contents survive; only `.len()` on the caller side of a returned array is
wrong. `.len()` inside the callee on a copy of the parameter is correct
(`var s = values; s.len()` -> 10 for 10 entries).

Related symptom on an array of structs returned from a function: printing
`sorted[i].source_identity` (a `text` field) prints pointer-sized integers such
as `221935157247137`, and `sorted[i].source_identity != expected[i]` answers
`false` for every element, so a verification loop over a returned array can
report success while comparing garbage.

## Consequence for the SCV sort question

A probe that sorts and checks the result in the caller is vacuous under this
defect. Sorting and joining inside one function instead
(`sort_and_join(values) -> text`, same insertion sort) gives the canonical byte
order on this lane — `src/app/B.spl`, `src/app/Zeta.spl`, `src/app/__init__.spl`,
`src/app/_x.spl`, `src/app/a.spl`, `src/app/audit.spl`,
`src/app/audit/__init__.spl`, `src/app/audit/ffi_analyzer.spl`,
`src/app/build/main.spl`, `src/lib/a.spl`, `JOINED_MATCHES_EXPECTED=true` —
and `"src/app/audit/ffi_analyzer.spl" < "src/app/__init__.spl"` is `false` as it
should be. The FreeBSD x86_64 noncanonical inventory order (1881 of 16796
adjacent pairs) was NOT reproduced here; it concerns the Stage 2 binary's own
phase-1-compiled sort on another target and is not explained by this record.

## Two more observations from the same probes (not reduced further)

- `.unwrap()` on a `Sym?` returned from a class method fails to build:
  `MIR lowering error: unresolved method call: unwrap`.
- `match self.tab.get_raw(id): case Some(info): …` where `get_raw` returns a
  struct Option from a `{i64: Sym}` dict field builds, but the program SIGSEGVs
  before its first `print` (`[simple-runtime] Fatal: SIGSEGV at address
  0x157bb9bffd88`). Not attributed to a specific construct.

## Candidate repair 2026-09-22: returned struct-array element provenance

Static inspection located a missing metadata edge: `emit_resolved_direct_call`
marked Array/Slice returns as runtime arrays but omitted their element layout
name. `lower_index_expr` needs that name in `array_element_struct_syms` to
register a decoded element in `struct_value_syms`; field projection otherwise
loses both field offsets and text representation information.

The candidate records the element name during the defining module's prescan,
then propagates it through direct calls and `remember_call_hir_return`. It does
not dereference foreign module SymbolIds. The registry participates in transient
heap promotion and disables ambiguous names, including scalar/struct array
collisions. The change adds no runtime ABI or OS dependency.

`test/01_unit/compiler/mir/returned_struct_array_native_spec.spl` requires an
explicit `SIMPLE_NATIVE_COMPILER`, builds the standalone insertion-sort fixture,
and executes its native binary. It checks exact stdout at fixed indices as well
as exit status, length, text fields, and a second integer field. Consequently a
zero length cannot skip the field oracle, and miscompiled equality cannot turn
pointer output into success.

Validation so far: whitespace validation and both direct-env-runtime guards
passed. Native compilation/execution of the candidate compiler remains pending;
neither the returned-array length defect nor FreeBSD Stage 3 admission is claimed
fixed by this static finding.

### Review revision: identities, imports, length routing

The admitted FreeBSD Stage 2 compiler reproduced the standalone candidate's
original same-module fixture: `count=0`, pointer-like field output, exit 91.
This is a red baseline, not validation of the repaired compiler.

Element collision detection now retains the defining module's qualified
identity separately from the bare layout name consumed by field projection.
Same-named structs from different modules therefore disable an ambiguous call
alias. The prescan registers raw, sanitized, and dotted call aliases, including
bare function names. The fixture now obtains its rows from an imported module;
registry tests cover same-name/different-owner and scalar/struct collisions.

The zero length also has a separate lowering hazard: the length dispatcher
rewrote `rt_len` to `rt_string_len` using only `runtime_array_locals`. That map
can omit returned locals whose MIR type already says Array/Slice. The candidate
now uses `local_is_runtime_array`, which consults both the map and MIR type.
Alias registration additionally lets HIR return recovery mark imported arrays.
This gives a concrete repair path for a real array handle reaching the string
length accessor, but without inspecting the red binary's generated MIR or
running a rebuilt compiler it does not prove that this was its precise cause.

Native test compilation is bounded to 360 seconds and execution to 10 seconds,
with output under a process-id/time-specific directory. Array and Slice share
the same repaired prescan/direct-call branches. A separately executed native
Slice fixture and rebuilt compiler validation remain pending; neither is
claimed covered by the array fixture.
