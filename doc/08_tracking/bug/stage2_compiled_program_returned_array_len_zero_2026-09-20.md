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
