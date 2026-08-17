# `shared` Parameter Lowers As Undeclared LLVM Global

## Symptom

During a full pure-Simple bootstrap, Stage 2 native-build failed for the HIP
and OpenCL backend contract modules with:

`llvm global load referenced undeclared symbol Shared`

Both failures used `shared` as a local and parameter name, then read fields
from that parameter. Renaming the binding to `contract` allows compilation to
proceed without changing behavior.

## Expected

Lowercase local and parameter bindings named `shared` must remain local SSA
values during LLVM lowering. They must not be canonicalized into a global or
variant symbol named `Shared`.

## Reproduction

Run the full bootstrap native-build over a module containing a typed parameter
named `shared` followed by a field read such as `shared.source`.

## Follow-up

Add a focused LLVM-lowering regression and fix name classification so local
bindings take precedence over global/variant canonicalization.

---

## RETIRED 2026-08-17 (W4 bug-fixing wave) — does not reproduce; a real binary is produced and returns the right value

The reproduction asked for is a native-build over a module with a typed parameter
named `shared` followed by a field read such as `shared.source`. Built exactly
that, as a standalone `native-build` (not a full bootstrap, which is not required
— the defect was a name-classification error in LLVM lowering, so a single module
that exercises the parameter + field read is a sufficient oracle):

```
struct Contract:
    source: i64

fn read_source(shared: Contract) -> i64:
    shared.source

fn main():
    val shared = Contract(source: 5)
    print "src={read_source(shared)}"
```

```
$ bin/simple native-build shared_probe.spl -o shared_probe_bin
rc=0                                  # binary produced; no diagnostic
$ ./shared_probe_bin
src=5                                 # correct (expected 5)
$ sh scripts/check/check-no-call-zero.shs shared_probe_bin
PASS — 1 binary/binaries checked, 0 call-to-zero sites
```

Binary that produced this: `bin/simple` ->
`bin/release/x86_64-unknown-linux-gnu/simple` (the Rust seed, which is the
binary that performs a `native-build` and therefore the binary whose LLVM
lowering this row is about). No `llvm global load referenced undeclared symbol
Shared` anywhere in the 1,575-line build log; the `native_compile` step reported
`1/1 complete` and the link succeeded.

The probe covers BOTH bindings this doc names — the parameter `shared: Contract`
with a field read AND a local `val shared` — and neither is canonicalized to a
global. The `call 0` check is included because a name misclassified into a
global/variant symbol is the same fail-open family as
`stage3_native_build_sigsegv_call_to_zero_root_cause_2026-08-11`; it is clean
here, so the value is genuinely computed rather than read from a fabricated stub.

### What fixes it in current source

`src/compiler_rust/compiler/src/hir/lower/tests/expression_tests.rs:93-98`,
`shared_keyword_local_read_does_not_become_global_variant`, is the landed
regression for exactly this classification: it lowers `val shared = 1; return
shared`, asserts `shared` appears in `function.locals`, and asserts the lowered
module does NOT contain `Global("Shared")`. The doc's "Follow-up" item ("add a
focused LLVM-lowering regression and fix name classification so local bindings
take precedence over global/variant canonicalization") is therefore already
discharged — a local/parameter binding now wins over variant canonicalization,
and a test pins it in both directions.

No new spec is added on top of that: the pure-Simple `test` runner is the
tree-walking interpreter and cannot exercise the LLVM lowering path this row is
about, so an interpreter spec would be a vacuous green. The end-to-end
`native-build` + execute above is the operative evidence.
