# native-build SIGSEGV: class-in-array field mutation through a function param

- **Status:** OPEN — filed, not fixed (found incidentally while verifying
  `struct_param_mutation_semantics_2026-07-03.md`'s class-reference-semantics
  fix; confirmed pre-existing and unrelated to that fix)
- **Discovered:** 2026-07-17, lane s19
- **Area:** native-build MIR/codegen — array-of-class parameter + indexed
  element field write
- **Severity:** High (crash, not silent-wrong-value, but still an unhandled
  compiler defect on a plausible everyday shape)

## Repro

```spl
class Counter:
    value: i64

    static fn new(v: i64) -> Counter:
        Counter(value: v)

fn mutate_first(arr: [Counter]):
    arr[0].value = arr[0].value + 1

fn main() -> i64:
    val arr = [Counter.new(0), Counter.new(0)]
    mutate_first(arr)
    print(arr[0].value)
    return arr[0].value
```

- Interpreter (`env -u SIMPLE_BOOTSTRAP bin/simple run <file>`): JIT rejects
  with `[W1006]` (mutation without `mut` capability), falls back to
  interpreter, prints `1` (correct — mutation visible).
- Native (`bin/simple native-build --entry <file> -o out --clean` then run
  `./out`): compiles cleanly (no diagnostic), then **SIGSEGV at runtime**
  (`rc=139`).

Confirmed via `git stash` / `git stash pop` in `/home/ormastes/dev/wt_s10`
that this crash is present identically with or without the
`struct_param_mutation_semantics_2026-07-03.md` class-reference-semantics fix
— it is a separate, pre-existing defect, not a regression from that change.

A closely related shape without the array (`arr[0].bump()`, a method call on
an indexed array element rather than a direct field write) hits a different,
already-tracked gap instead: `[mir-lower] WARNING: unresolved method call
'bump' lowered to const-0 placeholder (silent-null risk, Task #145)`, followed
by a hard MIR error (no binary produced) — so this segfault is specifically
about the **direct field-write** path on an array element passed through a
function parameter, not method dispatch.

## Impact

Any native-build code that takes a `[SomeClass]` parameter and writes a field
on an indexed element (`arr[i].field = ...`) will crash at runtime instead of
mutating correctly. Not yet root-caused; likely in the MIR lowering for
`Index` + `FieldSet` on a Named/class-typed array element, or in how the
array parameter's element storage interacts with the class reference-binding
introduced by the sibling fix above.

## Next step

Not fixed in lane s19 (out of scope: a different codegen path from the
function-parameter mutation-drop bug this lane targeted). Needs its own
root-cause pass — reproduce with `--backend cranelift` too to see if it's
LLVM-specific, and get a real crash-address symbol (build with
`--release`-off / check for a debug build or `gdb`/backtrace tooling) before
guessing at the fix.

## Durable reproducer

The exact two-element/static-constructor shape is checked in at
`test/fixtures/compiler/native_class_array_param_field_mutation.spl`.
Run it through both native backends with:

```sh
NATIVE_OPEN_BUG_REPROS=1 \
NATIVE_PARITY_CASES=class_array_param_field_mutation \
sh scripts/check/check-native-seed-parity.shs
```

It is intentionally excluded from the default green parity gate while this
issue is OPEN; it is a strict repro, not an expected-failure waiver. Remove
the opt-in guard only after both backend legs print exactly `1` and exit 0.

## Current-source audit (2026-07-17)

Current MIR lowering already marks typed array parameters as runtime arrays and
records the named element type in `array_element_struct_syms`. Indexed runtime
array reads transfer that name to `struct_value_syms` on the decoded element,
which is the shared provenance path required by the subsequent field write.
`mir_lowering_new_spec.spl` now pins that path, the critical mutation shape,
and its strict harness registration.

This is source hardening, not runtime closure. The strict dual-backend fixture
remains opt-in until LLVM and Cranelift both print `1` and exit zero; only then
should it join the Linux, macOS, Windows, and FreeBSD selected green gates.
