# Stage-3 vacuous binary: `??` on an `Option<UserEnum>` returns the enum's PAYLOAD

Date: 2026-08-08
Status: FIXED — landed on `main` at commit `ae07aaa2910` (`fix(runtime): gate
rt_unwrap_or_self on canonical Option enum_id`). The predicate in both
`src/runtime/runtime_native.c` and `src/runtime/simple_core/core_values.spl`
now gates on `rt_enum_id(value) == 1` (canonical Option) before unwrapping,
instead of unwrapping ANY boxed enum. Validated with a RED/GREEN proof at the
runtime-primitive level: a standalone C harness linked against a freshly
compiled `runtime_native.o` (stubbing the unrelated `spl_*`/`rt_process_*`
symbols it doesn't exercise) called `rt_enum_new` to build a user enum
`K.Slice(7)` and asserted `rt_unwrap_or_self(k_slice) == k_slice` (flat
Option ABI: a present `o: K?` IS the raw K handle directly, not a
double-boxed Option). Pre-fix object: `coalesced == payload7` (bug
reproduced, exit 1). Post-fix object: `coalesced == k_slice` (fix verified,
exit 0). `Result.unwrap()` is unaffected by this predicate change — it
routes through `rt_enum_payload` directly
(`method_calls_literals.spl:487`), never through `rt_unwrap_or_self`, so
"next action" item 2 in this doc (settle `Result.unwrap()` before changing
the predicate) turned out to be moot for the pure-Simple compiler path; the
codegen_instr_tests risk noted in §5 applies only to the separate Rust-seed
codegen dispatch (`compiler_rust/codegen/instr/closures_structs.rs`), not to
`src/compiler/50.mir` which this fix targets.

Regression: extended
`test/01_unit/compiler/mir/null_coalesce_lowering_spec.spl` with a new `it`
asserting the old buggy predicate is gone from `runtime_native.c` and the
`rt_enum_id == 1` gate is present in both runtimes. That new example passes.
(A separate, pre-existing example in the same file — asserting literal text
`"left_value = unwrapped"` against `expr_dispatch.spl` — is failing
independently of this fix: another concurrent lane refactored that call site
to `self.option_payload_or_self(left_local)`, a helper function, so the
literal string no longer appears. Out of scope for this bug; left as-is for
whichever lane owns that refactor to reconcile.)

Full end-to-end validation (native-build `enum30.spl` printing `A =
Slice(7)`, `D = Pair(3,4)`, `E = Bool`, `G = Str` per §6 next-action 1) was
NOT re-attempted here: the previous session's scratch build scripts
(`mk.sh`/`mk2.sh`) and the `stage2-runtime-authority` runtime path they
depended on are no longer present in this session's scratch area, and
`native-build --entry` without `--source` rescans the whole default source
tree (multi-minute, and hit an unrelated pre-existing compile error in this
run). The runtime-primitive RED/GREEN proof above isolates and validates
exactly the one-line predicate this bug is about, independent of that
build-plumbing gap. Re-running the full Stage-3 build to confirm downstream
effects on the "3,629 const-0 placeholder substitutions" symptom is the
remaining follow-up, tracked separately from this bug's specific defect.
Severity: was BLOCKER (critical path to self-host); root defect fixed.

Supersedes the "next actions" of
`stage3_vacuous_binary_is_enum_discriminant_garbage_not_a_link_failure_2026-08-08.md`.
That document's evidence chain (object is linked, `--gc-sections` is correct,
IR has 0 stores / 0 arithmetic / 15 `rt_panic`-only calls) stands unchanged.

## 1. The engine discriminator — answered

Three legs on the same 7-line reproducer (`fn addup(a,b) = a+b; print`).
The a-priori oracle is used throughout: a correct compile of `a + b` must
produce a binary that prints `RESULT=42`.

| # | compiler | backend | result |
|---|----------|---------|--------|
| 1 | seed `stage2-runtime-authority/simple` | cranelift | **PASS** — 29,952 B binary, `RESULT=42`, `cranelift` named 18x in the log |
| 2a | `build/cyc/S3FIX1/stage2-simple` (native) | llvm | **FAIL** rc=1, no object emitted |
| 2b | `build/cyc/S3FIX1/stage2-simple` (native) | cranelift | **FAIL** rc=1, byte-identical error |
| 3 | pure-Simple compiler **source, interpreted** by the seed (`simple run src/app/cli/bootstrap_main.spl native-build …`) | llvm | **PASS** — 28,744 B binary, `RESULT=42` |

Legs 2a and 2b die with the identical message *before any backend runs*:

```
[ERROR] MIR error: MIR lowering error: unsupported MIR type kind [wildcard-arm] disc=-1: <value:0x1800000007>
```

**Verdict: the defect is NOT in LLVM lowering. It is upstream, and it is not in
the compiler source either** — the same `.spl` source interpreted (leg 3)
lowers the same input correctly. It is a defect in the *natively compiled*
compiler, i.e. in code the seed's native lane emitted.

No IR/MIR census was needed and none is comparable: leg 2 hard-errors before
emitting anything, so hard-error-vs-`RESULT=42` is strictly stronger evidence
than a census diff would have been.

### Leg 3 was proven, not assumed

A positive capability probe: `eprint("[SABOTAGE-PROBE-ZQX7] …")` was inserted at
the top of `MirLowering.lower_type`
(`src/compiler/50.mir/_MirLowering/function_lowering.spl:641`), leg 3 was re-run,
and the marker appeared **5 times**. Leg 3 therefore executed the pure-Simple
`lower_type` — the exact function whose wildcard arm fires in leg 2. The source
was restored to its original blob `725d2e94cee48f8d6942f4710e55fc21d25dc1cc`
immediately afterwards.

### Correction to the prior document

The prior doc reported "the seed has no LLVM backend". That was true of
`src/compiler_rust/target/bootstrap/simple` only. The seed that actually builds
stage2 —
`…/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority/simple` —
has both LLVM and cranelift, and it built a 128 MB stage2 with `--backend llvm`.
A seed control was available all along.

## 2. A 2-second iteration loop now exists

The prior lane recorded that no iteration loop existed short of a 1200s Stage-3
run. That is no longer true. Because the broken code was emitted by the *seed*,
a standalone `.spl` file compiled with the **same seed and the same flags as
`build/cyc/build_stage2.sh`** reproduces the defect in ~2 s
(`0.3s compile + 1.4s link`). Recipe: `env -i` + `SIMPLE_BOOTSTRAP=1
SIMPLE_NATIVE_BUILD_RUST=1` + `native-build --backend llvm --runtime-bundle
core-c-bootstrap --entry-closure --mode dynload --entry <file> --runtime-path
<authority>`.

## 3. Root cause: `rt_unwrap_or_self` unwraps ANY boxed enum, not just Option

Minimal reproducer (`enum30.spl`) — an 4-variant enum, a `match`, and one `??`:

```
val o: K? = K.Slice(7)
print "A coalesce      = {nm(o ?? K.Bool)}"
```

Output from the seed's native lane:

```
A coalesce      = WILD v=7          <- K.Slice(7)  ->  7        (payload)
B ifval         = Slice(7)          <- `if val u = o` is CORRECT
C param-coalesce= WILD v=7          <- same through a K? parameter
D pair-coalesce = WILD v=[3, 4]     <- K.Pair(3,4)  ->  [3, 4]  (payload tuple)
E nullary-coal  = WILD v=nil        <- K.Bool       ->  nil     (nullary payload)
F field-coalesce= WILD v=7          <- same through a struct field of type K?
G nil-coalesce  = Str               <- a genuine nil IS handled correctly
```

`??` on an `Option<UserEnum>` evaluates to **the inner enum's payload**, not the
enum. The value that comes out matches no `case` arm of any subsequent `match`,
so it falls to `case _:`.

The mechanism is one line, in both runtime implementations:

- `src/runtime/runtime_native.c:3684`
- `src/runtime/simple_core/core_values.spl:45`

```c
int64_t rt_unwrap_or_self(int64_t value) {
    if (rt_enum_discriminant(value) >= 0) return rt_enum_payload(value);
    return value;
}
```

The test is "is this **any** boxed enum", so a boxed *user* enum is unwrapped to
its payload. The intended contract is Option-only and is stated verbatim in the
compiler at
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2168-2180`:

> "rt_unwrap_or_self is the runtime's own dual-lane reader (`disc >= 0 ? payload
> : value`), so it is correct on BOTH lanes. **Only Option switches to it; every
> other enum keeps rt_enum_payload verbatim.**"

The correct predicate already exists two lines below, in `rt_is_none`:
`rt_enum_id(value) == 1` — enum id 1 is the canonical Option (Some=0/None=1).

`??` provably routes through this function: `objdump -d` on the reproducer
binary shows **6 `call rt_unwrap_or_self` sites**, and the disassembled body is
exactly the buggy shape (`call rt_enum_discriminant; test %rax,%rax; js …`).

### Why this explains the whole Stage-3 picture

The compiler's own HIR/MIR types are enums held in optional fields and read back
through `??` throughout `50.mir`. Every such read degrades the enum to its
payload, so every `match` over it falls to a wildcard/unresolved arm. That is
the 3,629 `const-0 placeholder` substitutions, the 15-`rt_panic`-only call set,
the 0 stores and 0 arithmetic — one defect, all symptoms.

## 4. The TEMP-PROBE numbers are confirmed artifacts

The prior lane downgraded `d=-1` to UNPROVEN. That was right, and it can now be
upgraded to *disproven as evidence*. Under the seed's native lane
`rt_enum_discriminant` returns garbage for freshly constructed enums:

```
disc(Str)=3560734392   disc(Slice)=4126198529   disc(Any)=80134736
```

`disc(Slice)=4126198529` is **bit-identical** to the `slice=4126198529` printed
by the Stage-3 `[TEMP-PROBE-mir-wildcard]` line, from a completely different
program with a completely different enum. The probe's nine reference values
measure the probe, not the defect. Do not cite any of them — including `d=-1`.

Equally, do **not** read `0x18 = 24 = HirTypeKind.Any` out of the high word of
`<value:0x1800000007>`. `0x1800000007 & RT_VALUE_TAG_MASK(0x7) == 7`, an invalid
tag, so the value is malformed and its bit fields carry no reliable meaning.
`<value:0x…>` is `rt_to_string`'s opaque fallback for a value it recognises as
*nothing* — consistent with a raw payload word escaping through `??`.

## 5. Why the fix is not landed

The one-line change (gate on `rt_enum_id(value) == 1` instead of
`rt_enum_discriminant(value) >= 0`, in both runtimes) is written and anchored as
git blobs — `runtime_native.c` = `cf22da7f0b0c14c83ee722c9f4badd979c6f987f`,
`core_values.spl` = `29943414ce481cec8ac2a2497269465a34f3ff77` — but it is
**not landed**, for two reasons:

1. **It could not be validated.** Every available build lane links a *prebuilt*
   runtime (`--runtime-path .../stage2-runtime-authority`, and the default lane
   too). After patching both runtime sources, the rebuilt reproducer binary
   still disassembles to the old body (`call rt_enum_discriminant … js`) and
   still prints `WILD v=7`. Validating requires rebuilding the runtime archive
   that supplies `rt_unwrap_or_self`; that archive member was not located inside
   `libsimple_runtime.a` (452 members, none define the symbol), so the producer
   of the linked copy is still unidentified. **This is the next action.**
2. **There is a concrete regression risk.** `src/compiler_rust/compiler/src/
   codegen/codegen_instr_tests/calls.rs:250-315` asserts that bare `.unwrap()`
   and `.unwrap_or()` compile to `rt_unwrap_or_self`. Under the current
   implementation `.unwrap()` on a `Result` (enum id != 1) returns the Ok
   payload; under the proposed one it would return the `Result` enum itself.
   Landing without settling `Result.unwrap()` would trade one silent
   miscompile for another.

The prior lane's refusal to land the unvalidated `bootstrap_globals.spl:408`
guard change still stands and is unchanged by this work.

## 6. Next actions

1. Find which archive/object supplies the linked `rt_unwrap_or_self` and rebuild
   it from patched source. The 2-second loop then validates or refutes the fix
   directly (`enum30.spl` must print `A = Slice(7)`, `D = Pair(3,4)`,
   `E = Bool`, `G = Str`).
2. Settle `Result.unwrap()` before changing the predicate: either give Result a
   distinct unwrap helper, or make the gate `enum_id == 1 || enum_id ==
   <Result>`, or fix the callers.
3. Only then re-run Stage 3. Do not spend another 1200s run before step 1.
4. `rt_enum_discriminant` returning garbage (`disc(Slice)=4126198529`) on the
   native lane is a **separate, independent defect** and needs its own bug —
   it makes every `rt_enum_discriminant`-based probe in the tree fail open.

## Artifacts

Reproducers and logs: `<session scratch>/s3ctl/` — `repro.spl`, `enum27.spl`,
`enum29.spl`, `enum30.spl`, `mk.sh` (the 2-second stage2-flag build loop),
`mk2.sh` (default-flag loop), and per-leg logs `L1_seed_cl.log`,
`L2_llvm.log`, `L2_cranelift.log`, `L3_interp.log`, `L3_sab.log`.
