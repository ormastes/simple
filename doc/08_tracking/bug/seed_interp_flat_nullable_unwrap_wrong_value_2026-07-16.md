# seed_interp: flat-nullable `.unwrap()` returns wrong value

- Status: fix ready, pending seed redeploy
- Component: Rust seed interpreter (`bin/simple run`, SIMPLE_BOOTSTRAP unset) — actually the seed's default JIT-first execution path (Cranelift codegen), not the AST tree-walking interpreter; `SIMPLE_EXECUTION_MODE=interpret` was already correct before this fix
- Severity: medium (oracle landmine — corrupts oracle-vs-native parity comparisons)
- Found: 2026-07-16 during repro-verification of `native_text_option_unwrap_pointer_value_2026-07-15`
- Fixed: 2026-07-17, `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` (see Root Cause / Fix below). Patch staged at
  `/tmp/claude-1000/-home-ormastes-dev-pub-simple/33c947ae-e017-48b7-b5a6-08020378379a/scratchpad/s5_seed_interp.patch`
  (worktree `/home/ormastes/dev/wt_seedfix`). **Fix verified on a freshly built seed binary; deployment (redeploying
  `bin/release/x86_64-unknown-linux-gnu/simple`) is PENDING explicit user approval — the deployed binary still has the bug.**

## Root cause (confirmed)

Not the AST interpreter — the bug lives in the seed's default JIT/codegen path
(`bin/simple <file.spl>` compiles via Cranelift first, falling back to the
interpreter only on JIT failure; this file compiled cleanly, so it ran the
buggy codegen). When a bare `.unwrap()`/`.unwrap_or()` call's static type is
erased (`Any`) or is a flat-nullable `T?` (HIR `Pointer { inner: T }`, which
stores its payload directly rather than as a boxed `Option::Some` enum
object), MIR/codegen falls through to a generic dynamic-dispatch fallback
(`try_compile_builtin_method_call` in
`compiler/src/codegen/instr/closures_structs.rs`) that unconditionally mapped
`"unwrap" | "unwrap_or"` to the runtime function `rt_enum_payload`.
`rt_enum_payload` returns tagged-nil (`RuntimeValue` bit pattern `3` — see
`create_enum_value` in `compiler/src/codegen/instr/result.rs`, comment "Empty
payload uses tagged nil (3), not raw 0") whenever the receiver is not a
genuine heap-tagged `Enum` object, which is always true for a flat-nullable
local holding a present value (its raw/tagged scalar or heap pointer is not an
`Enum`-tagged object). Two distinct downstream symptoms result:
- **i64? case:** the statically-inferred return type is an integer, so
  codegen wraps the `rt_enum_payload` result in another `BoxInt`. This re-tags
  the nil bit-pattern `3` as if it were a raw native int, and `print` unboxes
  it back to `3` — explaining the exact garbage value reported below.
- **text? case:** no `BoxInt` wrapping is inserted (return type is text), so
  the raw tagged-nil bit-pattern `3` reaches `print` directly, which decodes
  it as `TAG_SPECIAL`/`SPECIAL_NIL` and prints nothing (the blank line).

## Fix

Changed the fallback mapping in `try_compile_builtin_method_call` from
`rt_enum_payload` to `rt_unwrap_or_self` — a runtime function that already
existed for the `??` operator with exactly the right fallback semantics: "if
it's a Some enum, return its payload; otherwise return the value itself
(could be a raw string, int, etc.)". This fixes flat-nullable/type-erased
`.unwrap()` without touching genuine-Enum-receiver behavior (still extracts
the payload correctly for a real `Some(x)`/`Ok(x)`).

While verifying the "explicit `Some(9)`" control case under the seed's
*default* execution mode (not the forced-interpret mode used to hand-verify
the doc's original repro), a second, closely-related defect was found and
fixed in the same patch: `Some(value)`/`Ok(value)`/`Err(value)` construction
(`compiler/src/mir/lower/lowering_expr_call.rs`) stored scalar payload values
(e.g. `Some(9)`'s `9`) directly into the enum object without boxing them into
tagged `RuntimeValue`s first — unlike the general user-defined-enum
construction path a few lines below it, which already does this boxing (see
`doc/08_tracking/bug/enum_field_i64_zero_destructure_2026-04-28.md`). This
made `Some(9).unwrap()` print `<invalid-heap:0x9>` under the default JIT path
(raw `9`'s low 3 bits accidentally equal `TAG_HEAP`). Fixed by boxing the
payload the same way the general enum-construction path does, for all 6
`Some`/`Ok`/`Err`/`Option.Some`/`Result.Ok`/`Result.Err` construction sites.

## Symptom

Flat-nullable optional values (declared as `T?` and assigned a bare value) misunwrap when using `.unwrap()`:

```spl
fn main():
    val n: i64? = 100
    print(n.unwrap())
    
    val t: text? = "opt"
    print(t.unwrap())
    
    val explicit = Some(9)
    print(explicit.unwrap())
```

Observed output:
```
3
<empty line>
9
```

Expected output:
```
100
opt
9
```

Control: explicit `Some(9).unwrap()` correctly prints `9`, proving the `.unwrap()` path for explicitly-constructed Some values is correct. Only the **flat nullable form** (`val x: T? = value` assigned a bare value, not wrapped in Some) mis-unwraps.

## Details

- **i64? case:** `val n: i64? = 100; n.unwrap()` prints `3` instead of `100`. The value `3` is consistent with the seed's known BoxInt tag/shift landmine class (see cross-reference: `doc/08_tracking/bug/` docs mentioning `box_int` or `tag-box`).
- **text? case:** `val t: text? = "opt"; t.unwrap()` prints an empty line instead of `"opt"`.
- **nil case:** `val x: i64? = nil; x.unwrap()` still panics correctly (behavior expected, not verified for this bug).
- **Workaround:** Use explicit `Some(value)` construction instead of flat-nullable assignment, or document explicit expected values in harness tests and compare against those instead of the oracle.

## Impact on parity harness

Any test case using flat-nullable optional values with `.unwrap()` cannot trust the oracle for comparison. The seed's output is corrupted and will produce false negatives (correct native code marked as wrong due to oracle corruption) or cause the harness to skip/annotate the case.

Examples of affected patterns:
- `val result: MyType? = compute_value(); val x = result.unwrap()`
- `filter()` / `map()` chains that unwrap optional field extraction

## Root cause hypothesis

Seed interpreter representation mismatch for flat-nullable optionals at the `.unwrap()` call site. Unlike explicit `Some(value)`, the flat form may store the value using a different tagged representation (possibly a BoxInt wrapper as evidenced by the i64→3 corruption pattern). The `.unwrap()` method in the seed may not account for this alternate representation.

Precedent: seed's known flat-Option representation bugs (see `native_text_option_unwrap_pointer_value_2026-07-15.md`, which this bug was discovered while verifying).

## Next steps

1. ~~Seed-side investigation~~ DONE — see Root Cause / Fix above; actual files were
   `compiler/src/codegen/instr/closures_structs.rs` (`unwrap`/`unwrap_or` runtime mapping)
   and `compiler/src/mir/lower/lowering_expr_call.rs` (`Some`/`Ok`/`Err` payload boxing).
2. Do NOT apply native-side workarounds (e.g., special-casing `.unwrap()` calls in parity harness). This bug is a seed defect; working around it hides the root cause.
3. When the seed is next rebuilt (post-native-build campaign) **and explicitly redeployed by the user**, verify the flat-nullable `.unwrap()` path against these test cases — already verified on a freshly built (not-yet-deployed) binary, see `s5_seed_interp_report.md` in the scratchpad path above for the transcript.

## Workaround (oracle-side)

For parity test cases requiring Optional `.unwrap()` semantics:
- Replace `val x: T? = value; x.unwrap()` with `val x = Some(value); x.unwrap()`
- Or pre-compute and document the expected value, comparing native output against it rather than the oracle

## Not a native path bug

Native-build's handling of flat-nullable `.unwrap()` is correct (verified by `native_text_option_unwrap_pointer_value_2026-07-15.md` which shows native prints `"opt"` as expected). This is a seed-only (Rust interpreter) defect.
