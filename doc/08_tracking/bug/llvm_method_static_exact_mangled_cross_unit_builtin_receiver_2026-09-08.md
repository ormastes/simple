# Exact mangled cross-unit free functions rejected as builtin methods

**Status:** OPEN (unverified 2026-09-12)

- Filed: 2026-09-08
- Severity: P0 Stage4 blocker
- Status: exact-mangled fix verified; three distinct fail-closed residuals block Stage2
- Owner: `src/compiler_rust/compiler/src/codegen/llvm/functions.rs`

## Pre-fix evidence

Both the canonical current-source Stage2 build and a direct Stage4 build failed
in 374 compilation units. Representative diagnostics were:

```text
cannot resolve method call compiler__frontend__core__types__str_len on builtin type
cannot resolve method call lib__common__convert__bool_to_text on builtin type
```

The direct attempt ran for 3654.28 seconds, peaked at 3,913,531,392 bytes RSS,
and produced no candidate. Evidence is retained in
`build/macos-stage4-direct/stage4-native-build.log`; canonical Stage2 evidence
is in `build/macos-stage4-deploy/logs/aarch64-apple-darwin/stage2-native-build.log`.

## Root cause and fix

The fail-closed builtin-receiver guard correctly rejects synthetic unresolved
names such as `text.split_whitespace`, but also rejected fully mangled exact
link identities transported through `MethodCallStatic`. The defining unit is
separate, so the declaration is expected to be absent from the current LLVM
module. Exact names containing `__` and containing neither `.` nor `_dot_` are
now declared unchanged. The synthetic builtin-method path remains fail-closed.

## Focused verification

`builtin_receiver_exact_mangled_free_function_is_declared_cross_unit` passed:
the generated IR declares
`compiler__frontend__core__types__str_len`, does not invent
`text.str_len`, and passes LLVM verification. The adjacent existing
`ufcs_builtin_receiver_unresolvable_method_fails_closed` test remains unchanged;
its detached test command completed after the terminal receipt was lost, so no
PASS is claimed for that invocation. Full current-source Stage4 is the required
acceptance test remains blocked. The final capped canonical cycle eliminated
all 374 exact-mangled failures and rebuilt the Rust seed, native-all runtime,
non-LTO runtime, and compiler backfill. Stage2 then failed on only three files:

- `virtual_source_registration_v1.spl`: unresolved `virtual_source_store`
- `dirty_module_record.spl`: unresolved `str.split_whitespace`
- `compile_source_inventory.spl`: unresolved `str.split_whitespace`

These are not exact mangled cross-unit identities and therefore were not
admitted by this fix. No Stage4 candidate or deployment was produced.

## Triage 2026-09-12
No cheap repro attempted in this bulk pass (rule D: newer than 45 days, left open). Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
