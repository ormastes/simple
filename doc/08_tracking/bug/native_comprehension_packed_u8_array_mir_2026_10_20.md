# Self-hosted MIR rejects a list comprehension over a packed [u8] array

- Canonical id: native_comprehension_packed_u8_array_mir_2026_10_20
- Date: 2026-10-20
- Status: open (workaround active)
- Producer: producer4 strict (`simple-producer4-strict.exe`, source 02ca146 + 81e50f5d441),
  phase-3 native-build of `src/app/cli/bootstrap_main.spl`, x86_64-pc-windows-msvc, llvm.
- Original failure: `E-MIR-EXPR-Comprehension: unsupported in stage2: comprehension over a
  packed [u8]/[u64] array (its slots are raw, not tagged); index it in a while loop` at
  `src/compiler/10.frontend/frontend_advisory_preprocess_port_v1.spl:90`
  (`sha256_bytes([value as i64 for value in text_to_bytes(source)])`). The Rust seed compiles
  the same source.
- Workaround: the comprehension is rewritten as a counted `while` loop that widens each byte
  to i64, marked `# @workaround bug=native_comprehension_packed_u8_array_mir_2026_10_20`.
  Recovery reference for the original form: `35123ed70c0`.
- Root fix needed: comprehension lowering in `src/compiler/50.mir` must read packed byte/u64
  slots raw (as the indexed for-in path already does) instead of rejecting them.
- Retirement: restore the comprehension once the root fix lands and a rebuilt producer lowers
  the original form.
- DB reconciliation: pending (no qualified `check-dbs` CLI on this host).

## 2026-11-04 fix (n88b, opus-n88b): status fix-implemented-verification-pending

`lower_list_comprehension` (`src/compiler/50.mir/_MirLoweringExpr/builtin_method_extras.spl`)
now accepts a packed `[u8]` source: the element is read raw through `rt_bytes_u8_at` (the
accessor `lower_for_array_indexed` and `arr[i]` use) and cast to `u8`, with no tagged decode.
`[u64]` stays fail-closed (message now says `[u64]`). Minimal change in 50.mir; coordinate with
the phase-3 MIR owner (agent a508755bae341480a).

- TDD spec (runs now under the seed): `test/01_unit/compiler/mir/comprehension_packed_u8_spec.spl`
  (fixture `comprehension_packed_u8_engine_fixture.spl`) - failed before ("comprehension over [u8]
  still rejected"), passes after; asserts one `rt_bytes_u8_at` read, zero `rt_array_get`, and that an
  `[i64]` comprehension still uses tagged `rt_array_get`.
- Native repro, exact stage3 command: `bin/simple native-build test/fixtures/native/comprehension_packed_u8/main.spl`
  then run the exe; stdout must equal `test/fixtures/native/comprehension_packed_u8/expected_output.txt`
  (`PASS comprehension_packed_u8 65,66`). Engine control: `test/01_unit/compiler/mir/comprehension_packed_u8_engine_native.spl`
  must print `PASS comprehension-packed-u8-engine`.
- Retire the while-loop workaround in `frontend_advisory_preprocess_port_v1.spl:90` after the repro passes.

## 2026-11-05 reopen triage (verify-sweep s3_fable43 sha256 615859c5c2815f71; seed oracle bin/simple.exe sha256 8c7341592f4d47de)
Sweep failure (probe b0_g 'FAIL comprehension') was observed on the seed (engine-demotion to hybrid interp; Rust seed does not use lower_list_comprehension) and on s3_fable43, which predates or lacks the 2026-11-04 lower_list_comprehension packed-u8 fix pin. The fix is source-only and cannot be exercised by the seed. Verification step unchanged: native-build test/fixtures/native/comprehension_packed_u8/main.spl on a stage3 containing the fix and compare to expected_output.txt, then retire the while-loop workaround at frontend_advisory_preprocess_port_v1.spl:90. Status stays fix-implemented-verification-pending.
