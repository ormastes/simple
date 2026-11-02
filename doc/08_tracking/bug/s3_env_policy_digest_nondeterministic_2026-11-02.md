# Frozen stage2 lowers `Result<text,_>?` as i64 in text concat/interp: handoff digests hash heap addresses

- **ID:** s3_env_policy_digest_nondeterministic_2026-11-02
- **Priority:** P1 (blocked every stage3 native-build)
- **Status:** open (workaround). The root cause is the same as `stage2_try_unwrap_text_typed_as_i64_2026-11-02`, which is fixed in source by 0528a9ed3ac. This id tracks the tagged source workaround in `environment_variant_policy_handoff_v1.spl` that the frozen stage2 still needs.
- **Found by:** phase-3 stage3 hello smoke (`C:/dev/p3new/linkdry/s3.exe`, objects from frozen stage2 ef0681fc0e1)

## Symptom
`native-build could not collect a valid environment variant policy: policy-encoding-failed:non-canonical`

## Root cause (stage2 miscompile, not a source or Windows-env bug)
In `src/compiler/00.common/structural_contracts/environment_variant_policy_handoff_v1.spl`, these sites use a
`Result<text,_>?` value inside text interpolation or `+`:
- line 138: `Ok("{name}={_handoff_hex_encode(value)?}\n")`
- lines 180 and 191-193: `out = out + _handoff_row(...)?`
- line 238: `val material = _handoff_material(...)?`, followed by `material + "integrity_digest=..."`

Stage2 types the unwrapped value as i64. It emits `rt_raw_i64_to_string` on the text handle, so the
material contains decimal heap addresses. The integrity digest therefore changes with every call, and
the recompute check in encode_v1 (line 236) fails.
Evidence: `rt_raw_i64_to_string` appears in `_handoff_row` and `encode_v1` of `aot-ff0e9939...o`.
A trace build printed the wire's first line as `2188812121569integrity_digest=...`, with nlines=2.

## Workaround
`@workaround bug=s3_env_policy_digest_nondeterministic_2026-11-02`. Each site binds through
`val x: text = match f(...): case Ok(v): v / case Err(e): return Err(e)`.
Semantics are unchanged and the validation is kept in full. The rebuilt object has no
`rt_raw_i64_to_string` in row/encode. The defined and undefined symbol sets are identical.

## Real fix
Already fixed in source by 0528a9ed3ac (see `stage2_try_unwrap_text_typed_as_i64_2026-11-02.md`, spec `test/01_unit/compiler/mir/try_unwrap_text_interp_concat_spec.spl`).

## Removal condition
Stage2 has been rebuilt from a compiler with the try-type fix, and the smoke passes without this workaround.
