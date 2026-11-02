# stage2: `?`-unwrapped Result<text, _> typed as i64 in text contexts

Status: fixed-in-source (by 0528a9ed3ac, 2026-10-30); present only in the frozen
stage2 binary `C:/dev/p3new/stage2.exe` (source ef0681fc0e1, which does NOT
contain 0528a9ed3ac). P0 for the stage3 self-build only in the sense that the
stage2-compiled stage3 must not be trusted for affected sources until stage3
is itself rebuilt from current source.

## Symptom

`"a{f()?}"` / `"a" + f()?` where `f() -> Result<text, _>`: the Ok payload from
`rt_enum_payload` stays an i64-typed MIR local, so `coerce_concat_operand`
(src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1854) renders the heap
handle through `rt_raw_i64_to_string`. Heap addresses end up in hashed text:
environment_variant_policy_handoff_v1.spl:138/180/191-193/238 at df3a14d194b,
see `s3_env_policy_digest_nondeterministic_2026-11-02.md` (p3-envpol worktree).

## Root cause

`lower_try_expr` (src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:5388,
Result branch ~5620) passes the payload to `decode_declared_enum_payload_slot`
(src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl:480). At
ef0681fc0e1 that decoder had no `HirTypeKind.Str` arm: it kept the i64 carrier
and only remembered the HIR type, while `local_is_str` keys off the MIR local
type, so the concat/interp path picked `rt_raw_i64_to_string`.

## Fix

0528a9ed3ac added the Str arm (`option_text_value(raw, bootstrap_text_type())`),
restoring the text ABI + MIR type. `lower_try_expr` itself is byte-identical
between ef0681fc0e1 and release/1.0.0.

## Tests

- test/01_unit/compiler/mir/result_try_text_payload_spec.spl (existing; `val x = f()?` then concat/trim)
- test/01_unit/compiler/mir/try_unwrap_text_interp_concat_spec.spl (new; interpolation,
  inline `+`, compare, text argument; static MIR check + execution). NOT EXECUTED in
  this session: bin/simple is a stale seed.

## Removal

Retire the tagged workaround once stage3 is rebuilt from a tree containing
0528a9ed3ac and the env-policy digest is deterministic.

## Workaround (stage3 closure, 2026-11-02)

The s3 self-build is still produced by the frozen stage2, so the affected
stage3-closure sources were rewritten into the typed-local form, tagged
`# @workaround bug=stage2_try_unwrap_text_typed_as_i64_2026-11-02`:

    val x: text = match f(...):
        case Ok(v): v
        case Err(e): return Err(e)

Earlier `?` operands of the same statement are hoisted in source order so
the first failing `?` still returns. Scope is `Result<text|str, _>` only:
`[u8]`/array payloads go through `runtime_array_locals` and `Option<text>`
through `option_text_value` at ef0681fc0e1. 274 sites in 51 modules were
rewritten here. The env-policy handoff and driver parse files belong to the
parse-path lane (s3_env_policy_digest_nondeterministic_2026-11-02). The
regression spec is test/01_unit/compiler/mir/try_text_typed_match_workaround_spec.spl.

Removal: once stage3 is rebuilt by a compiler containing 0528a9ed3ac, revert
the tagged sites (`rg 'bug=stage2_try_unwrap_text_typed_as_i64_2026-11-02' src`).
