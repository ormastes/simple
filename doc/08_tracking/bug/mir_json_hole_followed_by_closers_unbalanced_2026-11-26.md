# mir_json and other emitters drop a closing brace after an interpolation hole

- id: mir_json_hole_followed_by_closers_unbalanced_2026-11-26
- severity: P2
- status: verified (seed, this host, 2026-11-26)

## Symptom

`"{\"A\":{\"t\":{t}}}"` prints `{"A":{"t":7}`. In an interpolating literal EVERY
`}}` is one literal `}` (and `{{` one `{`), whether or not it follows a hole;
the hole closes at its own `}`. Two literal closers must be written `}}}}`.
Both lexers agree: the seed decodes it this way, and the self-hosted MIR split
(`split_interpolation_segments`) keeps `}}` as one escaped brace.

`serialize_mir_type` / `serialize_mir_inst_kind` emitted unbalanced JSON
for every nested shape (Ptr, Ref, Array, Dict, Alloc, Copy, BinOp, Call,
Cast, Aggregate, ...): strict parse failed with `Unclosed object`.
`serialize_mir_function` output feeds `native_capsule_mir_identity`,
`runtime_std_native_sections_v1` and mir_opt change detection. Those use
it as an identity text, not as JSON, so their digests change once.

## Sites fixed

- `src/compiler/50.mir/mir_json.spl`: 48 literals, `}}}"` -> `}}}}}"`. Also
  `:387` (TransferIn) and `:565` (DebugValue), which ended `\"}}"`.
  (`:182` Const Struct was already fixed by the brace-lexer landing.)
- `src/lib/nogc_sync_mut/lsp/main_wasi.spl:171` (initialize result, 3 closers).
- `src/os/compositor/host_compositor_core.spl:1395`.
- `src/app/sspec_maintain/report.spl:62`, `src/app/sspec_maintain/main.spl:59`.
- `src/app/sspec_maintain/main.spl:61` (SARIF error: driver/tool and message
  closers, two short); `report.spl:69` (fix replacement), `:75` (result
  region/location), `:88` (driver/tool): SARIF output was invalid JSON.
- `src/app/cli/query_commands.spl:201-202` (quickfix code action).
- `src/app/cli/query_commands.spl:175` (`]}}` closed one of `changes`/`edit`).
- `src/compiler/35.semantics/lint/security_raw_html.spl:152,156`: `"{{{"`
  decodes to 2 chars, so the 3-char slice compare never matched and the
  raw-HTML lint (WARN) was dead.

Judged correct and unchanged: `{{...{x}}}` forms (an escaped opener paired
with a hole then one escaped closer), `text_transforms.spl:39` (`{key}`
placeholder, as documented), `lua_backend.spl:247`, `regex_api.spl:488,494`.

## Evidence

Seed `/home/yoon/.cache/cargo-target-wr-seed1126b/release/simple`:

- `test/01_unit/compiler/mir/mir_json_strict_json_spec.spl` (strict parse of
  types, Alloc/Copy/Move/TransferIn/DebugValue, Const Struct, plus a source scan
  that decodes every self-contained object literal by seed rules and strict-
  parses it, over mir_json.spl, sspec_maintain/main.spl, lsp/main_wasi.spl):
  red 0/3 on origin; red 2/4 at the first fix (scan named :387, :565,
  main.spl:61); green 4/4.
- `test/01_unit/app/sspec_maintain/report_multi_render_spec.spl` new row
  (strict-parse multi- and single-report SARIF, with a fix present): red 3/4,
  green 4/4. scoring_spec 19/21 fails the same two tests on origin.
- `test/01_unit/compiler/lint/security_raw_html_triple_brace_spec.spl`:
  red 0/1, green 1/1.
- The other fixed sites were strict-parsed under the seed with stub values
  (scratch harness); all parse.
- Regression: mir specs unit_div_remainder_native 8/8,
  optional_array_ifval_payload 9/9, and mir_opt_capsule_immutability 6/6.
  logical_short_circuit_lowering (7/10) and dict_key_text_probe_bitcast
  (4/5) fail identically on origin (same failing-test set).
