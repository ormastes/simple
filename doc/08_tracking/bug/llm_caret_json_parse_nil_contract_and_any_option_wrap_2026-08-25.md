# LLM Caret JSON parse path: `json_parse` nil-contract + `any?` Option-wrap — 2026-08-25

Status: OPEN (P1) — std/seed defect surfacing in `src/app/llm_caret`; caret code
is NOT changed (see "Why not worked around" below).

## Affected specs (all RED, fresh seed built from origin/main `684fadabcae`)

| spec | Results: | failing examples |
|---|---|---|
| `test/01_unit/app/llm_caret/claude_cli_spec.spl` | `84 total, 54 passed, 30 failed` | every parse/stream example |
| `test/01_unit/app/llm_caret/provider_spec.spl` | `36 total, 29 passed, 7 failed` | 6 x `cannot convert enum to float`, 1 x `expected  to equal advanced-session` |
| `test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl` | `3 total, 1 passed, 2 failed` | ordered stream / malformed stream |
| `test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl` | `3 total, 2 passed, 1 failed` | CLI child prints `error: semantic: type mismatch: cannot convert enum to float` |
| `test/01_unit/app/llm_caret/opencode_cli_spec.spl` | `15 total, 13 passed, 2 failed` (after the nested-find spec fix) | raw fallback / malformed JSON |

On the deployed 2026-08-23 seed (`bin/release/x86_64-unknown-linux-gnu/simple`,
md5 `8773f4cc…`) `claude_cli_spec` is worse: `84 total, 33 passed, 51 failed`,
every one `semantic: invalid operation: cannot index value of type enum`.

## Two distinct symptoms, one call path

Call sites: `src/app/llm_caret/claude_cli.spl:249` and `:340`
(`val parsed = json_parse(raw)`), `src/app/llm_caret/opencode_cli.spl:83`;
numeric validation `claude_cli.spl:27-29` (`_json_i64`) and `:61-80`
(`_json_usage_kinds_valid`).

1. **`nil is forbidden by the non-optional return contract of 'json_parse'`.**
   `src/lib/common/json/parser.spl:592` declares `fn json_parse(text) -> any`
   and its docstring pins "nil otherwise"; line 605 returns `nil`. The fresh
   seed enforces the non-optional contract at runtime, so every malformed-input
   example dies before the caller's `if parsed == nil` check. std's own
   `test/01_unit/lib/common/parsers_json_core_spec.spl` fails the same way
   (`94 total, 92 passed, 2 failed`: "returns nil for empty string",
   "returns nil for malformed input"). The comment above `json_parse`
   explains why `-> any?` was NOT adopted (Option-wrap regresses the
   `.0/.1` tuple access) — symptom 2 is that very bug.
2. **`type mismatch: cannot convert enum to float`** and `d as i64` == 0.
   `src/lib/common/json/types.spl:219` `fn json_to_number(value: any) -> any?`
   returns `value.1`; the free-function `any?` return is Option-wrapped, so
   the caller receives an enum. Minimal repro (run as a spec on the fresh seed):

   ```
   val p = json_parse("{\"a\": 150}")
   val d = json_to_number(json_object_get(p, "a"))
   expect(d < 0.0).to_equal(false)      # semantic: cannot convert enum to float
   val i = if d == nil: 0 else: d as i64
   expect(i).to_equal(150)              # expected 0 to equal 150
   ```
   Reading the payload directly (`if json_get_type(v) == "number": v.1`)
   passes on the fresh seed but hits `cannot index value of type enum` on the
   deployed seed, so no caret-local form is green on both trees.

Also folded in (same specs, std serializer): `json_serialize` re-emits
integers as floats and reorders keys —
`expected {"answer":42.0,"labels":["a","b"]} to equal {"answer":42,...}`,
`{"items":[1.0,2.0],"name":"Simple",...}` vs `{"name":"Simple","items":[1,2],...}`.

## Why not worked around in llm_caret

`json_parse_with_error` (tuple return) does not trip the nil contract, and a
direct-payload number read avoids the wrap on the fresh seed — but the deployed
seed rejects the payload access, the rewrite would touch the whole usage
validation path in `claude_cli.spl`, and the contract being violated is std's
own documented one. Per `.claude/rules/testing.md` the specs stay RED.

## Unblock condition

Seed: free-function `T?`/`any?` returns must not Option-wrap (see
`doc/08_tracking/bug/free_fn_optional_wrap_2026-06-26.md`), after which
`json_parse` can be declared `-> any?` and `parsers_json_core_spec` +
the five specs above go green together. Re-verify with
`bin/simple test test/01_unit/app/llm_caret/claude_cli_spec.spl`.

Related: `doc/08_tracking/bug/non_optional_wrappers_return_nil_sweep_2026-08-21.md`.
