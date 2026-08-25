# LLM Caret JSON parse path: `json_parse` nil-contract + `any?` Option-wrap — 2026-08-25

Status: FIXED (std layer, 2026-08-25, uncommitted) — see "Fix and evidence" below.
The parse-nil-contract and `any?` Option-wrap class is closed in std; caret
code is NOT changed. Residual reds in `claude_cli_spec` / `provider_spec` are
DIFFERENT defect classes, split out at the bottom.

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

**Superseded 2026-08-25** — closed at the std layer by unannotating the
accessors (see "Fix and evidence"); the seed defect itself stands, tracked in
`free_fn_optional_wrap_2026-06-26.md`.

Seed: free-function `T?`/`any?` returns must not Option-wrap (see
`doc/08_tracking/bug/free_fn_optional_wrap_2026-06-26.md`), after which
`json_parse` can be declared `-> any?` and `parsers_json_core_spec` +
the five specs above go green together. Re-verify with
`bin/simple test test/01_unit/app/llm_caret/claude_cli_spec.spl`.

Related: `doc/08_tracking/bug/non_optional_wrappers_return_nil_sweep_2026-08-21.md`.

## Fix and evidence (2026-08-25)

Measured first on the fresh seed (clean origin/main `684fadabcae` checkout) with
a 6-example probe: `-> any` returning nil traps
(`nil is forbidden by the non-optional return contract`), `-> any?` returning
a value Option-wraps it (`cannot convert enum to float`, `as i64` == 0), and an
**unannotated** return passes both legs. So the fix is to drop the return
annotation on every JSON accessor whose documented contract is
value-or-nil; the (tag, payload) tuple representation and nil-on-failure
contract are unchanged, and no caller was edited (125 call sites counted;
18 sampled across 8 files, all value-or-nil usage: `== nil`, `as i64`,
arithmetic on the unwrapped value).

Files (std only, zero `src/app/llm_caret` edits):
- `src/lib/common/json/parser.spl` — `json_parse` (`-> any` dropped; comment rewritten)
- `src/lib/common/json/types.spl` — `json_to_boolean/number/string/array/object` (`-> any?` dropped)
- `src/lib/common/json/object_ops.spl` — `json_object_get`, `json_object_find`
- `src/lib/common/json/array_ops.spl` — `json_array_get`, `json_array_last`, `json_array_find`
- `src/lib/common/json/path_ops.spl` — `json_path_get`
- `src/lib/common/json/validation.spl` — `json_deep_clone`
- new reproducer: `test/01_unit/lib/common/parsers_json_return_contract_spec.spl`
  (before fix: `Results: 10 total, 3 passed, 7 failed` — quoting
  `semantic: nil is forbidden by the non-optional return contract of 'json_parse'`,
  `semantic: type mismatch: cannot convert enum to float`, `expected 0 to equal 2`;
  after: `Results: 10 total, 10 passed, 0 failed`). The before-line is the
  initial revision of the spec; its nested-null example was later rebuilt via
  `+` concatenation to dodge the separately-filed `}}` lexer bug, the other 6
  failures are the contract class verbatim.

Before/after `Results:` lines (same seed, same tree, one spec per run):

| spec | before | after |
|---|---|---|
| `test/01_unit/lib/common/parsers_json_core_spec.spl` | `94 total, 92 passed, 2 failed` | `94 total, 94 passed, 0 failed` |
| `test/01_unit/app/llm_caret/claude_cli_spec.spl` | `84 total, 54 passed, 30 failed` | `84 total, 66 passed, 18 failed` (residual, see below) |
| `test/01_unit/app/llm_caret/provider_spec.spl` | `36 total, 29 passed, 7 failed` | `36 total, 35 passed, 1 failed` (residual, see below) |
| `test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl` | `3 total, 1 passed, 2 failed` | `3 total, 3 passed, 0 failed` |
| `test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl` | `3 total, 2 passed, 1 failed` | `3 total, 3 passed, 0 failed` |
| `test/01_unit/app/llm_caret/opencode_cli_spec.spl` | `15 total, 13 passed, 2 failed` | `15 total, 15 passed, 0 failed` |
| `test/01_unit/lib/common/parsers_json_ops_spec.spl` | — | `64 total, 64 passed, 0 failed` |
| `test/01_unit/lib/common/json_logic_spec.spl` | — | `22 total, 22 passed, 0 failed` |
| `test/01_unit/lib/common/json_coverage_spec.spl` | — | `187 total, 187 passed, 0 failed` |

All six `cannot convert enum to float` examples and every nil-contract trap are
gone. Lint: parser/types/array_ops/validation 0 errors; object_ops and
path_ops each report pre-existing COLL001/COLL006 errors that are present
byte-identically on the HEAD versions (verified by linting `git show HEAD:`
copies) — not introduced here.

### Residual (NOT this class — left RED, filed separately)

1. **`}}` string-literal collapse (lexer)** —
   `doc/08_tracking/bug/string_literal_double_brace_collapse_2026-06-16.md`.
   `claude_cli_spec.spl` has 20 raw `}}` literals; each loses a brace at lex
   time, so `parse_claude_stream_line` correctly reports
   `invalid JSON in claude CLI stream` and the example fails with
   `expected 0 to equal 1/15/4/6`, `expected invalid JSON ... to contain must be numeric`, etc.
   Proven: the identical line built with `+ "}" + "}"` parses to
   `type=message_start in=25 out=1` on the fixed std. This is what the nil
   trap was masking. Fix belongs to the lexer, or the spec must build the
   literals via concatenation as `parsers_json_core_spec.spl` already does.
2. **`json_serialize` emits ints as floats and reorders keys**
   (`{"answer":42.0,...}` vs `{"answer":42,...}`) — 2 examples, std serializer,
   separate class.
3. **`provider_spec` "should preserve Claude CLI fields through advanced
   dispatch"** — `expected  to equal advanced-session`. `claude_cli_send`
   itself returns `session=[advanced-session]` on the fixed std (probed
   directly), so the field is dropped in `src/app/llm_caret/provider.spl`'s
   `dispatch_send_advanced` path — caret-owned.

### Residual follow-up (2026-08-25, second pass) — all three closed

Verified on the same fresh-seed worktree, one spec per run:

| spec | before (post json fix) | after |
|---|---|---|
| `test/01_unit/app/llm_caret/claude_cli_spec.spl` | `84 total, 66 passed, 18 failed` | `84 total, 84 passed, 0 failed` |
| `test/01_unit/app/llm_caret/provider_spec.spl` | `36 total, 35 passed, 1 failed` | `38 total, 38 passed, 0 failed` |
| `test/01_unit/lib/common/parsers_json_core_spec.spl` | `94 total, 94 passed, 0 failed` | `98 total, 98 passed, 0 failed` |
| `test/01_unit/lib/common/parsers_json_ops_spec.spl` | `64 total, 64 passed, 0 failed` | `64 total, 64 passed, 0 failed` |

1. **`}}` literal collapse** — spec-only fix. All 20 raw `}}` runs in
   `claude_cli_spec.spl` now end the literal at a single `}` and append
   `+ RB()` (the helper already imported from `std.mcp.helpers`); one
   mid-literal case (`...:4}},"session_id"...`) is split the same way.
   Assertions unchanged. The lexer bug itself stays open in
   `string_literal_double_brace_collapse_2026-06-16.md`.
2. **`json_serialize` ints / key order** — `src/lib/common/json/serializer.spl`
   gains `_json_serialize_number`: the parser stores every number as f64
   (`to_float()`), so an integral value in the exact-i64 band (|n| <= 2^53)
   now serialises as `42`, not `42.0`; fractions (`1.5`) unchanged, `1e3`
   -> `1000`. **Key order is NOT insertion order by design**: probed
   `{"zeta","alpha","mid"}.keys()` -> `[alpha, mid, zeta]`, i.e. the dict
   backing `json_object` is key-sorted, so no sorting was added and the one
   spec whose expected string was non-alphabetical
   (`structured_output` `name/items/note`) now asserts the members
   order-insensitively. Reproduce + similar cases (42, 0, -1, 1e3, 1.5, 2.5,
   nested array/object) added under `context "json_serialize"` in
   `parsers_json_core_spec.spl`. Lint of `serializer.spl`: the only errors
   are the two pre-existing COLL006 at lines 14/79, byte-identical on the
   HEAD copy; the new function adds 0 findings.
3. **`advanced-session` drop — NOT a provider.spl defect.** Probe
   (`bin/simple run`): `dispatch_send_advanced` and `claude_cli_send` both
   return `is_error=true, error="claude CLI exited with code 70: advanced CLI
   arguments were not forwarded", session=""` with the spec's arguments
   (`session_id=""`, `max_turns=0`, `tools=["Read"]`), and `claude_cli_send`
   returns `session=advanced-session` only with `"advanced-resume", 3,
   ["Read","Write"]` — exactly what
   `test/fixtures/llm_caret/mock_claude_cli.shs:143-151` enforces and what
   `test/03_system/.../llm_caret_claude_cli_advanced_spec.spl:39` already
   passes. The two unit examples (`provider_spec.spl` "preserve Claude CLI
   fields through advanced dispatch", `claude_cli_spec.spl` "forward advanced
   arguments and preserve response metadata") were stale against the
   tightened fixture; their arguments now match. `provider.spl` is unchanged
   (it forwards `resp.session_id` verbatim). Similar cases added to
   `provider_spec.spl`: session preserved on a plain `dispatch_send`
   (`fixture-success` -> `resume-1`), preserved on advanced send, and empty
   when the CLI fails closed (exit 70).

Consumer sweep for the number-format change: of the other `json_serialize`
specs only `test/01_unit/lib/common/json/json_control_char_escape_spec.spl:105`
pinned the old emission (`{"k\b":1.0}`, an example about key escaping, not
number format); updated to `{"k\b":1}` -> `9 total, 9 passed, 0 failed`.
