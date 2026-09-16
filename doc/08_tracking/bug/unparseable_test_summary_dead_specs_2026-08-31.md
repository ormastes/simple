# Unparseable pass/fail summary: specs that execute nothing (2026-08-31)

Suite run `/tmp/suite4.log` (ephemeral; binary from `4b4e2a304b4`, identified durably as the 60914128-byte binary dated 2026-08-31 13:46 — see Method note) produced 6 occurrences of
`Error: no parseable pass/fail summary in test output; refusing synthetic pass`.

**The refusal is correct and must not be weakened.** In every reproduced case the
spec genuinely executed zero examples. The parser is not at fault; the specs are.
Do NOT teach `output_has_zero_pass_summary`
(`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`) to accept the
`"N examples, M failures"` form — that would convert dead specs into silent
zero-green, which is the exact false-green class the refusal exists to block.

## Method note

The binary matters. `bin/simple` in the shared tree (2026-08-26) is an older seed
that cannot parse current `src/app/io/mod.spl`; it produces failures unrelated to
this class. All findings below were reproduced with the suite's own binary
(`/mnt/data/wt-suite/bin/release/x86_64-unknown-linux-gnu/simple`, 60914128 bytes,
2026-08-31 13:46) under the suite's lane, `SIMPLE_MCDC_MODE=on` (NOT `--coverage`
— `test_runner_execute.spl:1049` gates the mcdc fallback on
`mcdc_enabled and not options.coverage`, so `--coverage` takes a different path
and does not reproduce).

## Root causes — all category (a), the spec emits no summary

| spec | cause | status |
|---|---|---|
| `test/01_unit/std/cp_spec_test.spl` | `describe` nested inside a never-called `fn test():` — 2 real tests never ran | FIXED |
| `test/01_unit/lib/std/language/mixin_static_poly_integration_spec.spl` | leading `"""` docstring (lines 1-127) swallowed an injected `use std.spec.step` + `describe` with 3 real `it` blocks; the injector also dropped the `std.common.convert` import | FIXED |
| `test/feature/usage/async_effects_spec.spl` | doc-only spec whose `describe` body was a bare `pass`: zero examples registered | FIXED (declared via `pending`) |
| `test/fixtures/visibility_test/case_spec.spl` | **not a bug** — a deliberate test-infra fixture (a module with no tests, named `_spec.spl`) whose FAIL proves the runner reports failure at all. Listed "unfixable by design, do not touch" in `source_grep_guard_specs_blocked_on_selfhosted_binary_2026-08-26.md` | WORKING AS INTENDED |
| `test/feature/lib/mcp/bootstrap_protocol_test.spl` | OPEN — see below | FILED |
| `test/01_unit/std/no_paren_test.spl` | OPEN — see below | FILED |

The mixin case is the important one: the file's only live content was 8
`describe ... expect true` placeholder blocks that register no examples at all,
while its 3 genuine assertions sat inside a string literal. Reviving them
immediately surfaced a real defect (`semantic: function i64_to_text not found`),
which the missing import fix resolves.

## OPEN 1 — `test/feature/lib/mcp/bootstrap_protocol_test.spl`

A hand-rolled `fn main()` checker that prints `✓`/`✗` lines and
`Some checks failed (3/4)`, then **exits 0**. It emits no runner-parseable
summary AND swallows a genuine failure into a success exit status. Converting it
to the `describe`/`it` DSL is the right fix, but it will then legitimately go RED
(the failing check is "Errors found in output", caused by an MCP export warning),
so it needs the underlying export issue resolved in the same change.

## OPEN 2 — `test/01_unit/std/no_paren_test.spl`

Not reproduced. Standalone it emits a fully parseable
`SPEC FILE VERDICT ... executed=3 passed=3` and PASSes under `bin/simple test`,
under `--coverage`, and under `SIMPLE_MCDC_MODE=on`, solo and 6-way concurrent.
Its suite failure is suite-only and remains unexplained. Suspicion is structural,
not empirical: the wrapped-source temp path is derived from the test path ALONE,
with no pid/worktree/run uniquifier —
`src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl:583`
(`"/tmp/spipe_wrapped_" + file_path.replace("/", "_")`) and
`src/app/test_runner_new/test_runner_execute.spl:500` (identical), while
`cleanup_native_generated_file` deletes that same path. Two concurrent runs of
the same spec from different worktrees therefore write, compile, and delete one
shared file. Adding a pid suffix is safe (`driver_source_file.spl:40` and the
discovery filters key on the `spipe_wrapped_` PREFIX, not the whole name), but it
is hardening, not a demonstrated root cause.

Also observed during this investigation: `/mnt/data` reached 100% full. A
`file_write` of a wrapper failing on ENOSPC would produce an empty wrapper and
hence exactly this signature. Unverified for the 13:46 suite run.

## NOT a bug — the malformed-looking `function not found", stderr);;` text

Two occurrences of
`* \`fatal error: 'unistd.h' file not found\`, so it never reached the core-C; fputs("Simple runtime error: function not found", stderr);; "The interpreter ref...`
belong to `test/01_unit/lib/nogc_sync_mut/concurrent/channel_scalar_abi_spec.spl`
(a genuine `1 passed, 2 failed` result). That spec does
`file_read_text("src/runtime/runtime_native.c")` and asserts `to_contain(...)`;
on failure the matcher embeds the actual value, which is literally C source from
`src/runtime/runtime_native.c` — the only file in the tree containing
`fputs("Simple runtime error: function not found`. So this is **quoted source in
a failing assertion's diagnostic, not a diagnostic constructed from stray source
fragments**. No bug in the message constructor. Diagnostic quality is arguably
poor (unbounded actual-value spew from a whole-file `to_contain`), but that is a
separate, lower-priority concern.

## Residual: docstring-swallowed spec code elsewhere

A scan for files whose LEADING `"""` docstring closes only after a `describe`/`it`
line found 19 candidates. Rule: the file's first line is a bare `"""`; find its
closing partner (the next bare `"""`); report the file if any line between them
matches `^(describe|it)\s+["']`. Scanner, kept here so the finding stays
reproducible:

```python
import os, re
for root, _, fs in os.walk('test'):
    for fn in fs:
        if not fn.endswith('.spl'): continue
        p = os.path.join(root, fn)
        lines = open(p, encoding='utf-8', errors='replace').read().split('\n')
        if not lines or lines[0].strip() != '"""': continue
        close = next((i for i in range(1, len(lines))
                      if lines[i].strip() == '"""'), None)
        if close is None:
            print('UNCLOSED', p); continue
        bad = [(i + 1, lines[i].strip()[:45]) for i in range(1, close)
               if re.match(r'^(describe|it)\s+["\']', lines[i].strip())]
        if bad: print(p, bad[0], 'n=', len(bad))
```
 Only the mixin spec above is confirmed and fixed; the "UNCLOSED" entries
may be scanner artifacts (a closing `"""` with trailing content on the line is not
matched) and each needs spot-checking before any edit. An earlier count of 1139
was a scanner artifact from naive triple-quote parity and is retracted.
