# The Rust seed's parser is behind main's grammar, so `simple test` cannot run on this host
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-05 (macOS, aarch64)
**Status:** STALE 2026-11-11 (lane p3-comp9) — premise no longer holds at tip:
the grammar closure landed 2026-08-01 (rows
`parser_leading_operator_line_continuation_2026-08-01` /
`parser_trailing_operator_line_continuation_2026-08-01`, both FIXED) and the
tracked seed (46fe8f6b6def) now parses all three named stdlib files rc=0, runs a
stdlib-dependent spec under `test` 24/24, and passes both continuation specs
(8/8, 11/11). The filed host state (stale deployed seed, no working test lane)
is superseded by the current seed. See the dated addendum below.
**Severity:** blocks the whole test sweep on this host

## Symptom

`simple_seed test <dir>` never reaches a single example. It dies at module
load, and it dies at a *different* stdlib file each time one is worked
around — a chain, not a single defect:

| file | seed's parse error |
|---|---|
| `src/lib/common/perf/execution_metrics.spl:365` | `expected expression, found Indent` |
| `src/lib/nogc_sync_mut/mcdc/dynamic_aspect.spl:257` | `expected expression, found Assign` |
| `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` | `expected expression, found Dedent` |

## Root cause — the stdlib is NOT broken

Each of those files parses **cleanly** under main's own pure-Simple
compiler:

```
bin/local/phase2-aarch64-apple-darwin/simple compile --format=smf -o /tmp/o.smf \
    src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0
```

So the grammar main is written in is valid; the **Rust seed's parser is
behind it**. The two forms the seed rejected are both ordinary in this tree:

```simple
if a <= 0.0 or b < 0.0 or          # trailing operator, indented continuation,
        c <= 0 or d < 0:           # NOT wrapped in parentheses

if result: self.arr[slot] = self.arr[slot] | bit   # inline `if` whose body assigns
```

## Why this was nearly mis-filed

Both sites were first "fixed" in source (parenthesise the condition; expand
the inline `if` to a block) and both fixes worked — which is exactly how a
stale-tool problem gets laundered into a permanent source workaround. The
edits were reverted once the phase2 binary proved the grammar valid. Nothing
in `src/lib/**` should be reshaped to please the seed.

## The real blocker

There is still no FULL-CLI pure-Simple binary deployed on this host:
`bin/simple`, `bin/release/aarch64-apple-darwin-macho/simple` and
`bin/local/phase2-aarch64-apple-darwin/simple` are all the BOOTSTRAP CLI
(`compile` / `native-build` only — `src/app/cli/bootstrap_main.spl`), and
`bin/release/aarch64-apple-darwin/simple_seed` is the Rust seed. So the only
binary with a `test` command is the one whose parser cannot read the tree.

Fix is a Stage-4 full-CLI redeploy, not a source change. Until then, the
per-spec lane `simple_seed run <spec>.spl` still works (it loads far fewer
modules) and is the only way to execute a spec on this host.

## Impact on the `@tag:in-development` lane

`src/lib/nogc_sync_mut/spec/in_development.spl` and its runner wiring were
restored the same day and the pure classification layer is verified
(`simple_seed run test/01_unit/lib/spec/in_development_tag_spec.spl` ->
21 examples, 0 failures). The **end-to-end** behaviour — a tagged failing
spec being neutralised in a real sweep — remains UNVERIFIED on this host for
the reason above, and is stated as unverified rather than assumed.

## Update 2026-09-05 (later the same day): the per-spec `run` lane is dead too

The closing sentence above is no longer true. `simple_seed run
test/03_system/plan_acceptance/sspec_modernization_plan_spec.spl` — a spec
that imports only `std.spec`, `file_ops`, `sha256` and two app modules — exits 1
with `error: semantic: variable `always_inline` not found` (the `@always_inline`
attribute in `src/lib/nogc_sync_mut/io/vulkan_sffi.spl`, reached through
`file_ops`). A one-line probe `use std.nogc_sync_mut.io.file_ops.{file_read}`
fails the same way, so any spec that reads a file cannot run under the seed.
`std.cli.cli_util` dies on the `execution_metrics.spl:365` grammar gap listed
above; `std.crypto.sha256` dies on `function unsafe not found`
(`secure_memory.spl:5` `@unsafe(...)`). What DOES load: `std.tooling.easy_fix.types`
and raw runtime externs (`rt_file_read_text`, `rt_file_exists`,
`rt_file_write_text`, `rt_file_hash_sha256`) — which is how
`scripts/check/sspec-score-seed-lane.shs` runs the sspec scorer here without
touching `src/`.


## Triage 2026-11-11 (lane comp9, worktree simple-p3-comp9-20261111, base 77be2266752d)

Verdict: **STALE** — the filed premise (the deployed Rust seed's parser is behind
main's grammar so `simple test` cannot run) no longer holds at this base. Fresh
evidence, all on the tracked seed bin/simple.exe @ 46fe8f6b6def
(`SIMPLE_LIB=src ... --mode=interpreter --no-cache`):

1. All three named stdlib files parse cleanly now:
   `src/lib/common/perf/execution_metrics.spl`,
   `src/lib/nogc_sync_mut/mcdc/dynamic_aspect.spl`,
   `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` — `compile --format=smf`
   rc=0 each, zero `expected expression, found ...` diagnostics (the third emits only
   unrelated cross-module private-signature warnings).
2. The seed `test` lane — "never reaches a single example" per this row — now runs a
   stdlib-dependent spec end to end: `test/01_unit/lib/spec/in_development_tag_spec.spl`
   outcome=OK, executed=24 passed=24 failed=0 via `bin/simple.exe test ...` itself
   (the row body recorded only the per-spec `run` lane at 21 examples).
3. Both grammar pins pass: `test/01_unit/compiler/parser_trailing_operator_continuation_spec.spl`
   8/8 and `test/01_unit/compiler/parser_leading_operator_continuation_spec.spl` 11/11
   — covering exactly the trailing-operator indented-continuation form in this row's
   root-cause section. The source closure is recorded FIXED 2026-08-01 in
   `doc/08_tracking/bug/parser_leading_operator_line_continuation_2026-08-01.md` and
   `parser_trailing_operator_line_continuation_2026-08-01.md` ("the seed/self-hosted
   divergence is now CLOSED in source"); the only residue those rows name is the old
   deployed binary, which the 2026-11-11 tracked seed supersedes.

Absorbers: the 2026-08-01 operator-continuation grammar-fix family (source, both rows
above) + the seed-fix lane's regular seed rebuilds/redeploys that produced the
current tracked binary. What this row does NOT settle (left to the named owners):
- the same-indent leading-operator disambiguation for `+`/`-`
  (`parser_same_indent_leading_operator_continuation_2026-08-17`, BLOCKED — language
  owner + seed-build lane); tracked separately, not a blocker for this row's premise;
- the macOS-host Stage-4 full-CLI deployment this row names as "the real blocker" —
  host infrastructure, not a compiler-source defect.

Disposition: STALE. Header flipped OPEN → STALE 2026-11-11 (lane p3-comp9).
