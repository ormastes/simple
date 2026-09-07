# Stage 3 blocked: the self-hosted parser rejects caseless `pattern -> body` match arms

**Status:** FIXED 2026-09-06 (parser + lexer, `src/compiler/10.frontend/core/`)
**Filed:** 2026-09-06
**Affects:** the self-hosted (Stage-2 / pure-Simple) frontend ONLY. The Rust seed
has always accepted the form.
**Severity:** HIGH — it blocked self-hosting outright.
**Regression spec:** `test/01_unit/compiler/frontend/match_arrow_arm_parse_spec.spl`
(16 examples)

## Symptom

The sanctioned bootstrap reached Stage 2 and then failed in Stage 3 PARSE:

```
[parser_error] path src/compiler/driver/driver_source_pipeline_parsing.spl
line 309:16: expected :, got -> '->'
```

(`src/compiler/driver` is the symlink to `src/compiler/80.driver`.) Lines 309-310
of that file are

```simple
    match validate_offload_profile(frontend_offload_profile(switch)):
        Ok(()) -> ()
        Err(message) -> return Err("frontend_offload_invalid_profile: " + message)
```

## Reproduction (minimal, 7 lines)

`scratch/repro.spl`:

```simple
fn probe(n: i64) -> text:
    match n:
        0 -> "zero"
        _ -> "other"

fn main():
    print "{probe(0)} {probe(7)}"
```

Rust seed (`bin/release/aarch64-unknown-linux-gnu/simple run`) — **accepts**:

```
zero other
```

Stage-2 pure-Simple compiler
(`build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple compile --format=smf`)
— **rejects**:

```
[parser_error] path scratch_arrow/repro.spl line 3:11: expected :, got -> '->'
[parser_error] line 3:11: unexpected token in expression: -> '->'
[parser_error] path scratch_arrow/repro.spl line 3:20: expected :, got Newline ''
[parser_error] line 4:11: unexpected token in expression: -> '->'
[parser_error] path scratch_arrow/repro.spl line 4:14: expected :, got StringLit 'other'
[ERROR] phase 2 FAILED (1 recorded error(s))
error: in-process SMF compile: parse error in scratch_arrow/repro.spl
```

## Which side was wrong: the SELF-HOSTED PARSER

The form is blessed Simple, not a seed-only extension:

1. `doc/07_guide/quick_reference/syntax_quick_reference.md` § Pattern Matching
   states **"Erlang-style `| ->` is preferred (shorter)"** — `->` is THE
   documented arm separator, and § Pattern Guards documents it with guards too.
2. The self-hosted parser ALREADY accepted the caseless spelling with two other
   separators — `pattern: body` and, since G28, `pattern => body` — neither of
   which appears in `doc/05_design/language/language_features/control_flow/
   match_arrow_syntax.md`'s EBNF (`arrow_arm := "|" pattern ... "->" expr`)
   either. That EBNF describes only the pipe-prefixed spelling and is already
   stale with respect to both compilers; it is not evidence that the caseless
   arrow is invalid.
3. Owned source uses the form widely and it PREDATES the change that exposed the
   break. Census 2026-09-06 — an awk scan for `->` lines inside `match` blocks
   matched **≈87 lines across 16 owned files**; the count is an upper bound
   (it also catches a return-type `extern fn ... -> text` and a `" -> "` string
   literal), and **14 of those files were confirmed by actually parsing them**
   (all clean after the fix). 18 in `src/lib/nogc_sync_mut/driver/loader.spl`
   (`driver_class_from_code()` is 15 consecutive `N -> return DriverClass.X`
   arms), 18 in `src/lib/nogc_async_mut/driver/loader.spl`, 10 in
   `src/os/drivers/gpu/gpu_vendor_probe.spl`, plus `sfm/manifest.spl`,
   three `gpu_driver/driver_adapter.spl`, `io/dma.spl`,
   `structural/component/descriptor.spl`, `backend/callback_trampoline.spl`,
   `backend/c_type_mapper.spl` and the two compiler-driver files. The seed's own
   Simple stdlib (`src/compiler_rust/lib/std/`, vendored) uses it ~1,000 times.

So this is a parser GAP, not a leniency to be normalised away. Per CLAUDE.md
Critical Rules the parser was fixed; the 24 arms were NOT rewritten.

## Root cause — TWO defects, both required for the fix

### 1. `parse_match_arms_common` had no `->` branch

`src/compiler/10.frontend/core/parser_stmts.spl`, caseless-arm path: after the
pattern list, the optional guard and the optional `as` binding, the separator
dispatch handled `TOK_FAT_ARROW` (G28) and otherwise `parser_expect(TOK_COLON)`.
`TOK_ARROW` (kind 167) hit the colon expectation, hence `expected :, got ->`.

Fix: an `elif par_kind_get() == TOK_ARROW:` branch that delegates to
`parse_block()` — **not** `parse_expr()`, which the `=>` inline path uses. An
arm body may be a STATEMENT (`Err(m) -> return Err(m)`,
`0 -> return DriverClass.Block`), and `parse_block()` is what the `:` spelling
already uses to cover the same-line statement, the same-line expression and the
indented block with one call.

### 2. The lexer suppressed the arm body's layout tokens

`token_requires_rhs()` (`core/tokens.spl:554`) returns true for `TOK_ARROW` so a
RETURN type may sit on the next physical line (`fn f() ->\n    i64:`). A trailing
`->` therefore suppresses the following Newline/Indent/Dedent. With only fix 1,
a block-bodied arm silently kept its FIRST statement and handed the second to the
arm loop as the next arm's pattern:

| source | with fix 1 only | with both fixes | `:` twin |
|---|---|---|---|
| `0 ->` + 2 indented stmts + nested `fn` | **FAIL** `expected :, got Newline` | parses | parses |
| `0 ->` with a dedented next line (no body) | **wrongly ACCEPTS** | error `expected Indent, got Dedent` | error, same text |

Fix: the arm branch calls `lex_mark_current_token_as_generic_close()` before
advancing past the arrow. That existing handoff clears the lexer's previous-token
kind so `token_requires_rhs` does not fire — the same mechanism the parser
already uses when `>` closes a generic rather than being binary greater-than. It
is scoped to the ARM arrow only, so return-type continuation is untouched
(verified by two regression scenarios, including a wrapped return arrow nested
inside an arrow arm body).

## Verification

Self-hosted parser exercised in-process via `parse_and_build_module`
(`compiler.frontend.flat_ast_bridge`) under the seed — the only way to run
`src/compiler/10.frontend/` today, since `bin/simple` is the Rust seed.

- All 14 owned files carrying arrow arms parse with `has_errors=false`,
  including `src/compiler/80.driver/driver_source_pipeline_parsing.spl`
  (30 functions) and `src/lib/nogc_sync_mut/driver/loader.spl` (17).
- The 16-example regression spec passes.
- Discrimination, measured: with the parser branch removed, every arrow scenario
  goes red with exactly `expected :, got -> '->'` while the `=>`, `:` and `case`
  scenarios stay green. With the parser branch present but the lexer handoff
  removed, the nested-declaration scenario goes red and the empty-body sabotage
  goes green-but-wrong.

Two spec classes ship with the fix, per `.claude/rules/testing.md`: the
reproducing scenarios (the exact `Ok(()) -> ()` / `Err(m) -> return ...` shape
and the 6-line repro) and the generalization scenarios probing the adjacent
paths — guard arms, `as` bindings, multi-statement and nested-declaration block
bodies, the empty-body sabotage with its `:` parity twin, and the `=>`, `:`,
`case` and return-type-continuation regressions.

## Proven on a REBUILT Stage 2, not only on the seed

`--full-bootstrap --stop-after-stage2 --mode=dynload` in an isolated worktree
(`SIMPLE_CACHE_SCOPE=arrow-arm-lane`, `--output=build/bootstrap-arrow`, never
deployed, `bin/simple` untouched). The host has no SDL2 and no sudo; the
`-lSDL2` blocker was sidestepped with a symbol-less `libSDL2.so` on
`LIBRARY_PATH` — a workaround, not a fix, and
`bootstrap_stage2_selfhost_link_requires_sdl2_2026-09-06.md` stands.

BEFORE — Stage 2 built from the UNFIXED source, sha256
`88cf297f2846d8b6635d797d96103b1cb05dd1c5da711e0bcddf424eeddbbb1f`,
152,381,584 bytes, `compile --format=smf` on the 7-line repro, **rc=1**:

```
[parser_error] path scratch_boot/repro/repro.spl line 3:11: expected :, got -> '->'
[parser_error] line 3:11: unexpected token in expression: -> '->'
[parser_error] path scratch_boot/repro/repro.spl line 3:20: expected :, got Newline ''
[parser_error] line 4:11: unexpected token in expression: -> '->'
[parser_error] path scratch_boot/repro/repro.spl line 4:14: expected :, got StringLit 'other'
[ERROR]   parse error in scratch_boot/repro/repro.spl
```

AFTER — Stage 2 built from THIS source, sha256
`4d0c20ba36add1d5bb3407852480ad83143084bbf8c4ed42e8a36d5ad9feab7c`,
152,654,248 bytes, same command, **rc=0, zero `[parser_error]` lines**:

```
[cranelift-direct] compile main
[cranelift-direct] compile probe
[build] smf_package unknown/unknown step 1/1 +1234ms dt=33ms scratch_boot/repro/repro.smf
```

And on the file that actually blocked Stage 3 —
`compile --format=smf src/compiler/80.driver/driver_source_pipeline_parsing.spl`,
which pulls the whole compiler closure: **zero `[parser_error]` lines** across
the entire closure. The parse blocker is gone.

That invocation then ended at

```
error: in-process SMF compile: HIR lowering error in
src/compiler/frontend/core/lexer.spl: invalid export origin `compiler...`
```

— **stated for completeness, and explicitly NOT claimed as the next Stage-3
blocker.** It is an isolated single-file `compile` of one compiler module, not a
Stage-3 whole-tree build, and single-file compiles of compiler modules do not
resolve export origins the way a whole-tree build does. The bootstrap's real
next blocker is the Stage-2 sanity failure below.

## Next blocker after this one (Stage 2 sanity, NOT parse, NOT SDL2)

The stage-2-only bootstrap built Stage 2 successfully and then failed its
**Stage-2 bootstrap-compiler sanity** gate, so the binary was preserved as
`stage2/<triple>/simple.rejected`:

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
  ERROR: scripts.check.cert.redeploy_gate.fixtures.hello_world
      reason: native-capsule-source-mutated:scripts.check.cert.redeploy_gate.fixtures.hello_world
error: Stage 2 bootstrap compiler sanity failed
```

The smoke's own trace shows `parse`, `hir`, `monomorphize`, `mir`, `aop_weave`
and `native_cache` all **complete**; the failure is the native-capsule
source-mutation check at `native_compile`. That is a different defect from both
this record and the SDL2 one and is not investigated here.

One observation, not a diagnosis. The emitter is
`driver_native_collect_capsule_result_v1`
(`src/compiler/80.driver/driver_aot_native_output.spl:455-462`) and it has TWO
triggers: the on-disk source identity differing from the one recorded at parse,
**or `capsule.source_identity` being empty**. The fixture here
(`scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`) is a tracked file
in an isolated worktree that nothing mutated during the run, which points at the
empty-identity branch rather than a real mutation — but that was not confirmed,
and the run used a non-default `--output=build/bootstrap-arrow` with
`SIMPLE_CACHE_SCOPE=arrow-arm-lane`, so a lane-isolation artifact is not ruled
out either. Whoever picks this up should start by instrumenting which of the two
branches fires.

Note the wrapper's final line is `UNDIAGNOSABLE: the stage failed with no error
message of any kind.` — it is wrong, and it points at the wrong log. The real
error is in `stage3/<triple>/stage2-sanity.env.frontend-failure.log`, not
`logs/<triple>/stage2-native-build.log`.

## Pre-existing reds stepped over when landing (recorded per .claude/rules/vcs.md)

Range `0dc18e8edfc..ec029f32a08`, measured 2026-09-06:

- `check-tree-size-push` — `PASS — 1 commit(s) checked ... 0 structural faults`
- `check-no-conflict-markers-push` — `PASS — 5 file(s) scanned ... 0 conflict markers`
- `check-no-conflict-tree-push` — `PASS — 1 commit(s), 1 unique tree(s) checked ... 0 conflict trees`
- `check-runtime-api-regression-push` — `PASS — 2994 symbol(s) checked, 0 removed`
- `check-rt-dual-implementation-ratchet` (clean detached checkout of the sha) —
  `PASS — 2491 symbol(s) checked against 2491 baselined, 0 new, 0 stale`
- `check-test-tree-divergence-delta 0dc18e8edfc ec029f32a08` —
  `PASS — 3197 pre-existing offender(s), 0 introduced by this range`. The
  pre-existing offender list is saved at
  `/tmp/test_tree_divergence_preexisting.txt`; the base verdict is
  `FAIL — 3931 diverged vs 965 baselined (3069 new, 103 fixed-but-still-baselined);
  26 mirror-only (25 unallowlisted, 0 stale-allowlist)`. **This range introduces
  none of it** — it adds one new spec under `test/01_unit/` only.
- `check-no-direct-rt` (clean detached checkout) — **RED, and byte-identically
  red at the BASE**: `FAIL — forbidden direct rt_* count 27313 exceeds baseline
  7776 (roots=src,examples,tools,scripts,test, src=6072 examples=1344 tools=14
  scripts=308 test=19575), extern_decls=13220`, same top offenders at both ends.
  This range adds **zero** `rt_*` call sites (`git show <sha> -- src/ | grep -c
  'rt_[a-z_]*('` returns 0).

## Still open, deliberately NOT addressed here

`| pattern -> body` (PIPE-prefixed, inline, followed by another arm) remains
broken on BOTH compilers — that is
`doc/08_tracking/bug/inline_arrow_match_arm_fails_when_followed_by_another_arm_2026-09-05.md`
and it is a different defect (the `|` is absorbed as a binary-or operator). The
quick reference's "preferred" recommendation still points at that broken
spelling. This record covers only the CASELESS arrow arm.

`case pattern -> body` (the `case` keyword with an arrow separator) is also not
accepted; the seed was not verified to accept it either, so it was left alone.
