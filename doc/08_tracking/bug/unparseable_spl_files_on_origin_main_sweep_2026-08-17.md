# Exhaustive parse sweep of `origin/main` — 12,074 `.spl` files, 86 unparseable

- **Date:** 2026-08-17
- **Revision swept:** `origin/main` = `eb4d4d9cd2518d08dd5d91cfbef26daf11cb4309`
- **Status:** **Tier 1 and Tier 2 are GREEN as of 2026-08-17** (0 unparseable of 9,478 probed). Tier 3 (`src/app`, does not block a push) still has 24. See "Resolution 2026-08-17".
- **Headline:** most of them are **not bad source**. A parser built from `origin/main` **rejects 32 files
  that the currently deployed `bin/simple` accepts.** `origin/main` carries a Rust parser regression.

## UPDATE 2026-08-17 — the regression half is FIXED and now ABLATED

The 32-file regression is the relative-import defect and nothing else. Root cause confirmed by
reading the diffs, not inferred:

- **Introduced by `3c4e6551b7a`** ("11 soft keywords could not be used as identifiers"), which added
  `TokenKind::Use` to the `soft_kw_stmt_as_ident` `.`-peek predicate in
  `parser/src/parser_impl/core.rs`. `use .mod.X` *is* the relative-import statement form, so `Use`
  followed by `Dot` was rerouted to an expression. That commit's own message admits `--bin simple`
  was never built.
- **Fixed by `579a0e1a171`**, which excludes `use` from the `.`-peek half only.

**Why the sweep still saw it:** `3c4e6551b7a` IS an ancestor of the swept revision
`eb4d4d9cd25`; `579a0e1a171` and `c3506bfbc4b` are **not**. The fix was committed locally and had
not reached `origin/main` when the sweep ran. Verified with `git merge-base --is-ancestor`. So the
sweep is accurate for the revision it names — no re-derivation needed.

`579a0e1a171` landed labelled *"the RED is proven on a full binary, the GREEN is not"*. That gap is
now closed at the parser-crate level. Ablation, both arms verbatim, on a real corpus harvested from
the tree rather than hand-written fixtures (`parser/tests/relative_import_brace_glob_corpus.rs`):

| arm | `relative_import_brace_glob_corpus` | `relative_import_not_soft_keyword_ident` |
|---|---|---|
| fix APPLIED (HEAD) | `test result: ok. 2 passed; 0 failed` | `test result: ok. 7 passed; 0 failed` |
| fix REVERTED (control) | `test result: FAILED. 1 passed; 1 failed` — **`106 of 130 real relative brace/glob imports failed to parse`** | `test result: FAILED. 4 passed; 3 failed` |

The control fails, so the test discriminates. Reverted-arm messages are the census's exact two:
`expected identifier, found LBrace` and `found Star`.

**A finding about the pre-existing fixture test:** under the reverted fix,
`double_dot_relative_import_with_glob_parses` still PASSES. The hand-written fixture set is weaker
than the defect — 3 of its 7 cases discriminate. This is the same failure mode the Calibration
section below records for the or-pattern repro, and is why the new test harvests real lines and
asserts a non-vacuity floor instead.

**Not fixed by this, and not the same defect** — these remain open and are NOT parser regressions:
the 7 genuine `src/lib` source defects, the 9 de-symlinked files committed as regular blobs (the 12
`Slash` failures), and the continuation-line-indentation family. They need separate work.

## Method

The probe is `simple compile <file> --emit-ast=/dev/null -o <tmp>`, not `simple run`:

- it fails in ~0.3 s at the parse stage and never executes the file (`run` on
  `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` did not return in 120 s);
- a failure is recorded **only** when the emitted `parse: in "<path>"` names the probed file
  itself — the driver also reports parse errors for dependency files, which is how
  earlier one-at-a-time triage produced wrong attributions;
- the exit status is read directly into a variable, never through a pipe;
- `rc=143/144/137` is recorded as `UNVERIFIED` and re-run (earlyoom SIGTERMs `simple` on this box);
- `rc=124` (timeout at 15 s) is recorded as `TIMEOUT_PARSED`: parse errors are emitted well under
  one second, so a run that survived to codegen had already parsed. It is not counted as a failure.

**The binary matters more than anything else here.** The deployed `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, dated 2026-08-10) is not built from `origin/main`.
The sweep therefore used a Rust seed compiled **from the extracted `origin/main` tree itself**
(`git archive origin/main`, `cargo build --release --bin simple`,
`CARGO_TARGET_DIR=/mnt/data/cargo-target-sweep`), *not* from the working copy — the working copy has
7 uncommitted modified files under `src/compiler_rust/`, four of them in the parser
(`parser_impl/core.rs`, `stmt_parsing/control_flow.rs`, `expressions/postfix.rs`, plus new tests
`multiline_or_pattern.rs` and `relative_import_not_soft_keyword_ident.rs`). Building from it would
have measured a parser that exists in no commit. `d7213eb6174` (the landed parser fix) was confirmed
an ancestor of `origin/main` before starting.

### Calibration (both required, both passed)

| control | expectation | result |
|---|---|---|
| `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` @ origin/main | must PARSE | PARSED — it was never broken |
| pre-fix `verification_semantic_coverage.spl` (`eb4d4d9cd25^`), real wrapped or-pattern | must FAIL | FAIL — `expected pattern, found Indent` |

A *synthetic* wrapped or-pattern (`case 1 |` / newline / `2:`) **parses fine**, so the or-pattern gap
is narrower than "any wrapped `|`". Use the real pre-fix file as the control, never a hand-written one.

## Coverage

| tier | scope | swept | unparseable |
|---|---|---|---|
| 1 | `src/compiler/**/*.spl` | **1686 of 1686** | **23** |
| 2 | `src/lib/**/*.spl` | **7749 of 7749** | **8** |
| 3 | `src/app/**/*.spl` | **2639 of 2639** | **55** |
| — | **total** | **12,074** | **86** |

Not swept: `test/**` (a broken test file does not block a push), `src/os`, `src/unit`,
`src/compiler_rust/lib/std`, `src/i18n`, `src/runtime`, `src/type`, `src/verification`
(2,701 further `.spl` files). Vendored trees excluded per CLAUDE.md Owned-Code Scope.

## The regression is the main finding

32 files parse on the deployed 2026-08-10 `bin/simple` and **fail** on a seed built from `origin/main`;
1 file (`expr_dispatch.spl`) goes the other way. Minimal repros, verified on both binaries:

| fixture | deployed `bin/simple` | seed built from `origin/main` |
|---|---|---|
| `use .foo.{A, B}` | PARSED | **FAIL** — `expected identifier, found LBrace` |
| `use .foo.*` | PARSED | **FAIL** — `expected identifier, found Star` |
| wrapped `if` condition then dedented call args (below) | PARSED | **FAIL** — `expected expression, found Dedent` |
| `use foo.bar.{A, B}` (absolute) | PARSED | PARSED |

Relative-prefix imports (`.`, `..`, `...`) lost brace-group and glob support; the absolute form still
works. That single defect accounts for 16 of the 23 Tier 1 failures and 21 of the 55 Tier 3 failures.
The uncommitted `relative_import_not_soft_keyword_ident.rs` in the working copy suggests another lane
is already on exactly this — **confirm before anyone starts a second fix.**

The dedent shape, minimised from `src/compiler/00.common/assurance/formal_delivery_gates.spl:42-45`:

```
fn f(a: int, b: int) -> int: a
fn g(x: bool, y: text) -> int:
    if not x or
            y == "": return f(
        1, 2)
    0
```

The call's argument lines are indented *less* than the wrapped condition line. Same family as the two
defects fixed earlier today: **continuation-line indentation**, not any one keyword.

## Tier 1 — 23 files (blocks every push)

Relative-import brace/glob — `expected identifier, found LBrace` / `found Star` (**regression**, 16):

`70.backend/backend/vhdl_backend.spl`, `vhdl_codegen_helpers.spl`, `vhdl_entity_compile.spl`,
`vhdl_expr.spl`, `vhdl_validation.spl`, `vhdl/vhdl_design_catalog.spl`, `vhdl/vhdl_memory_templates.spl`,
`vhdl/vhdl_register_file.spl`, `vhdl/vhdl_rv32i_decode.spl`;
`99.loader/loader/generation_sweeper.spl`, `jit_context.spl` (Star), `jit_instantiator.spl`,
`module_loader.spl`, `module_loader_lib_support.spl` (Star), `object_mapper.spl`,
`resource_lifecycle.spl`, `smf_cache.spl`, `smf_cache_manager.spl`.

Offending line, e.g. `99.loader/loader/smf_cache.spl:21`:
`use .smf_mmap_native.{native_mmap_file, native_munmap, native_mmap_read_bytes, ...}`

Continuation-line indentation — `expected expression, found Dedent` (5):

- `00.common/assurance/formal_delivery_gates.spl` (**regression**) — `evaluate_formal_delivery_gates_v1`
  and `_v2`, the wrapped-`if`-then-dedented-args shape quoted above
- `00.common/mission_critical/__init__.spl` — wrapped `export A, B,` / newline / `C from mod`
  (minimal repro fails on **both** binaries: a long-standing gap, not the new regression)
- `50.mir/hwir/riscv_scalar_fence_owner.spl` — `fence_ports`, `fence_outputs`
- `90.tools/verify/replay_runner.spl` — `replay_executable_identity_hash_v1`

Other (2):

- `50.mir/hwir/riscv_scalar_csr_owner.spl` — `expected Indent, found FString([Literal("completion_")])`
  in `csr_owner_ports`, plus a second Dedent failure in `csr_owner_outputs`

## Tier 2 — 8 files in `src/lib`

7 fail on **both** binaries (genuine source defects, not the regression):

| file | message |
|---|---|
| `common/crypto/x25519_mlkem768/matrix_receipt.spl` | `expected expression, found Else` |
| `hardware/rv64gc_rtl/imac_protected_core.spl` | `expected expression, found Else` |
| `nogc_async_mut/wm/wm_optimization.spl` | `expected expression, found Plus` |
| `nogc_sync_mut/web_framework/persistence.spl` | refutable pattern in `val` binding needs a diverging `else:` |
| `nogc_sync_mut/web_framework/session_redis.spl` | same |
| `scv/integrity.spl` | same |
| `scv/integrity_object.spl` | same |

1 is a regression: `gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl`
— a numeric literal in generic argument position, newly rejected.

`src/lib` is read as SOURCE on every run, so these have the same blast radius as Tier 1.

## Tier 3 — 55 files in `src/app` (does not block a push)

21 relative-import brace (regression, mostly `src/app/mcp/**` and `src/app/simple_lsp_mcp/**`);
12 `expected expression, found Slash`; the rest are scattered one-offs — reserved keywords used as
parameter names (`actor`, `val`, `exists`), `expected Import, found LBrace`, `expected LParen, found Lt`.

**The 12 `Slash` failures are a separate defect entirely: 9 files are symlinks committed as regular
files.** `src/app/leak_finder/*.spl` (8) and `src/app/lint/main.spl` are mode `100644` blobs whose
entire content is a relative path, e.g. `../../compiler/90.tools/leak_finder/config.spl` — the parser
sees a division operator. A repo-wide census found exactly these 9 and no others.

## What to do

1. **Fix the parser regression first**, not the 37 call sites. Check with the lane holding the
   uncommitted `src/compiler_rust/parser/` edits before starting.
2. **Redeploy `bin/simple`.** It is a week stale and disagrees with `origin/main` on 33 files;
   that disagreement has already produced several wrong root causes today.
3. The 7 genuine `src/lib` defects and the 9 de-symlinked files are independent and can be fixed now.

Raw per-file results, fixtures and the stale-vs-fresh comparison live in this session's scratchpad
(`t1.tsv`, `t2.tsv`, `t3.tsv`, `cmp1.tsv`, `cmp3.tsv`, `fix/`); they are not committed.

## Resolution 2026-08-17 — Tier 1 and Tier 2 are at ZERO

Re-swept the whole of `src/compiler` + `src/lib` + `src/app` (12,115 files,
`xargs -P 12`) with the same probe and the same non-vacuity rules as the
original sweep, on the redeployed seed `bin/release/x86_64-unknown-linux-gnu/simple`
(59537240 bytes, 2026-08-17 12:58:51).

| tier | swept | unparseable BEFORE (origin/main, this doc) | AFTER first re-sweep | AFTER fixes |
|---|---|---|---|---|
| 1 `src/compiler` | 1686 | 23 | 5 | **0** |
| 2 `src/lib` | 7749 | 8 | 4 | **0** |
| 3 `src/app` | 2639 | 55 | 24 | 24 (not addressed) |

The 32-file relative-import regression is gone on the redeployed binary, exactly
as the "UPDATE" section predicted — it was fixed in the parser and had simply not
reached the swept revision. The 9 de-symlinked `src/app/leak_finder/*` +
`src/app/lint/main.spl` blobs are also gone: all 9 now carry real source, not a
relative path.

### What was actually fixed here — 9 genuine source defects

All nine were located from a **single** compile each, using the caret added by
`compile_parse_diagnostics_carry_no_line_column_2026-08-17.md` (fixed in the same
session). The doc's own estimate for the old message was ~600 invocations per
file of prefix bisection.

**Tier 2 (`src/lib`, 4 files)** — the doc listed 7 here, of which 3
(`web_framework/persistence.spl`, `web_framework/session_redis.spl`,
`scv/integrity.spl`, `scv/integrity_object.spl` — the refutable-`val` family)
had already been fixed by another lane and now parse:

| file | site | shape | fix |
|---|---|---|---|
| `common/crypto/x25519_mlkem768/matrix_receipt.spl` | 698:20 | `if c: "" elif c2:` / newline / `x else: y` — inline `else` trailing a block-`if` expression | expanded to a block `if`/`elif`/`else` |
| `hardware/rv64gc_rtl/imac_protected_core.spl` | 530:33 | same | same |
| `nogc_async_mut/wm/wm_optimization.spl` | 57:5 (+ 2 more sites, 12 lines total) | same-indent **leading**-`+` continuation | moved the operator to the end of the previous line |
| `gc_async_mut/gpu/browser_engine/…_renderer_foundation.spl` | 500:17 | `offset < 0 or …` parsed as a generic-argument list | parenthesised the comparison |

**Tier 1 (`src/compiler`, 5 files)** — every one was the *same* family the doc
identified, "continuation-line indentation, not any one keyword": a wrapped
boolean condition whose continuation is indented MORE than the statement that
follows it.

| file | sites | fix |
|---|---|---|
| `00.common/assurance/formal_delivery_gates.spl` | 3 (`_v1` and `_v2`) | hoisted each wrapped condition into a `val`, then `if <val>:` |
| `90.tools/verify/replay_runner.spl` | 1 | same |
| `50.mir/hwir/riscv_scalar_csr_owner.spl` | 2 | same, plus expanding the inline `if/else` |
| `50.mir/hwir/riscv_scalar_fence_owner.spl` | 2 | same |
| `00.common/mission_critical/__init__.spl` | 1 | wrapped `export A, B,` / newline / `C from mod` joined onto one line |

Note the multiplicity: each of those files carried the shape **more than once**,
so the first fix only moved the reported line. The caret is what made iterating
cheap.

These are **source normalisations around known parser gaps**, not parser fixes.
The gaps themselves stay filed —
`parser_same_indent_leading_operator_continuation_2026-08-17.md`,
`parser_block_if_expr_trailing_inline_else_2026-08-17.md`,
`const_generic_argument_rejected_in_constructor_call_2026-08-17.md` — per
CLAUDE.md's rule against silently normalising a workaround.

### Verification (non-vacuity stated)

```
$ xargs -a t12.txt -P 12 -n 1 sh probe.sh > sweep12.tsv     # t12.txt = src/compiler + src/lib
probed=9478 parsefail=0 rc124=212
```

`rc124` is the 15s `TIMEOUT_PARSED` class the doc defines (parse errors emit in
well under a second, so a run that survived to codegen had already parsed); it is
not a failure. **The control that makes this non-vacuous:** the identical probe
over the identical file list an hour earlier returned **9** Tier-1/Tier-2
PARSEFAILs (33 across all three tiers). The probe finds failures when they exist.

### Not addressed — Tier 3 (`src/app`, 24 files)

Does not block a push, per this doc's own tiering. The current list is dominated
by reserved keywords used as parameter names (`actor`, `val`, `exists`), four
`expected Import, found LBrace` under `src/app/interpreter/expr/`, two
`expected LParen, found Lt`, one unterminated f-string, and two
`vscode_extension/examples/phase1-*.spl` fixtures. Left for a follow-up.
