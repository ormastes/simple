# `push-sffi-v2-authority` is RED on unmodified `origin/main` (2026-09-03)

Status: OPEN — pre-existing debt, measured, not introduced by any one branch

## Verdict

```
SFFI contract inventory: FAIL source_variants=416/399 migration=3378/3546
sffi-v2-authority: FAIL — 1 of 46 guard(s) failed
push-must-check: BLOCKING gate push-sffi-v2-authority failed (exit 1)
```

`source_signature_variants` counts symbols declared with MORE THAN ONE distinct
signature across the scanned source (`signatures[symbol] > 1`,
`scripts/audit/sffi-contract-inventory.shs:370`). The ceiling is a hardcoded
default of 399 (`:505`, overridable via `SFFI_MAX_SOURCE_SIGNATURE_VARIANTS`).
Measured: **416**, i.e. 17 over. The `migration` half is comfortably under
(3378 of 3546) and is not the problem.

Because `push-sffi-v2-authority` is a BLOCKING `push,`-tier row of
`config/check/must_check_gates.sdn`, this red blocks EVERY push that runs the
hook. It is one of the concrete reasons `.claude/rules/vcs.md` records that
"pushes are therefore routinely made with `--no-verify`, which nullifies every
guard below".

## It is pre-existing — measured on both sides, one identical binary

Both trees scanned with the SAME `SIMPLE_BIN`
(`bin/release/aarch64-apple-darwin-macho/simple`), same fixed audit scripts, so
only the source differs:

| tree | rc | source_signature_variants |
|---|---|---|
| `origin/main` (detached worktree, pristine) | 1 (FAIL) | **416** |
| `chore/repo-cleanup-2026-09-03` | 1 (FAIL) | **416** |

Corroborating, independent of the run: the cleanup branch adds and removes
**zero** `extern fn` lines (`git diff origin/main..HEAD -- 'src/**.spl'
'test/**.spl' | grep -E '^[+-]extern fn '` is empty), touches 6 `.spl` files none
of which declare externs, and its only deletions under `src/`/`test/` are 11
cargo build artefacts with no `.spl` among them. A purely source-derived metric
cannot move under those conditions.

## Why it surfaced today rather than earlier

On macOS this audit could not run at all until two defects fixed on
2026-09-03 (both in `chore/repo-cleanup-2026-09-03`):

1. `scripts/audit/io-sffi-authority.shs` — `ckeq` compares with `=` (string) and
   BSD `wc` right-aligns its count in an 8-column field, so the assertion failed
   as `expected 0, actual        0`.
2. `scripts/audit/sffi-contract-inventory.shs` — `bin/simple` on a macOS deploy
   is a shell WRAPPER, so `nm` yielded 0 symbols and the audit aborted with
   `nothing was checked ... (floor 100)`. Its only fallback path was a hardcoded
   `bin/release/x86_64-unknown-linux-gnu/simple`.

Before those, the gate FAILED for tooling reasons on this platform. It still
FAILS — now for a true reason. Nothing regressed; the measurement became
possible.

## What is NOT being done

The ceiling is deliberately **not** raised to 416 in tracked config. That would
be "relax it to make a run green", which the sibling guards explicitly forbid
(`check-tree-size-push.shs`: "Do not relax it to make a run green"). Shrinking
416 -> 399 means reconciling 17 symbols that carry divergent extern signatures,
which is real work with real risk and belongs to whoever owns those symbols.

The symbol-level evidence is reproducible in minutes:

```sh
SIMPLE_BIN=<real binary> sh scripts/audit/sffi-contract-inventory.shs out.tsv out.symbols.tsv
awk -F'\t' 'NR>1 && $10=="source_signature_variants"{print $1}' out.symbols.tsv | sort -u
```
