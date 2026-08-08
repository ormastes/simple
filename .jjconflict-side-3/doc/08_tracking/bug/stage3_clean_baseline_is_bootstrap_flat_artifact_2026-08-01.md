# Stage3 "728/0/0, 0 unresolved" is a bootstrap-flat artifact, not a clean tree

- **Date:** 2026-08-01
- **Status:** OPEN — measurement-validity defect. No product code is wrong; the
  *evidence* circulating between lanes is.
- **Severity:** HIGH. Three lanes (HirType layer, residual unresolved names,
  duplicate type aliases) were told their targets may be closed on the strength
  of this number.
- **Area:** `src/compiler/80.driver/` bootstrap pipeline gating
- **Tip measured:** `f793418c80240580c0abab03f67c51bb118ab33c` (tree 109,555 files)

## Claim being retired

> "stage3 at this tip is clean: 728 compiled, 0 cached, 0 failed, zero
> `unresolved` in the log — so the tree has no unresolved names."

The first half is a true observation. **The inference is invalid.** A stage3
build does not run the analysis that produces `unresolved type` / `unresolved
name`, so its silence is not evidence about the tree.

## Mechanism (PROVED — read at the measured tip)

Every stage3 build runs with `SIMPLE_BOOTSTRAP=1` and `SIMPLE_BOOTSTRAP_STAGE4`
**unset**. That exact conjunction — `BOOTSTRAP == "1" and STAGE4 != "1"` — gates
a distinct, much weaker "bootstrap-flat" pipeline at four sites:

| File | Line | Effect when the stage3 condition holds |
|---|---|---|
| `driver_source_pipeline_parsing.spl` | 198 | `parse_full_frontend` runs for the **bootstrap entry source only**; other sources take the lighter path |
| `driver_pipeline_lowering.spl` | 171 | MIR lowering runs for **`app.cli.bootstrap_main` only**, then `return self.ctx.errors.len() == 0` — the other 727 modules are never MIR-lowered |
| `driver_aot_pipeline.spl` | 35 | `bootstrap_lower_to_mir_context(...)` replaces `self.lower_to_mir()` |
| `driver_aot_pipeline.spl` | 53 | `bootstrap_flat_aot` ⇒ `log_phase("aot:flat_mir_passes:skipped")` — **borrow-check and the flat MIR passes are skipped entirely** |

So "0 failed" means "the passes that fail were not run", not "the passes passed".

## The flag cannot be used to check this (PROVED — two real runs)

The standing repo finding "stage4 HIR errors are invisible without
`SIMPLE_BOOTSTRAP_STAGE4=1`" invites the obvious control: re-run stage3 with the
flag on. **That control is impossible.** `SIMPLE_BOOTSTRAP_STAGE4=1` is not a
verbosity toggle; it selects a different build product, and it hard-errors on a
stage3 invocation:

- with the stage3 entry `--entry src/app/cli/bootstrap_main.spl`:
  `Error: Stage4 entry must be src/app/cli/main.spl or src/app/os/main.spl` (exit 1)
- with `--mode dynload`:
  `Error: Stage4 compiler capsule requires --mode one-binary` (exit 1)

There is therefore **no flag-on/flag-off comparison for stage3**. The only way
to see the hidden diagnostics is to run the stage4 product itself
(`--entry src/app/cli/main.spl --mode one-binary`), which is a different and
far more expensive build.

## Why no wrapper accidentally set it (PROVED)

`build/glob-memo-lane-artifacts/stage_run.shs` — the wrapper that produced every
number in this round — contains **zero** occurrences of
`SIMPLE_BOOTSTRAP_STAGE4`, and invokes the compiler under `env -i`, so the
variable cannot be inherited from the parent shell either. Every measurement was
taken on the bootstrap-flat path. This is not an oversight in one script; it is
what a stage3 build *is*.

## What is still true

The stage3 comparison remains valid **as a differential**: pristine and patched
arms ran the identical pipeline with the identical gating, so a delta between
them would still have been meaningful. Both returned 728/0/0 with empty
unresolved sets, so the glob-memo change introduced no *new* stage3 failure.
That conclusion survives. What does not survive is reading the same number as a
statement about the tree.

## Required follow-up

1. Stop quoting stage3 `0 unresolved` as tree evidence. The three dependent
   lanes must not close targets on it.
2. Any "is the tree clean" question must be answered by a stage4 build
   (`--entry src/app/cli/main.spl --mode one-binary`, `SIMPLE_BOOTSTRAP_STAGE4=1`).
3. Consider making the asymmetry loud: have the bootstrap-flat path emit a
   one-line banner (e.g. `aot:flat_mir_passes:skipped` is already logged, but at
   a level the runs above did not surface) so a reader of a stage3 log cannot
   mistake it for a full analysis.

## Reproduction

```sh
# stage3 (bootstrap-flat, silent): 728/0/0, zero unresolved
sh build/glob-memo-lane-artifacts/stage_run.shs \
   s3 <src_tree> <stage2_binary> <outdir> 8 0

# attempting the control — both fail, this is the point
SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1 <stage2> native-build \
  ... --mode dynload --entry src/app/cli/bootstrap_main.spl
# Error: Stage4 entry must be src/app/cli/main.spl or src/app/os/main.spl
# Error: Stage4 compiler capsule requires --mode one-binary
```
