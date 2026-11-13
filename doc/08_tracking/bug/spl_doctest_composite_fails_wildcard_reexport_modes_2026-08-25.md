# SPL-doctest composite fails on a wildcard re-export that imports fine standalone

- **Filed:** 2026-08-25
- **Status:** OPEN
- **Severity:** blocks 13 doctest blocks across 4 files from ever going green,
  independent of the content of those blocks
- **Engine:** Rust seed rebuilt from this tree, **60634072 bytes, 2026-08-25
  05:17**. (The previously deployed seed, 60650360 bytes 2026-08-23, cannot run
  the doctest phase at all — see
  `deployed_seed_cannot_parse_value_bound_unsafe_2026-08-25.md`.)

## Symptom

Every doctest block in four files fails with a reason that is only a bare source
location, no message:

```
  FAIL  src/compiler/15.blocks/blocks/builder.spl (0 passed, 5 failed, 638ms)
        Line 21:  --> /mnt/data/worktrees/lane-doctest13/src/compiler/15.blocks/blocks/modes.spl:6:1
        Line 264: --> .../modes.spl:6:1
        Line 288: --> .../modes.spl:6:1
        Line 308: --> .../modes.spl:6:1
        Line 348: --> .../modes.spl:6:1
```

`src/compiler/15.blocks/blocks/modes.spl:6` is a wildcard re-export:

```
export use compiler.frontend.block_types.*
```

Affected: `blocks/builder.spl` (5 blocks), `blocks/mod.spl` (6),
`blocks/unified_registry.spl` (1), `blocks/easy.spl` (1).

## The discriminating measurement

Importing the same module **standalone succeeds**:

```
use compiler.blocks.modes.{LexerMode}
print "ok"
```

exits **0** on the same binary, in the same worktree. Parsing and module
resolution are not context-dependent here, so the failure exists only inside the
composite that `build_spl_doctest_code` assembles
(`src/lib/nogc_sync_mut/test_runner/doctest_runner.spl:440-441`):

```
source_content + "\n\n# --- doctest from line {n} ---\nuse std.spec.*\n" + dt.code
```

That is: the whole source file, then `use std.spec.*`, then the block. The
suspicion is an interaction between the file's own wildcard re-export chain and
the injected `use std.spec.*` — two wildcard imports in one unit — but that is
not yet proven and should not be recorded as fact.

## Why this matters beyond the affected blocks

It is **not** a defect in any documented example. `builder.spl:21` is a
pre-existing example that nobody edited, and it fails identically. Measured at
`HEAD~1` and `HEAD` with the same binary, `builder.spl` is `0 passed, 5 failed`
on both sides.

This misled an earlier triage
(`spl_doctest_parse_unexpected_token_class_2026-08-24.md`), which recorded that
`builder.spl:21` "chains identically and passes" and treated the resulting
apparent contradiction as evidence of a possible compiler bug in method sugar.
Line 21 does not pass; it fails for this reason. Any future triage that reads a
`--> modes.spl:6:1` reason as an example defect will make the same mistake.

## Secondary defect: the reason line loses the message

The failure is rendered as `--> <path>:<line>:<col>` with **no diagnostic text**.
That is the entire reason string the runner captured, which is why the shape of
this bug could not be identified from the suite output alone and needed a
hand-built probe. Reason extraction should keep the message, not just the span.

## Reproduce

```sh
cd <worktree>
./bin/simple test --spl-doctest src/compiler/15.blocks/blocks/builder.spl   # 0 passed, 5 failed
./bin/simple run /tmp/probe.spl    # `use compiler.blocks.modes.{LexerMode}` -> exit 0
```

## Related

- `deployed_seed_cannot_parse_value_bound_unsafe_2026-08-25.md` — must be
  resolved (or the seed rebuilt) before any of this is measurable.
- `spl_doctest_parse_unexpected_token_class_2026-08-24.md` — the 13 doc defects,
  now repaired; 10 of them still fail, most on THIS defect.


---

## Lane disposition 2026-11-13 (p3-misc-b)

OPEN; composite doctest mode fails on wildcard re-export while standalone import works - owner: spl-doctest/import-flattening lane (seed import/flattening divergence family).
## Addendum 2026-11-13 (lane lp5, work/live-p3-l5-20261113) — secondary defect FIXED; primary no longer reproduces at tip

Investigated on release/1.0.0 tip (tracked seed `bin/simple.exe`).

**Secondary defect (reason line loses the message) — FIXED in this lane's PR.**
`_dt_failure_reason` (`src/lib/nogc_sync_mut/test_runner/doctest_runner.spl`) returned the
FIRST non-warning stderr line, which in a child compile failure is the `-->` span
continuation of an earlier skipped warning — never the actual error. Reproduced with a
```spl doctest whose composite compile-fails: the suite reported
`--> ...\io_runtime.spl:349:41` instead of the error. Fixed with a three-pass extractor:
(1) first `error:` line on stderr; (2) the failing example's detail from the child's spec
stdout (`✗ <name>` + its indented `semantic: ...` line) — the seed prints example failure
detail on stdout, while stderr only carries the generic `spec failure: N of M` tail;
(3) last informative stderr line, skipping every warning class and its diagnostic
decoration (spans, gutters, carets) so the fallback is a message, not a bare span.
After the fix the same failing doctest reports
`✗ compile-errors: semantic: ...:25:9: variable 'undefined_name_here' not found`.
Pinned by `test/01_unit/app/test_runner/doctest_failure_reason_spec.spl` (4/4).

**Primary defect (composite fails on wildcard re-export) — does NOT reproduce at tip.**
`builder.spl`'s doctest blocks are now ` ```text ` fences (not ` ```spl `), so
`--spl-doctest` finds no SPL blocks in it ("no doctest blocks found"), and a hand-built
composite of `modes.spl` + the injected `use std.spec.*` + a spec block runs CLEAN
(`simple run` exit 0) on the current seed. The seed/import-flattening behaviour recorded
here appears already resolved; if a real `Local`-emitting writer re-enables the composite
failure shape, re-open with a fresh repro. The `parse_binding`/`exported_symbols` note in
this family is tracked separately under
`smf_reader_memory_binding_decode_changes_exported_set_2026-09-19.md`.
