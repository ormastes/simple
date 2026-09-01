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
