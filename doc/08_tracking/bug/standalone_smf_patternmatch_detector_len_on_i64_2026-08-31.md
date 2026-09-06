# Standalone native-build of a match-bearing file crashes the unsupported-construct scan with `len` on i64

- Date: 2026-08-31
- Severity: medium (masks the real "PatternMatch requires interpreter" report)
- Status: OPEN

## Symptom

`bin/simple native-build vis2.spl -o vis2.bin` (standalone, no closure) on a
25-line file containing `match` over a 3-variant enum fails with:

```
error: semantic: method `len` not found on type `i64` (receiver value: 3)
```

The receiver value tracks the enum's VARIANT COUNT (3 for 3 variants, 6 for
6), i.e. somewhere in the pure-Simple semantic scan a variant count (i64) is
used where a variant list is expected. The correct behavior is what the seed's
`compile --format=smf` path prints for the same file:

```
error: ... cannot compile to standalone SMF: 1 function(s) contain constructs that require the interpreter:
  - tag_of: [PatternMatch]
```

So the limitation itself is by design; the defect is the detector crashing
with a nonsense dispatch error instead of the typed report. Reproduces
identically on a clean worktree of committed HEAD (3c714ddb55f), interpreted
`bin/simple run` of the same file is fine.

## Repro

`/mnt/data/tmp/claude-1000/.../scratchpad/repro/vis2.spl` (3-variant enum,
match with unqualified arms + `case _`, main printing the result); run
`bin/simple native-build vis2.spl -o vis2.bin` from repo root.

## Note

This is NOT the stage2 `hir codec: no Visibility arm for tag -1` bug — that
one is tracked separately; this detector crash merely blocked the standalone
reduction path while investigating it.
