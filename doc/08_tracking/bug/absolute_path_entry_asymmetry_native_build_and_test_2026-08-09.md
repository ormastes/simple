# Absolute paths are mishandled in opposite directions by `native-build --entry` and `simple test` -- 2026-08-09

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status: OPEN (usability / fail-open). READ-DERIVED filing -- neither half was re-executed for this doc.

Two CLI entry points disagree about absolute paths, and they fail in *opposite*
ways. Anyone who hits one will eventually hit the other, so both halves are
recorded together.

## Half 1 -- `native-build` rejects an absolute `--entry` path (loud, wrong)

```
bin/simple native-build --entry /abs/path/to/entry.spl ...
  -> "native entry source not found"
```

The file exists and is readable. The **same file passed as a path relative to
the repo root works.** Observed today; it cost a fence iteration before the
absolute path was recognised as the variable.

Failure mode: LOUD and misleading. The message asserts the source does not
exist, when the real condition is that the entry resolver does not accept an
already-absolute path (it appears to join the argument onto a base directory
unconditionally). The diagnostic names the wrong cause, which is what makes it
expensive.

**Workaround:** pass `--entry` as a path relative to the invocation root.

## Half 2 -- `simple test <ABSOLUTE path>` runs nothing and exits 0 (silent, worse)

The known mirror-image trap. Given an absolute path, `simple test` runs no
specs, prints **no** `SPEC FILE VERDICT ... executed=N` line, and exits 0.
A caller that trusts the exit code reads this as GREEN.

**Workaround:** pass spec paths relative to the repo root, and never accept
`EXIT=0` from `simple test` as a pass -- require the verdict line with a
non-zero `executed=` count.

## Why the pair matters

The two halves are the same underlying gap -- no shared, tested policy for
absolute vs. relative path arguments across CLI subcommands -- but they fail
open and closed respectively:

| | absolute path | exit code | detectable? |
|---|---|---|---|
| `native-build --entry` | refuses to build | non-zero | yes, but blames a missing file |
| `simple test` | runs nothing | **0** | no -- looks like a pass |

The `simple test` half is the dangerous one: it manufactures false GREENs.

## Fix recipe

1. Normalise entry/spec path arguments once, in shared CLI argument handling:
   if the argument is already absolute, use it as-is; otherwise resolve it
   against the invocation root. Do not join unconditionally.
2. `native-build`: when the resolved entry does not exist, report the path that
   was actually probed, so the message cannot blame the user's path when the
   resolver rewrote it.
3. `simple test`: a spec-path argument that matches **zero** spec files must be
   a non-zero-exit ERROR, never a silent exit 0. A run that executed nothing is
   not a pass.

## Verification

- `native-build --entry` with an absolute path must produce the same artifact as
  the relative form (compare output binaries).
- `simple test <abs path>` must emit `SPEC FILE VERDICT ... executed=N` with the
  same `N` as the relative form; and `simple test <path matching nothing>` must
  exit non-zero.
- Both checks belong in the CLI-behaviour spec corpus so the asymmetry cannot
  silently return.
