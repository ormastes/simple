# Absolute paths are mishandled in opposite directions by `native-build --entry` and `simple test` -- 2026-08-09

## Status: PARTIALLY FIXED (Half 1 implemented 2026-08-16; admitted Stage 2/4 verification pending). Half 2 remains OPEN / fail-open.

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
exist, but the retained Phase-2 evidence identified a narrower cause: the
single-file collector applied recursive/bulk exclusions to the full spelling.
`test/foo.spl` does not contain `/test/`, while
`/workspace/test/foo.spl` does, so only the absolute spelling was discarded.

**Workaround:** pass `--entry` as a path relative to the invocation root.

### 2026-08-16 containment

`_driver_collect_sources` now exempts only the direct `.spl` source whose
physical identity exactly matches `SIMPLE_NATIVE_BUILD_ENTRY`. Directory-walk
prefilters and unrelated explicit paths retain the existing exclusions. A
focused unit regression uses the retained failing fixture
`test/fixtures/compiler/type_multiline_signature_valid.spl`, proves its
absolute spelling remains filtered with both an empty and a nonmatching entry,
and proves only the exact requested absolute spelling is collected.

Latest retained failure evidence:

- compiler authority: admitted pure-Simple Phase 2,
  SHA-256 `530779a2240d35bfe7ce8834dfdb203b0f30651113a5708f91f853c3a94d654c`;
- rejected existing entry:
  `/mnt/data/worktrees/stage4-debug-frozen/test/fixtures/compiler/type_multiline_signature_valid.spl`;
- log:
  `build/native_probe/phase2-compiler-tools-matrix-20260816/compiler-smf-probe.log`.

This is implementation evidence only until a newly produced pure-Simple
compiler passes the focused native-build probe. Rust-seed/interpreter unit
evidence is diagnostic and cannot admit Stage 4.

Diagnostic verification on 2026-08-16:

- the exact admitted Stage-2 bootstrap capsule could not run the spec because
  that capsule intentionally exposes no `test` command (`unknown command`), so
  this was an infrastructure result and measured no criterion;
- installed pure-Simple CLI SHA-256
  `877dace60ce8eb11b656670b701019af5b4a0fb51b861832492bb5779237118b`
  ran the focused interpreter spec: 6 declared, 6 executed, 6 passed;
- evidence:
  `build/native_probe/phase2-absolute-entry-fix-20260816/focused-spec-bin-simple.log`.

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
