# `export use X.*` is rejected by the compiler but used 1,719 times in its own source (2026-08-17)

Status: OPEN
Priority: P1

## Symptom

A freshly built Rust seed at `origin/main` cannot `native-build` a two-line
hello-world. It fails on the repo's OWN source:

```
$ printf 'fun main()\n  print("hi42")\n' > /tmp/hw.spl
$ <fresh-seed> native-build /tmp/hw.spl -o /tmp/hw.bin
  --> src/app/io/env_ops.spl:3:1
   |
  3 | export use std.nogc_sync_mut.io.env_ops.*
   | ^
Use explicit exports instead
RC=1
```

Exit status read directly into a variable, not through a pipe.

## Scale

`export use <path>.*` occurs **1,719 times** in owned `src/**/*.spl`:

```
/usr/bin/grep -rn --include=*.spl -E '^\s*export use .*\.\*\s*$' src/ | wc -l
1719
```

Examples: `src/type/simple_lang/__init__.spl:1`, `src/lib/string_core.spl:3`,
`src/lib/gc_sync_mut/__init__.spl:5`, and the whole
`src/lib/gc_sync_mut/terminal/` tree.

The offending line is COMMITTED at `origin/main` — confirmed via
`git show origin/main:src/app/io/env_ops.spl`. This is not an uncommitted
working-copy problem.

## Why this matters

The compiler and the source it must compile disagree. The diagnostic rejects a
form the tree relies on pervasively, so the toolchain cannot build the project
it belongs to. This blocks:

- any `native-build` through the affected module graph,
- therefore verification of any self-hosted stage,
- therefore the bootstrap chain end to end.

## What is NOT yet established

- Whether the diagnostic is newly introduced or newly reachable.
- Whether it is intended as an ERROR at all. The wording ("Use explicit exports
  instead") reads like lint advice, yet it terminates the build with RC=1.
- Whether it is correctly scoped: it may be intended only for a narrower case
  and is over-firing on ordinary re-export barrels.

## Candidate fixes, in order of preference

1. If the diagnostic was never meant to be fatal, downgrade it to a warning.
   That restores the toolchain immediately and costs nothing semantically.
2. If wildcard re-export is genuinely being removed as a language feature, the
   removal is incomplete: it needs a migration of all 1,719 sites landed in the
   SAME change as the diagnostic. Shipping the rejection without the migration
   is what produced this state.

Do NOT "fix" this by editing `src/app/io/env_ops.spl:3` alone. That file is one
of 1,719 and the next module in the graph fails identically.

## Related

- `doc/08_tracking/bug/selfhost_load_sources_nil_receiver_tail_tuple_2026-08-17.md`
  — the nil-tail-tuple miscompilation found behind this class of blocker.
- `doc/08_tracking/bug/deployed_seed_predates_landed_parser_fixes_blocks_repo_2026-08-17.md`
  — why a stale deployed binary masks and shifts these failures; the observed
  blocker moved between seed builds today.
