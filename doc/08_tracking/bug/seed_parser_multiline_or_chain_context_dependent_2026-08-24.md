# Seed parse error on a bodyless multi-line `or` chain blocks the whole SimpleOS build (2026-08-24)

- Status: OPEN (P2) — worked around at the call site, root cause NOT fixed
- Measured in `/mnt/data/worktrees/goal-lane-d-simpleos-fs`
- Blocks: `bin/simple os build --arch=<any>`, therefore every SimpleOS QEMU
  filesystem gate that needs `build/os/simpleos_<arch>.elf`

## Symptom

```
$ bin/simple os build --arch=x86_64
error: compile failed: parse: in ".../src/os/_QemuRunner/scenario_exec.spl": Unexpected token: expected Colon, found Dot
```
rc=1. No artifact is produced. **The diagnostic carries no line or column** —
that is a second, independent defect: every other diagnostic in the same run
prints a `-->` source span, this one does not.

## Isolation

Bisected at top-level `fn` boundaries over the 1007-line file (60 functions).
The prefix ending at line 416 parses; the prefix ending at line 422 does not.
The only lines added are `_is_compiler_filesystem_scenario`, whose body is a
bodyless-expression multi-line `or` chain:

```
fn _is_compiler_filesystem_scenario(scenario: QemuScenario) -> bool:
    scenario.name == "x86_64-compiler-filesystem" or
        scenario.name == "arm64-compiler-filesystem" or
        scenario.name == "riscv64-compiler-filesystem"
```

Introduced by `89a2a27b558` ("feat(simpleos): reserve fail-closed compiler QEMU routes").

**The shape alone is NOT the bug.** Four standalone fixtures with exactly this
shape all parse cleanly (rc=0), including the 3-term version and the
field-access version:

| fixture | shape | rc |
|---|---|---|
| r1 | 2-term `or`, `s.name` field access | 0 |
| r2 | same, parenthesised | 0 |
| r3 | 2-term `or`, plain identifier | 0 |
| r4 | 3-term `or`, `s.name` field access | 0 |

So the parser enters a bad state somewhere in the preceding 416 lines and only
faults when it then meets this construct. The poisoning construct has not been
located; that is the open work.

## Workaround applied

The chain was parenthesised in place (a semantic no-op) with a comment pointing
here. After that edit the file's parse error is gone and `os build` advances to
a later, unrelated phase. **This is a workaround, not a fix** — the parser still
mis-parses the bare form in this context, and the next file to use it will fail
the same way.

## Fix order

1. Find which preceding construct poisons the parser state (the file is the
   reproducer; bisect within lines 1-416 by construct, not by truncation —
   truncation mid-expression produces confounding errors).
2. Give the parse error a source span. A parse diagnostic with no location cost
   an entire bisect to recover information the parser already had.
3. Remove the parenthesis workaround once 1 lands.
