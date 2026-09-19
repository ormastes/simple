# Two more whole-file `simple lint` aborts, distinct from the string-index one

**Status:** OPEN 2026-09-19
**Area:** semantic phase / lint file admission
**Severity:** each blocks EVERY lint rule on the affected file
**Sibling:** `lint_semantic_string_index_out_of_bounds_aborts_whole_file_2026-09-19.md`

Found in the same 52-file measurement. Both produce no findings at all for the
file, so like the string-index defect they silently skip every rule, not one.

## 1. `cannot iterate over this type: Nil`

```
$ bin/simple lint src/compiler_rust/lib/std/src/lms/workspace.spl
error: semantic: cannot iterate over this type: Nil
```

1 of 52 files. The semantic phase resolves the iterable of some `for` to
`Nil` and stops. Not reduced; the file above reproduces it.

## 2. `NOT LINTED: 1 file(s) were not analysed`

```
$ bin/simple lint src/compiler_rust/lib/std/src/tooling/compiler/pattern_matching.spl
NOT LINTED: 1 file(s) were not analysed
```
(exit 1, no `error:` line)

2 of 52 files — the other is
`test/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.spl`.

This one is arguably the worst of the three for a user, because it names no
cause. "Not analysed" is the correct thing to SAY — it is at least not a
false clean verdict, which is the trap the repo's guard conventions exist to
avoid — but it gives nothing to act on: not which phase refused, not why, not
which rules were skipped. A verdict that reports a non-vacuous refusal should
carry the reason with it.

## Together with the sibling record

Of the 52 files measured, 7 abort before any rule runs: 4 string-index, 1
iterate-over-Nil, 2 not-analysed. That is 13% of an arbitrary sample of repo
source on which `bin/simple lint` reports nothing, and it is the real ceiling
on lint coverage in this tree — larger than any individual rule's blind spot.
