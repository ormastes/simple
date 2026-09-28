# Release 1.0 C collection removal backport

Date: 2026-09-28
Base: `63b50fd00c61870a8892b883255e30d5b928939f` (`release/1.0`).
Source: original reviewed Windows proposal
`a4aa33c3492ce19e3b6a56766405fa7bc3a1a41b` (single-pass dictionary deletion).
PR #1991 dropped the overlapping C changes before merge; main's collection
dispatcher landed independently in `1d90954`. The array prerequisite was
compared against the main runtime implementation.

## Scope and behavior

Release 1.0 still traps on `rt_collection_remove` and lacks the prerequisite
`rt_array_remove` implementation. The backport adds the array primitive from
the main source tree and the erased array/dictionary dispatcher from the
original Windows proposal.
All changes are in the C runtime; the compiler receiver fix has a separate lane.
Independent review found that main's packed U64 removal shifts wide integers
directly and loses high bits. This backport uses the existing `rt_value_int`
helper to box values outside the immediate range. Main needs the same follow-up
fix separately; no main files were modified in this release worktree.

The array primitive takes a raw index, shifts the tail with `memmove`, shrinks
the length, and returns the removed tagged value. Object handles remain
unchanged. Byte and packed U64 scalars are tagged on return. Negative and
out-of-range indices return nil without mutation. The dispatcher decodes a
tagged integer index and rejects other index values. Dictionary removal returns
the removed value using one lookup/delete pass. The existing `rt_dict_remove`
ABI still returns an `int8_t` boolean; its declaration and the existing contains
declaration are exposed in the header for the regression fixture.

## Focused verification

`src/runtime/test/rt_collection_remove_selfcheck.c` passes **48 checks** under
both Ubuntu Clang 14.0.0 and GCC 11.4.0, using C99 mode on x86_64 WSL Ubuntu
22.04. The fixture covers object pointer preservation, byte and packed U64
middle removal and tail shifts, raw first/last removal, empty arrays, invalid
indices/receivers, integer/text dictionary keys, nil values, missing keys, and
legacy boolean removal. Packed fixtures cover `1 << 59`, `1 << 60`, `1 << 62`,
`INT64_MAX`, and `INT64_MIN`; wide results are compared after decoding.

From the repository root in a Linux shell, run each compiler once:

```sh
mkdir -p build/removal-backport
for cc in clang gcc; do
  "$cc" -std=c99 -O1 -ffunction-sections -fdata-sections \
    -DSIMPLE_CORE_C_STANDALONE=1 -Isrc/runtime -Isrc/runtime/platform \
    src/runtime/runtime_native.c src/runtime/test/rt_collection_remove_selfcheck.c \
    -Wl,--gc-sections -lm -o "build/removal-backport/remove-$cc-linux" &&
    "build/removal-backport/remove-$cc-linux" || exit 1
done
```

Both executables reported `PASS: 48 checks, 0 failures`. Clang reported existing
typedef/comment warnings; GCC reported an existing unchecked `write` warning.
`git diff --check` passed. Executable spec files under `doc/06_spec`: **0**.

Windows MSYS2 MinGW Clang could not start (exit `-1073741515`). Windows GCC
15.2 compiled the updated translation units, but its minimal two-file link
retained references to unrelated bridge providers such as `spl_file_read` and
`rt_process_spawn_async`; that executable was not produced. These attempts do
not establish Windows executable behavior.

This is focused C regression evidence. No bootstrap, Simple SPipe suite,
candidate admission, package promotion, tag, or release publication was run.
The draft backport must not be treated as release admission.
