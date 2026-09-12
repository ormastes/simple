# native_zero_work_admission_spec: six examples red on an unregistered `rt_file_write`

- Status: OPEN (2026-09-12)
- Area: test/03_system/compiler/feature, compiler extern registry
- Found by: BOOT-3 bootstrap lane, while adding an unrelated example to the same file

## Symptom

`test/03_system/compiler/feature/native_zero_work_admission_spec.spl` is red on
six of its nine examples, every one with the same diagnostic:

    semantic: unknown extern function: rt_file_write

Verdict line:

    9 examples, 6 failures
    SPEC FILE VERDICT: test/03_system/compiler/feature/native_zero_work_admission_spec.spl
      outcome=ERROR declared>=9 executed=9 passed=3 failed=6 skipped=0 dropped=0

Failing examples: "admits unchanged bounded inputs before scheduler work",
"fails closed on source, output, provenance, and interrupted pointer
publication", "rejects stale invocation identity and deleted or corrupt
generations", "recursively rejects deleted and corrupt ancestors", "preserves
and recovers an unselected immutable generation collision", "misses when any
representative canonical build control changes".

This predates the lane (inferred from the 9-example run, not measured at that
sha): the file had 8 examples and 6 failed the same way. Every failing example
is one that writes a fixture file.

## Repro

    cd <worktree>; bin/simple test \
      test/03_system/compiler/feature/native_zero_work_admission_spec.spl

Binary identity: `bin/simple` -> the Rust seed at
`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b...` (first 16). Duration ~9s.

## Cause

The spec declares, at its top:

    extern fn rt_file_write(path: text, content: text) -> bool

`rt_file_write` exists in the C runtime (`src/runtime/runtime.c:1904`,
`src/runtime/runtime_legacy_core.c:464`) but is NOT in the compiler's extern
registry -- `grep -rn '"rt_file_write"' src/compiler/` returns nothing -- so
the frontend cannot resolve the declaration. The declaration every other system
spec under `test/03_system/compiler` uses is `rt_file_write_text`, which is
registered and resolves.

This is the "declared but unbacked extern" class tracked by
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md` and fenced
by `scripts/check/check-unbacked-extern-ratchet.shs`, except that here it
surfaces as a hard semantic error rather than a silent nil, because it is a
call in a spec rather than a call in product code.

## Why it was not fixed here

Six failing examples are six real assertions about the zero-work admission
cache that nobody is currently running, and switching their declaration is a
one-word edit -- but it is an edit to six examples whose green behaviour has
never been observed on this tree, in a lane whose scope is the Stage-2
bootstrap blockers. Turning six unknown reds into six unknown greens inside a
bootstrap lane is how a real regression gets laundered. The declaration is left
exactly as it is. Fix is either to register `rt_file_write` in the extern
registry or to move the six examples onto `rt_file_write_text`, with each
example's verdict inspected on the way.

The example added on 2026-09-12 ("refuses to publish a receipt for a request
with no identity") declares `rt_file_write_text` for exactly this reason, so
that its own red/green says something about the code under test.
