# `use std.spec.step` puts a duplicate `file_rename` in the unit; every atomic write self-recurses
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-08-27
- Found by: SCV-IMPL-B-01 (sj-capsule transaction coordinator)
- Binary: deployed seed `bin/release/x86_64-unknown-linux-gnu/simple`
- Status: FIXED 2026-11-11 — runner8 triage; `file_rename` wrapper now forwards to uniquely-named `rename_path`, repro + regression spec green on seed lane. See addendum at end.

## Symptom

Any spec that (a) carries the bare line `use std.spec.step` **in addition to**
the braces form `use std.spec.{describe, it, expect, step}`, and (b) reaches a
write that goes through `src/lib/scv/store.spl`'s `scv_write_text` ->
`atomic_write`, dies with:

```
stack overflow: recursion depth 1000 exceeded limit 1000 in function 'file_rename'
```

The failure is **not** in the spec's own code and names no user function — it
looks like an infra hang, which is why it cost most of a session to localize.

## Bisection

Reduced to a 9-line spec that only acquires and releases a capsule lease:

| spec content | result |
|---|---|
| braces import only | `Results: 1 total, 1 passed, 0 failed` |
| + one added line `use std.spec.step` | `stack overflow ... in function 'file_rename'` |

Nothing else changed. The same module functions called from a plain `bin/simple
run` script always worked, and the same journal/WAL calls made *directly* from a
spec body (rather than from inside a library module) also worked — so this is a
flattened-compilation-unit symbol-resolution problem, not a logic bug.

## Mechanism (consistent with an existing note in the tree)

`src/lib/nogc_sync_mut/io/file_ops.spl:272-275` defines

```
use std.io_runtime.{file_rename as runtime_file_rename}
fn file_rename(src: text, dst: text) -> bool:
    runtime_file_rename(src, dst)
```

i.e. a wrapper whose body calls the *aliased* import. `src/lib/nogc_sync_mut/
io_runtime.spl:576-578` already warns in a comment that
`file_move_cross_device` was given a "unique semantic name" specifically to
"avoid the flattened-unit `file_rename` collision". When a second definition of
`file_rename` enters the unit, the alias `runtime_file_rename` resolves back to
the wrapper itself and the call becomes unbounded self-recursion. The bare
`std.spec.step` import is one way to pull that second definition in.

## Why it matters beyond one spec

- The failure mode is silent-until-write and blames a stdlib function, so it
  reads as flaky infra rather than a defect.
- The bare `use std.spec.step` line appears in many SCV specs. They pass only
  because they never perform an atomic write in-process; any of them gains this
  crash the moment it does.
- The general defect (a duplicate symbol dispatching to itself instead of to the
  aliased import) is not specific to `file_rename` and is the same class as the
  already-reported `mcdc_condition_key` co-compiled-definition warning the
  compiler prints on every test run.

## Workaround in place

`test/integration/app/scv_sj_capsule_spec.spl` (and its `test/02_integration`
twin) omit the bare `use std.spec.step` line and import `step` only in the
braces form, with a comment pointing here. Nothing else was changed and no
product code was altered to accommodate this.

## Suggested fix

Make flattened-unit duplicate resolution prefer the alias binding recorded at
the definition site, or reject a duplicate top-level `fn` whose body calls an
import aliased to the same name. Either turns a silent infinite recursion into a
diagnostic.


---

## Addendum 2026-11-11 — runner8 P3 triage: FIXED

Verified fixed on release/1.0.0 tip (worktree `simple-p3-runner8-20261111`).

Root-cause fix already in the tree: the `file_rename` wrapper in
`src/lib/nogc_sync_mut/io/file_ops.spl:451-456` no longer forwards to an
import aliased to its own name; it calls the uniquely-named
`rename_path(old_path, new_path)` forwarder (`src/lib/nogc_sync_mut/io_runtime.spl:503-507`,
rework landed with merge 9e7e7a526edb, 2026-11-07). With the wrapper calling a
unique name, a second `file_rename` co-compiled into the flattened unit can no
longer dispatch back to the wrapper, so the unbounded self-recursion through
`scv_write_text -> atomic_write` is structurally impossible. `dir_remove_all`
(`src/lib/nogc_sync_mut/io/dir_ops.spl:84-85`) likewise now calls its own raw
extern lane and never touches `file_rename`.

Evidence (seed binary, tracked `bin/simple.exe` @ 46fe8f6b6def,
`SIMPLE_LIB=src ... test <spec> --mode=interpreter --no-cache`):

- Repro of the original failing shape — `scv_sj_capsule_spec` content plus the
  bare `use std.spec.step` line: `SPEC FILE VERDICT ... outcome=OK declared>=14
  executed=14 passed=14 failed=0`.
- Regression coverage committed in the same change: the workaround was removed
  from `test/02_integration/app/scv_sj_capsule_spec.spl` — the bare
  `use std.spec.step` line is imported again (with a comment naming this bug)
  and the spec passes 14/14 on the seed interpreter lane. `test/integration/`
  was consolidated into `test/02_integration/` by 4f51a7ee31fc, so one live
  copy remains.

Residual (separate concern, seed lane): the GENERAL flattened-unit defect —
a duplicate top-level fn whose body calls an import aliased to the same name
still self-dispatches; the tree still emits `compiler_cross_module_private_symbol_collision`
warnings for other duplicate pairs (e.g. `print_summary`, `spipe_helpers_used`)
on every test run. That class needs a compiler/seed-lane decision (alias-aware
duplicate resolution or a hard diagnostic); this row's named `file_rename`
symptom is closed.
