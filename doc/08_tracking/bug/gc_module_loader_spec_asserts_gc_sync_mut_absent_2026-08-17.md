# `gc_module_loader_spec` asserts `src/lib/gc_sync_mut` does not exist — it does, with 867 files

- **Filed:** 2026-08-17
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Status:** OPEN — needs an architecture decision, not a test edit
- **Severity:** medium (1 RED example; the spec is an architecture gate)
- **Spec:** `test/feature/lib/gc_parity/gc_module_loader_spec.spl`

## Symptom

Sweep of `test/feature/lib` (81 total, 72 passed, 9 failed):

```
FAIL  test/feature/lib/gc_parity/gc_module_loader_spec.spl (1 passed, 1 failed, 825ms)
      Error: Process exited with code 1
SPEC FILE VERDICT: ... declared>=2 executed=2 passed=1 failed=1 dropped=0
```

The failing example is `"does not expose an unimplemented gc_sync_mut family"`,
which shells out via `rt_process_run("/bin/sh", ["-c", "test -d src/lib/gc_sync_mut"])`
and asserts the directory is **absent**:

```
expect(_has_gc_sync_mut_source_dir()).to_equal(false)
```

Its docstring states the intent:

> gc_sync_mut/ is intentionally not a public variant directory. Sync GC-related
> contracts are covered by nogc_sync_mut/gc and nogc_sync_mut/ptr until a future
> family is explicitly designed. ... The source tree should not contain a stub
> family that reverses the no-GC-first direction.

## Measured reality

```
$ find src/lib/gc_sync_mut -name '*.spl' | wc -l
867
$ ls -d src/lib/gc_sync_mut src/std/gc_sync_mut
src/lib/gc_sync_mut
src/std/gc_sync_mut
```

`src/lib/gc_sync_mut/` contains `__init__.spl`, `log.spl`, and subtrees
`terminal/ shell/ service/ net/ unsafe/ testing/ websocket/` among others, and
is mirrored at `src/std/gc_sync_mut/`. Sibling families `gc_sync_immut/`,
`gc_async_immut/` and `gc_async_mut/` are present too. This is a fully realized
family, not the "stub family" the spec was written to fence out.

## Why this was NOT fixed by editing the test

Flipping the assertion to `to_equal(true)` would make the suite green by
asserting whatever the tree currently happens to contain — which is precisely
the failure mode this spec exists to prevent. The spec encodes a deliberate
architectural direction ("no-GC-first"); a 867-file family either

- **supersedes that decision**, in which case the decision doc must be updated
  first and the spec then rewritten to gate the *new* invariant (e.g. that the
  family is complete and mirror-synced), or
- **violates it**, in which case the spec is correct and the tree is the defect.

Determining which requires the owner of the runtime-family matrix. Recorded
rather than guessed.

Note the spec's other example ("accesses array utilities after migration")
passes, so this is a single-assertion staleness, not a broken file.

## Repro

```
SIMPLE_TIMEOUT_SECONDS=600 bin/simple test test/feature/lib/gc_parity/gc_module_loader_spec.spl
```
