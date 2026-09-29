# `simple lint` SIGSEGVs in the JIT lane for any file whose basename ends `_spec` — content-independent
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-13)
- Found: 2026-09-13, PERF-9, while trying to reproduce PERF-5's report.
- Component: default (JIT-attempt) execution lane reached by `simple lint`.
- Lane: default only. `SIMPLE_EXECUTION_MODE=interpret` returns rc 0 every time.

## The discriminator, isolated

**It is the FILE NAME, not the content, not the path, and not the invoking
binary's location.** Two byte-identical five-line files in the same directory,
linted by the same binary from the same cwd:

```
printf 'use std.spec\n\ndescribe "x":\n    it "y":\n        expect(1).to_equal(1)\n' > /tmp/x/c1.spl
cp /tmp/x/c1.spl /tmp/x/c1_spec.spl

./bin/simple_pin lint /tmp/x/c1.spl        # rc 0, 3 runs of 3
./bin/simple_pin lint /tmp/x/c1_spec.spl   # rc 139 (SIGSEGV), 3 runs of 3
```

`cmp` reports the two files identical. Renaming a crashing file to drop the
`_spec` suffix makes it pass; renaming a passing file to add the suffix makes
it crash. Both directions verified, 3 runs each, no flake.

## Relation to the two existing records — a SECOND discriminator, not a correction

`lint_default_lane_segfault_from_worktree_bin_path_2026-09-13.md` (PERF-5) was
**not reproduced at this base**, and this record does not claim to refute it.
PERF-5's exact shape — the deployed seed `3d120a6f9ab5704b2225` linting
`src/lib/common/base_encoding.spl` from a worktree root — returns rc 0 here.
But PERF-5 ran it at `f26970e9d93` and this lane is at `2cb951036a4`, and lint
reads `src/lib/**` as SOURCE on every run, so the two probes did not lint the
same bytes. The honest reading is that PERF-5's probe is not reproducible at
this base and that there is a second, independent discriminator — the one
isolated above — which PERF-5's data cannot speak to because it named a target
(`base_encoding.spl`) that does NOT end in `_spec`. Whether the two are one
defect or two is open.

Likewise this is not evidence against
`lint_intermittent_segv_on_deployed_seed_2026-09-13.md`. What is true is
narrower: **in this lane's probes, once the file name is held fixed, the
outcome is deterministic** — 10/10 crashes on one name, 3/3 clean runs on a
byte-identical file under another. Apparent flake across differently-named
fixtures is explained by the name; flake on ONE name is not, and is not
observed here.

## Binary dependence — this is a REGRESSION, not an old defect

| binary | `c1_spec.spl` | `base_encoding.spl` |
|---|---|---|
| seed built from `2cb951036a4` (`633b3aabe70c149b9400`) | **rc 139**, 10/10 | rc 0 |
| deployed seed `3d120a6f9ab5704b2225` (Sep 6, `bin/release/aarch64-unknown-linux-gnu/simple`) | rc 0, 5/5 | rc 0 |

The Sep-6 deployed seed does not crash. A seed built from `origin/main` at
`2cb951036a4` does, every time. So the defect landed between those two points
and is live on `main` now. (The deployed seed does return rc 1 — not a crash —
on a large real spec file; that run's output went to `/dev/null`, so the
message was not captured and the resemblance to
`lint_string_index_out_of_bounds_on_spec_files_2026-09-13.md` is **unverified**.)

Reproduced identically on this lane's candidate seed, whose changes are
confined to the interpreter's call path, so it is not caused by them.

## What is known about the fault

`gdb -batch -ex run -ex bt` gives `Thread 2 "simple-main" received signal
SIGSEGV` with **no resolvable frames** (`#0 0x0000ffffd423510c in ??`), i.e.
the fault is inside JIT-emitted code, not in a symbol of the binary. That is
consistent with `SIMPLE_EXECUTION_MODE=interpret` avoiding it completely, and
with the other open JIT-lane lint crashes
(`lint_directory_target_segv_in_jit_lane_2026-09-12.md`,
`lint_jit_abort_on_src_app_sj_2026-09-05.md`,
`lint_segv_on_unit_spec_files_2026-09-12.md`).

## Next step

Find where lint's pipeline branches on a `_spec` basename — a spec-file rule
set, an sspec-aware path, or a module-name derivation — and which of those
reaches the JIT. The five-line fixture above makes this cheap to bisect; a
`_spec`-named file with an EMPTY body is the next probe to try, to separate
"the name selects a different pipeline" from "the name selects a pipeline that
then chokes on `describe`/`it`".

## Workaround

`SIMPLE_EXECUTION_MODE=interpret bin/simple lint <spec>` — rc 0, correct
verdict.

