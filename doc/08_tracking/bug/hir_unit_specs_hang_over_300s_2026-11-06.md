# HIR unit specs run longer than 300 s (hang) on the seed

- **Found:** 2026-11-06 during the W2b before/after directory runs (data plan W2b).
- **Seed:** a Rust seed built from release `4d7dda0c117`, which includes the W2a change.
- **Tree:** the unmodified base `4d7dda0c117`, so the hangs are pre-existing and do not come from W2b.
- **Specs:** each ran past 300 s with no output and was killed. Before W2a's seed rebuild, `module_surface_semantic_projection_spec` also ran past 12 min.
  - `test/01_unit/compiler/hir/module_surface_semantic_projection_spec.spl`
  - `test/01_unit/compiler/hir/field_index_erased_receiver_spec.spl`
  - Only these two hit the 300 s reaper in that run, which covered 139 of the directory's 287 specs before it was stopped.
- **Repro:** `simple test test/01_unit/compiler/hir/module_surface_semantic_projection_spec.spl`. The `[route] mode=interpreter` line prints, then the process stays busy with no further output.
- **Expected:** a verdict, or a failing assertion, within the runner's per-file budget. A hang is a defect: it blocks every directory-lane run of `test/01_unit/compiler/hir`.
- **Next step:** run each spec with `SIMPLE_JIT_STRICT=0` and a stack sampler to find the looping pass. Whether the cause is the seed interpreter or the spec's own fixture size is not known yet.

## Re-run 2026-11-08 (Windows, `C:/dev/simple/bin/simple.exe` seed, release/1.0.0 sparse worktree)

- `field_index_erased_receiver_spec.spl`: **no longer hangs** — finishes in 10 s with
  `outcome=ERROR executed=1 failed=1`. The failure is environmental, not a loop: every
  receiver shape reports `BUILD-FAILED: absolute runtime/workspace required` (the spec
  native-builds probes and needs an absolute runtime/workspace, absent in this checkout).
- `module_surface_semantic_projection_spec.spl`: **still exceeds budget** — killed by the
  kill_monitor watchdog at 318 s (exit 143, `reason=child-died-early`), no example output.
  The spec's own docstring says it loads the full frontend in-process (`parse_and_build_module`
  + `module_surfaces_from_modules`) and to "expect a multi-minute interpreter run", so this is
  interpreter cost of the fixture, not yet proven an infinite loop.
- Still open: needs a stack sample (`SIMPLE_TIMEOUT_SECONDS=3600` run to completion, or a
  sampler) to decide between "slow but terminates" (move to a slow/perf lane, or split the
  scenarios) and a real loop in the projection. Not fixable in a lib-only lane without that data.

## 2026-11-09 note (PR #7883)
Still open. The bare-path scan hang in `module_path_naming.spl` is worked around with typed
`byte_len` bindings; root cause is `seed_untyped_byte_len_binding_raw_i64_misdecoded_2026_11_09`.
The spec file is still slow and 4 scenarios still fail, so this row is not resolved. Known twin:
`src/compiler/bootstrap_admission/stage2_module_path_naming.spl` keeps the untyped form.

## 2026-11-09 root cause + fix (hang) — fix-implemented-verification-pending
Root cause: the pure-Simple bitfield parser (`_ParserDecls/bitfield_aop_arch_decls.spl`)
did not accept the seed's bare bit-width field form `mode: 4`
(`compiler_rust/parser/src/types_def/bitfield.rs` parses an integer width). The IntLit was
never consumed, so the field loop re-reported the same parser errors forever — the
"changes for bitfield widths" scenario never returned (probe: a single
`parse_module_silent_checked("bitfield Flags(u32):\n    mode: 4\n ...")` hit the 400 s
watchdog; `mode: u4` parses in seconds). Fix: accept `name: N` as `uN`, plus a
forward-progress guard in the field loop. New `test/01_unit/compiler/parser/bitfield_bare_width_spec.spl` 4/4.
`module_surface_semantic_projection_spec` now finishes in ~72 s (was >3600 s, killed):
12 executed, 7 passed, 5 failed — sort-comparator hoist, field defaults/array-size,
export route, unresolved imports, bitfield widths/extend payload. Those are semantic-identity
assertion failures, not hangs; tracked as the remaining work on this row.
