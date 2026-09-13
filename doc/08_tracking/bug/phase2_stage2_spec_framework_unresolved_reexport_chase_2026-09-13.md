# Stage-2 (phase 2) cannot native-build almost any spec: `std.nogc_sync_mut.spec`'s own transitive deps fail HIR reexport-chase resolution

## FILED, not fixed — 2026-09-13, FULLTEST lane

## Symptom

Native-building an ordinary `test/01_unit/compiler/**/*_spec.spl` file with
the pinned Stage-2 (phase 2) binary fails during HIR lowering, not because of
anything in the spec file itself, but because the spec DSL's own facade
(`std.nogc_sync_mut.spec`, exporting `describe`/`it`/`expect`) fails to
resolve several of ITS OWN transitive dependencies. Representative log lines
(`src/std/nogc_sync_mut/spec.spl` is the facade every spec imports via
`use std.spec`):

```
[hir-fatal] ... HIR lowering error in src/std/nogc_sync_mut/spec.spl: unresolved name: process_run at src/std/nogc_sync_mut/spec.spl:29:21
[hir-fatal] ... HIR lowering error in src/std/nogc_sync_mut/spec.spl: imported enum `SkipRejectReason` has no declaration owner
[hir-fatal] ... HIR lowering error in src/lib/nogc_sync_mut/spec/skip_governance.spl: unresolved name: read_file_text ...
[hir-fatal] ... HIR lowering error in src/lib/nogc_sync_mut/spec/skip_governance.spl: unresolved name: time_now_unix_micros ...
[hir-fatal] ... HIR lowering error in src/compiler/common/assurance/policy.spl: imported enum `AssuranceGrade` has no declaration owner
[hir-fatal] ... HIR lowering error in src/compiler/common/assurance/policy.spl: imported enum `AssuranceConvention` has no declaration owner
[hir-fatal] ... HIR lowering error in src/compiler/common/assurance/policy.spl: imported enum `AssuranceStrictnessV2` has no declaration owner
[hir-reexport-chase-unresolved] facade=std.nogc_sync_mut.spec item=Any local=Any importer=<any spec file>: the facade neither declares this name nor routes it through a resolvable re-export; ...
```

Downstream, because the facade itself is "poisoned"
(`[hir-poisoned] ... module=std.nogc_sync_mut.spec errors=0->1`), every
importing spec file then reports its OWN symptom of the same root cause —
most commonly `unresolved name: expect` / `unresolved name: it` at whatever
line first calls into the DSL.

## Scope: measured on a 28-spec sample, not a handful of outliers

Sampled 28 `test/01_unit/compiler/**/*_spec.spl` files (mixed: light
black-box specs with no `use compiler.*` import, and a few heavier
white-box specs), native-built one at a time with
`SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1
bin/release/aarch64-unknown-linux-gnu/simple.phase2 native-build <spec> -o
<out>`, timeout 120s each:

| outcome | count | first-error signature |
|---|---|---|
| HIR reexport-chase / unresolved-name failure rooted in `std.nogc_sync_mut.spec`'s own deps | 24/28 (~86%) | `[hir-reexport-chase-unresolved] facade=std.nogc_sync_mut.spec item=Any ...` or the downstream `unresolved name: expect`/`it` symptom |
| parse error, pre-existing FILED bug (`spawn_call_expr_silently_becomes_nillit_2026-07-29.md`) | 1/28 | `flat AST bridge: unhandled expr node kind (tag=50)` |
| native-build TIMEOUT (>120s), heavy `use compiler.*` entry closure, still in the parse phase | 1/28 | see companion note below, not filed separately here |
| native-build process SEGV | 1/28 | see `phase2_stage2_native_build_segv_callback_trampoline_spec_2026-09-13.md` |
| (already investigated this lane, excluded from this count) `scalar_compound_reassign_not_array_merge_spec.spl` | - | fixed in `dea98eba7f9` |

This is **not** a spec-specific defect and is **not** one of this lane's two
known P0s (`phase2_drops_loop_carried_accumulator`,
`phase2_str_returns_raw_pointer`) — it reproduces on almost every spec
sampled, light or heavy, because `use std.spec` is present in essentially
every spec file in the tree, and the facade itself is what fails to lower.
Practically, this means the pinned phase-2 (Stage 2) binary currently
**cannot native-build the test suite's own spec files at all**, independent
of anything under test.

## Why this is plausible as a real (not environmental) defect

- The SAME binary, run as `bin/simple test <spec>` (phase 1, the Rust seed
  interpreter), runs these same spec files and their `use std.spec` import
  fine — this is not a missing file or a bad `SIMPLE_SOURCE` path, it is
  specifically the phase-2 HIR lowering pass mishandling re-export chains
  through `std.nogc_sync_mut.spec` -> `lib.nogc_sync_mut.spec.skip_governance`
  -> `compiler.common.assurance.policy` that the seed's own HIR lowering
  resolves without complaint.
- The enums named (`SkipRejectReason`, `AssuranceGrade`, `AssuranceConvention`,
  `AssuranceStrictnessV2`) and the free functions named (`process_run`,
  `read_file_text`, `time_now_unix_micros`, `rt_env_cwd`) are real,
  declared symbols in this tree, not typos — the failure is "has no
  declaration owner" / "unresolved name", i.e. Stage 2's own re-export/name
  resolution losing track of where a name is declared as it chases through
  several facade hops, not the name being absent.

## Not investigated further in this lane (out of budget)

Root cause not narrowed past "reexport-chase resolution breaks on this
specific facade chain, in Stage 2's own HIR lowering, for names reached
through >=2 facade hops." Candidate next steps for whoever picks this up:
reproduce narrowly with a 3-file minimal facade chain (module A re-exports
an enum from module B, module C imports A), same in-process
`parse_full_frontend -> HirLowering.lower_module` technique used elsewhere in
this lane (fast, no native-build subprocess needed), to isolate whether the
break is at the `SkipRejectReason`/`Assurance*` enum-import step specifically
or the generic multi-hop facade chase.

- Filed by: FULLTEST lane, `work/fulltest-phase2-2026-09-13`
- Binary: pinned Stage-2 candidate `bin/release/aarch64-unknown-linux-gnu/simple.phase2`, sha256 `d19daa8c090c2a30ec6f56304ea354c947edc870c822235f97b97b3d30e0d1ae`
- Class: `build-failed` (HIR lowering), affects native-build of the test suite broadly, not runtime correctness of a specific program
