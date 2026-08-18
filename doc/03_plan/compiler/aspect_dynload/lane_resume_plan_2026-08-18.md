# Lane aspect-dynload — resume plan (2026-08-18)

Worktree: `/mnt/data/worktrees/lane-aspect-dynload`. Tip `5ffd9e20e59`.
`origin/main` re-fetched this session: still `ca7c33ecf75` — my tip is 2 commits
ahead of it, already on top of it. **No rebase needed** (verified, not assumed).

Binary identity at plan time:
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
59645008 bytes, 2026-08-18 10:12:23 UTC. Re-stamp before/after every run — the
symlink target is swapped by other sessions.

Environment hazard: earlyoom (`-r 3600 --prefer simple|rustc|cc1`) SIGTERMs at
10% free RAM, SIGKILLs at 5%. Expect exit 143 with no dmesg record. Run one
compiler process at a time, detached via `nohup setsid`, never under `timeout`.

## What already landed

- **SIF v1** (`5ffd9e20e59`, committed, +357 lines): `src/compiler/80.driver/sif/sif.spl`
  — canonical separable module-interface artifact, closing audit gap #19.
  Specs: `test/01_unit/compiler/driver/sif_{roundtrip,discrimination}_spec.spl`.
- Static component table generator (`acd936994ba`).

## What is written but UNCOMMITTED (this lane's remaining work)

| File | LOC | State |
|---|---|---|
| `src/lib/common/aspect_pack.spl` | 604 | `kind=aspect_pack` SMF container + Aspect Catalog + counters (design §11/§12). No TODO markers. |
| `src/compiler/99.loader/segment_mapper.spl` | 342 | one-mapping-per-segment mapper (startup_perf §8.4/§8.15) |
| `src/compiler/99.loader/smf_segment_load.spl` | 61 | SMF section -> segment extents |
| `src/compiler/99.loader/module_loader_compat.spl` | (mod) | wires the per-symbol loop onto the segment mapper |
| specs | 4 files | `aspect_pack_{,defect_class_}spec`, `segment_{mapping_count,symbol_resolution}_spec` |

Out-of-lane untracked files also present in this tree (jit_typed_ir,
doc_coverage option-route, gui_web reports, persistent_code_cache, Rust
interpreter dispatch_profile). **Not mine to land** — leave uncommitted, do not
fold into an aspect-dynload commit.

## Verification order (before trusting any prior conclusion)

1. Re-stamp binary identity.
2. Run the 4 lane specs individually, detached, sequential:
   `aspect_pack_spec`, `aspect_pack_defect_class_spec`,
   `segment_mapping_count_spec`, `segment_symbol_resolution_spec`.
   Exit 143 == OOM-killed, NOT a failure — re-run, don't record a verdict.
3. Re-run the SIF specs to confirm the committed work still passes on the
   current binary (it was verified against an earlier one).
4. Lint only the changed `.spl` files, one file per invocation (batching
   exceeded 600s historically).
5. `git commit` in this worktree. **Do NOT push** (per lane instruction).

## Open risk

`module_loader_compat.spl` is the only modified *existing* file in the loader
path; a regression there is a whole-loader regression. Its spec evidence
(`segment_mapping_count_spec`) must be green on the current binary before
commit, not on a remembered run.

## Verification RESULTS (2026-08-18, this session)

Binary identity byte-identical before AND after the whole spec run and the whole
lint sweep: `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
59645008, 2026-08-18 10:12:23.164167908 +0000. No mid-run swap, so these
verdicts are trustworthy.

### Specs — 5 green, 1 real failure

| spec | exit |
|---|---|
| `aspect_pack_spec` | 0 |
| `aspect_pack_defect_class_spec` | 0 |
| `segment_mapping_count_spec` | 0 |
| `segment_symbol_resolution_spec` | **1 — FAIL** |
| `sif_roundtrip_spec` | 0 |
| `sif_discrimination_spec` | 0 |

SIF v1 re-confirmed green on the CURRENT binary, not merely the one it was
written against.

The failure (exit 1, not 143 — genuine, not an earlyoom kill):

```
POSITIVE CONTROL: the mapped code still executes correctly
  x calls each symbol and gets that symbol's own value back
    assert_equal failed: expected 33, got 0
```

7 of 8 examples pass, including "places each symbol at base + its segment
offset", "gives three DISTINCT addresses from a single mapping", and all five
bounds/lifecycle examples. So the address arithmetic and the mapping lifecycle
are correct, but **the mapped code does not execute**. A clean `0` rather than a
segfault or garbage fits a zeroed anon mmap whose code bytes were never copied
in — ranked suspects: (1) segment payload never memcpy'd into the region,
(2) wrong source offset (`smf_payload_file_offset` vs section-relative) in
`smf_segment_load.spl`, (3) RW->RX transition / icache flush ordered before the
copy instead of after.

**Consequence: the lane's headline claim — one mmap per SEGMENT instead of one
per SYMBOL — is currently proven only as ARITHMETIC, not as WORKING CODE. Not
commit-ready.** The positive control must not be weakened or deleted to reach
green; it is the only example proving the loader still emits running code.

### Lint — INCONCLUSIVE, blocked by a tool defect

Not a pass and not a fail. `sh scripts/check/lint-cached.shs` returns
`FAIL — 1 file(s) checked, 1 with findings` for EVERY file, with a single
unattributed diagnostic:

```
error: semantic: undefined field 'config': cannot access field on value of type 'object'
```

Control experiment: identical error text at the identical log-line offset (251)
for `src/lib/common/aspect_pack.spl` and for the untouched known-good control
`src/lib/common/base_encoding.spl`. `.config` appears ZERO times in
`aspect_pack.spl`. The diagnostic is therefore independent of the file under
lint — a lint-tool defect, and lint is repo-wide non-discriminating right now.
Filed: `doc/08_tracking/bug/lint_semantic_undefined_field_config_every_file_2026-08-18.md`.
Not localised within its time-box; unconfirmed candidates are `linter.config` /
`self.config` accesses at `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:113,406-442`
and `lint_checks.spl:212`.

No lane source was modified to appease this diagnostic, and no lane file's lint
verdict should be quoted as a pass.
