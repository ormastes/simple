# Aspect/dynload lane — plan (authored 2026-08-19)

My plan for this lane, written after re-verifying the tree rather than from memory.

Binary identity at authoring time (stamp before AND after every step below; other
sessions swap this symlink, so an unstamped verdict is worthless):
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
59645008, 2026-08-18 10:12:23.164167908 +0000.

Machine hazard, measured this session: ~18 GB of 128 GB available, swap 0, and
**33 orphaned `simple` processes holding 92.4 GB**. earlyoom
(`--prefer simple|rustc|cc1 --avoid claude`) SIGTERMs at 10% free and SIGKILLs at
5%; 699 SIGTERMs hit `simple` in 6 hours. Separately the kernel OOM killer took
three claude sessions at 23:30:27 after a memory-guard script set
`oom_score_adj=1000` on them. **Exit 143/137 is an OOM kill, not a verdict** —
re-run, never record. One `simple` process at a time, detached with
`nohup setsid`, never wrapped in `timeout`.

## Position vs origin (re-verified, changed twice during the session)

At 23:47 `ca7c33ecf75` was my ANCESTOR (0 behind / 3 ahead), so no rebase was due.
By 00:xx origin had genuinely moved to **`e347858a954`** and I am now
**12 behind / 3 ahead**. A rebase IS now required. `git ls-remote` is the
authority here, not the local ref.

My 3 commits: `ca7c33ecf75` (base) -> `acd936994ba` (static component table) ->
`5ffd9e20e59` (SIF v1) -> `013f1b33a10` (this session's loader+aspect work).

## What has ACTUALLY landed

| Piece | State | Evidence |
|---|---|---|
| SIF v1 (`80.driver/sif/sif.spl`) | committed, specs green | `5ffd9e20e59`; roundtrip + discrimination specs exit 0 |
| aspect_pack container/catalog/loader | committed, 39 fns, specs 7/7 + 9/9 | `013f1b33a10` |
| segment mapper (one mmap per SEGMENT) | committed, WIRED | `module_loader_compat.spl:15` imports it; `:302` `map_segment`, `:312` `bind_symbol` |
| **smf_mmap_native real native layer** | committed — the real fix | was a Dict fake (`_g_fake_memory`, `native_call_function_0` -> `return 0`); now `rt_mmap_raw`/`rt_mprotect`/`rt_ptr_*` |
| ABI mismatch gate | genuinely wired | compare at `aspect_pack.spl:870`, error `:872`, asserted by defect spec `:240` |

## What is NOT done — stated plainly

**1. Neither SIF nor aspect_pack has a single product caller.** Verified by grep:
`use .*aspect_pack` across `src/**.spl` returns ZERO importers; the only mention
is `aop_group_manifest.spl:39` `aspect_pack_artifacts` commented
"SPEC-FORWARD: no aspect packs yet". SIF likewise has no importer outside its own
directory. Both are spec-proven libraries that nothing calls. This is the same
unwired-code defect class CLAUDE.md documents for `interface_digest_of` and
`smf_manifest_entry_verifies`, and it is the single most important gap in the
lane — passing specs are not the same as being in the load path.

**2. Execution of mapped code is unproven.** `segment_symbol_resolution_spec`
stands at 7/8 with the POSITIVE CONTROL honestly red: this interpreter cannot
invoke a raw `i64` code address (no working pointer cast — `unsupported cast
target type: Pointer` — and no `rt_call_*` extern). Arithmetic, bounds, lifecycle
and the native layer are proven; RUNNING code is not. Filed:
`doc/08_tracking/bug/loader_interpreter_cannot_call_raw_code_address_2026-08-18.md`.

**3. Deliberately not implemented** (recorded, not forgotten): PackRef
`content_hash`/`index_hash`/`signature_policy` (grep: 0 occurrences — no verifier
or signing authority in-tree, an unchecked hash is decoration);
`required_core_public_abi_hash` is carried and round-tripped but NEVER compared
(nothing publishes a core ABI hash, so the gate would be fake); multi-profile
catalogs §9.6; zstd dictionaries / co-load clusters §12.2 (design says optional);
AspectPackIndexCache + `pread`/`WILLNEED` policy §14.1/§15 (needs a file layer
this byte-array module lacks); unload §14.7 (design says not required initially).
§12.1/§23 remain PARTIAL — the pack is a standalone container, not yet a
registered SMF section type.

**4. Lint is INCONCLUSIVE, not green.** `lint-cached.shs` FAILs on every file
including an untouched control, with an unattributed
`undefined field 'config'`. Filed. No lane file's lint result may be quoted as a
pass until that is fixed.

## Order of work

1. **Rebase onto `e347858a954`** and re-verify: the guard verdicts I already hold
   (conflict-tree, markers, tree-size, runtime-API, divergence-delta — all PASS
   for `ca7c33ecf75..013f1b33a10`) are STALE the moment the base moves. Re-run
   all of them with an explicit range; the four that returned
   `ERROR — nothing was checked` did so because this is a linked worktree whose
   `.git` is a file, and exit 2 is never a pass.
2. **Record the 2 pre-existing divergence offenders** in the commit message or a
   `doc/08_tracking/bug/` record. The delta-PASS escape REQUIRES this; an
   unrecorded step-over is a violation even with a clean delta.
3. **Land** via `sh scripts/check/land.shs` — never raw `jj git push`, which
   skips the rules.sdl gates entirely.
4. **Close gap #1 — wire something.** Pick ONE real caller for the segment loader
   path and one for the aspect catalog, and prove it with a spec that fails if the
   wiring is removed. Unwired code is the lane's actual risk, not missing features.
5. **Close gap #2 — prove execution.** Cheapest credible route is an
   `rt_call_ptr_0(addr: i64) -> i64` extern in the C runtime; alternatives are
   making the pointer cast compile, or running the spec in a compiled-mode lane.
6. Only then consider §12.1/§23 (pack as a registered SMF section type). Every
   other unimplemented section stays deliberately unbuilt until something needs it.

## What I will NOT do

Add features from the design doc that nothing calls; run `--update-baseline` on
the no-direct-rt ratchet (197 below baseline is a deliberate reviewed action, not
a drive-by); weaken the positive control to make the board green; or commit any
out-of-lane file (jit_typed_ir, doc_coverage option-route, gui_web reports, Rust
`dispatch_profile`, `persistent_code_cache`) that other lanes authored.
