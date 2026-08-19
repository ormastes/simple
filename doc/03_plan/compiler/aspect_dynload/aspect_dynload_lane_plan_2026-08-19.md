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

## Update 2026-08-19 — research findings folded in as work items

Source: `doc/01_research/compiler/startup_perf/aspect_dynload_startup_loader_perf_research_2026-08-19.md`
(static reading only, no compiler run). Each item below was re-verified by me at
file:line before being written down.

### W1. W^X violation — DONE this session

`native_alloc_exec_memory` mapped `PROT_READ|PROT_WRITE|PROT_EXEC`, handing out a
simultaneously writable+executable page. Forbidden by startup_perf §8.5. The
alloc -> write -> `native_make_executable` sequence
(`segment_mapper.spl:124,129,134`) already grants RX by `mprotect` afterwards, so
`PROT_EXEC` at map time bought nothing. Now maps RW only.

### W2. The segment win is plausibly cancelled by a byte-at-a-time copy — OPEN, highest priority

`native_write_exec_memory` (`smf_mmap_native.spl:157-170`) writes **one byte per
SFFI call** in a `while` loop over `rt_ptr_write_u8`, and `smf_section_bytes`
copies byte-by-byte again before it. So the lane traded O(symbols) syscalls for
O(bytes) SFFI calls. The headline claim — that one-mapping-per-segment is FASTER
— is therefore **not established**, and could be a regression on large sections.
`rt_memcpy` exists but is pointer-typed and unreachable from an `i64` address.
Fix: a bulk `rt_ptr_write_bytes(addr, offset, [u8])`-style extern. **This must be
measured, not assumed, before the lane claims a perf win.**

### W3. Mapped code still cannot execute — OPEN

All four `native_call_function_N` return 0 unconditionally; no `rt_call_ptr_*`
extern exists anywhere in `src/runtime/*.c`. The RED positive control in
`segment_symbol_resolution_spec` is CORRECT and stays red. Cheapest route is an
`rt_call_ptr_0(addr: i64) -> i64` extern. Same root cause as W2: no way to reach
a raw address from Simple except one byte at a time.

### W4. Duplicate loader trees, and the FABRICATING one is the exported one — OPEN

`99.loader/object_mapper.spl:31-58` fabricates addresses arithmetically
(`4096 + gen*256 + len`) rather than mapping anything, and it is the mapper that
`99.loader/__init__.spl:34-38` re-exports. The real one (`segment_mapper.spl`) is
reached only by `module_loader_compat.spl` importing it directly. Any consumer
going through the package's public surface therefore gets the fake. This is the
same class as the `smf_mmap_native` Dict fake fixed this session.

### W5. The "82 .spl opens per run" anchor is REFUTED for the traced case

`doc/10_metrics/startup/startup_perf_check_2026-08-17.md` records `src/lib opens: 0`,
`openat 14`. `.claude/rules/commands.md` states 82 opens / 0 `.smf`. Both cannot be
right; the traced evidence wins for that case. Do not quote the 82 figure as
current without re-tracing the specific program.

### W6. Perf contract §20 has never been measured

§20.1-20.5 (cold-aspect startup, hot path, first use, steady state, config) plus
§15 mapping/I-O policy are this lane's, and there is **no measured number for any
of them**. What exists is instrumentation (`packs_opened`,
`modules_decompressed`, `bytes_decompressed`, `cache_hits`) proving the code takes
the cheap path — not that it is fast. aspect_pack is additionally in-memory only
(no mmap/open) with zero production consumers.

### Revised order

1. W2 (bulk write extern) + measure — without it the lane's perf claim is unproven.
2. W3 (`rt_call_ptr_0`) — turns the red positive control green honestly.
3. W4 (stop exporting the fabricating mapper) — a correctness trap for consumers.
4. Then wiring (gap #1 above), then W6 measurement against §20.
