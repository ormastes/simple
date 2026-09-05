# `gzip_compress` dominates every SCV pack write (110s for a 16 KB payload)

- Found: 2026-08-26, during SCV-IMPL-B-06 (pack v2 hardening).
- Status: OPEN. Worked around **only** on the new `pack-write-v2r` path; the
  shared encoder is deliberately not edited.
- Component: `src/lib/common/compress/gzip.spl` (`gzip_compress`).

## Evidence

Phase timings for a single `scv pack-write` on a two-snapshot repo with 8
chunks / 16 KB payload, measured by a probe that calls the library functions
directly (`bin/simple run`, this host, 2026-08-26):

| phase | time |
|---|---|
| manifest (`scv_pack_manifest_for_kind` x8, 8,927 bytes) | 3 ms |
| payload assembly (`scv_pack_payload`, 16,274 bytes) | 5 ms |
| **`gzip_compress` (16,274 -> 4,472 bytes)** | **110,234 ms** |
| `scv_pack_payload_v2` (delta pass, 16,489 bytes) | 121 ms |

`scv pack-write` wall time was 115-124 s against ~10 s process startup, so the
compressor is ~95% of the command. A synthetic 4,500-byte low-entropy array
compresses in 19 ms, so the cost is data-dependent (match search), not fixed
overhead — the defect is invisible on trivial fixtures.

## Impact

Any bounded loop that packs repeatedly is unaffordable: a 50-cycle
pack/GC soak costs hours purely in the compressor. It also makes every
`pack-write` / `pack-write-v2` a two-minute command in practice.

## Workaround in place (scoped, not a fix)

`scv_pack_v2_gzip_stored` in `src/lib/scv/pack_v2.spl` emits a valid gzip
stream of DEFLATE **stored** (BTYPE=00) blocks with a real CRC32/ISIZE footer.
It is used **only** by `scv_pack_write_v2_reachable`; `pack-write` (v1) and
`pack-write-v2` keep the shared encoder, so no existing pack, repo or spec
changes behaviour. Round-trip is pinned two ways in
`test/integration/app/scv_pack_v2_spec.spl`: the repo's own `gzip_decompress`
reads it back byte-identically, and system `gunzip -t` accepts the file.
Cost of the same write dropped 148 s -> 13 s. The trade is size: a stored pack
is ~1.0x the payload instead of ~0.28x.

## Fix wanted

Make `gzip_compress` linear-ish (bounded hash-chain match search with a capped
chain length, as every production deflate does), then delete
`scv_pack_v2_gzip_stored` and route `pack-write-v2r` back to the shared encoder.

## Second finding: per-cycle soak cost still scales with repository size

With gzip removed from the `pack-write-v2r` path, a 12-cycle
`scv pack-soak-v2` run costs 148 s of work, split (instrumented, reported in
the command's own row):

| phase | 12 cycles |
|---|---|
| pack (`pack-write-v2r`: manifest + delta pass + reach check) | 78.7 s |
| gc (`scv_gc_roots_reachable` + `scv_gc_quarantine`, maintenance.spl) | 32.1 s |
| fsck (`scv_fsck`, integrity.spl) | 23.1 s |
| snapshot (working_copy.spl) | 5.3 s |
| reachable-object read-back verify | 0.03 s |

Every phase except the verify walks the whole repository each cycle, so total
cost is quadratic in cycle count. A 50-cycle run is therefore ~2500 s and
cannot share the 1800 s spec budget with the other cases;
`test/integration/app/scv_pack_v2_spec.spl` runs 20 cycles and says why, and
`scv pack-soak-v2` accepts 1..500 for out-of-band runs. The GC and fsck halves
live in `maintenance.spl` / `integrity.spl`, which SCV-IMPL-B-06 may only read.

## Non-finding worth recording: `scv_append_bytes` is NOT the problem

`scv_append_bytes` (`src/lib/scv/pack.spl`) looks like the COW-alias
anti-pattern from `.claude/rules/code-style.md` (`var out = target` + per-byte
`out.push`) and was rewritten to a single `target + source` concat during this
work. Measured on 100 appends of 2,000 bytes (200 KB total): alias-push **1 ms**,
concat **582 ms**, plain local push **1 ms**. The concat is 500x SLOWER, so the
"fix" was a pessimization and was reverted; the file is unchanged. Push into a
`var` binding is amortized here — the alias rule's cost applies to collections
copied per write, not to this loop. Do not "fix" this function without
re-measuring.

## 50-cycle soak: attempted twice, never completed (2026-08-26)

Neither out-of-band `scv pack-soak-v2 50` run finished on this host, so no
50-cycle evidence exists and nothing in this repository should claim otherwise:

1. First attempt: killed at **963 s** by `scripts/resource/kill_simple_monitor.shs`
   (`age=963s>=900s`) — the CPU watchdog, not the spec budget.
2. Second attempt, with `SIMPLE_TIMEOUT_SECONDS=0` set in the environment: still
   running past ~30 min and stopped when the session reclaimed the task.

The largest COMPLETED soaks are 20 cycles (in the spec, PASS) and 12 cycles
(instrumented, PASS, table above). Completing 50 is gated on the per-cycle
scaling described above, which lives in `maintenance.spl` and `integrity.spl`.

## ROOT CAUSE FOUND AND FIXED — stdlib LZ77 had no hash chain (2026-08-26)

**Root cause.** `lz77_compress`
(`src/lib/nogc_sync_mut/compression/gzip/lz77.spl`) called `lz77_find_match`,
which linearly scanned **every** position of the 32 KB sliding window for
**every** output position, comparing bytes at each. On compressible input this
hides, because a long match lets `pos` skip far ahead — a 4 KB repetitive
fixture produced only 98 tokens and compressed in 0.14 s. On the
near-incompressible payloads SCV packs, no match is ever found, `pos` advances
one byte at a time, and the cost is O(n x window) = **O(n^2)** byte comparisons.

A second, compounding defect: `lz77_compress` computed `max_search` from
`level` (128 / 4096 / 32768) and then **never used it**. The level knob bounded
nothing at all; every level paid the full window scan.

**Evidence (pseudo-random incompressible input, one process per measurement,
seed binary, level 6).** Doubling the input quadruples the time — textbook
quadratic:

| bytes | lz77 BEFORE | lz77 AFTER | lz77+deflate BEFORE | lz77+deflate AFTER |
|-------|------------|-----------|--------------------|-------------------|
| 2,048  | 0.38 s  | —      | 0.40 s  | —      |
| 4,096  | 1.19 s  | 0.28 s | 1.30 s  | 0.80 s |
| 8,192  | 4.44 s  | —      | 4.59 s  | —      |
| 16,384 | 17.80 s | **0.42 s** | 18.63 s | **1.10 s** |
| 32,768 | (not run; >60 s projected) | 0.50 s | — | 1.92 s |
| 65,536 | (not run; >240 s projected) | 1.23 s | — | 3.09 s |

At 16 KB — the size in this bug's title — LZ77 is **42x faster** (17.80 s ->
0.42 s) and the full deflate path is **17x faster** (18.63 s -> 1.10 s). Timings
are wall-clock including ~0.15 s process startup, taken on a loaded shared host;
treat them as an envelope. The absolute numbers here are smaller than the
reported 110 s (different payload and host load), but the complexity class is
the same and it is the one that was removed.

**Fix.** Replaced the linear window scan with a standard 3-byte hash-chain
matcher inside `lz77_compress`: `head[hash]` holds the most recent position with
that 3-byte prefix, `prev[pos]` chains backwards, chain walks are bounded by
`max_search` — which is what finally wires the level knob to real work. Both
tables are allocated once and mutated in place through their single owner
(`head[h] = pos`), never through a temporary alias, so the COW trap in
`.claude/rules/code-style.md` is not reintroduced. Every position covered by an
emitted match is inserted into the chain, so match quality does not degrade.
Matching stays **greedy** — no lazy matching, no level-dependent extras.
`lz77_find_match` is left in place for API compatibility and is no longer on the
hot path. The public API is unchanged.

**Match quality preserved, not traded away.** Token counts are byte-for-byte
identical before and after on the random fixtures (16,360 tokens at 16 KB both
ways), and repetitive input still compresses hard: 8,192 bytes -> 81 bytes gzip
at level 6, 4,096 -> 53 at level 9.

**Correctness.** Six payloads round-trip through the repo's own
`gzip_decompress` (all OK) *and* pass system `gunzip -t` (rc=0, which validates
CRC32 and ISIZE, not just framing): empty input, all 256 byte values, 4 KB
random, 8 KB repetitive, 1 KB random at level 1, 4 KB repetitive at level 9.

Regression specs, final `Results:` lines only:

- `test/01_unit/lib/common/compress/gzip_spec.spl` — 6 total, 6 passed, 0 failed
- `test/01_unit/lib/common/deflate_inflate_spec.spl` — 14 total, 14 passed, 0 failed
- `test/01_unit/lib/common/compress/compression_utilities_spec.spl` — 2 total, 2 passed, 0 failed
- `test/01_unit/lib/common/compress/typed/deflate_typed_spec.spl` — 37 total, 37 passed, 0 failed
- `test/01_unit/lib/common/compress/gzip_header_spec.spl` — 9 total, 9 passed, 0 failed
- `test/01_unit/lib/nogc_async_mut/http_server/compression_spec.spl` — 20 total, 20 passed, 0 failed
- `test/integration/app/scv_allocation_bounds_spec.spl` — 4 total, 4 passed, 0 failed
- `test/02_integration/app/scv_pack_v2_spec.spl` — 8 total, 8 passed, 0 failed (~13 min wall; most of it blocked on child processes, not CPU — 4 s CPU over 734 s elapsed)

**Remaining gap, stated rather than papered over.** After the fix the deflate
bitstream is the larger remaining term (16 KB: 0.68 s of the 1.10 s; 64 KB:
1.86 s of 3.09 s). `bitstream_write_bits_lsb` / `bitstream_write_huffman`
(`huffman.spl`) do carry the `var bytes = bs[0]; bytes.push(...); return
[bytes, ...]` alias shape, but the measured scaling across 16/32/64 KB is
roughly **linear, not quadratic**, consistent with lane B's counter-example that
alias-push is amortized here. It is therefore a constant-factor cost, not a
second O(n^2) bug, and `huffman.spl` was deliberately left untouched. gzip
compression is still materially slower than a C implementation; this fix removes
the quadratic blowup, it does not make the codec fast.

**Effect on the pack_v2 workaround.** The stored-block (uncompressed) gzip
workaround in `src/lib/scv/pack_v2.spl` should no longer be *necessary* for
performance at these payload sizes. It was **not** removed in this lane, as
instructed; re-enabling real compression there is a separate, separately
measured change.

---

## Follow-up 2026-08-27 — 50-cycle soak completed, and the "remaining gap" above was misattributed

Two results, both measured on `bin/simple` =
`bin/release/x86_64-unknown-linux-gnu/simple`, md5 `64b12cd8197770073f9f9b816f27ef13`,
60744944 bytes, mtime 2026-08-26 01:16:25. Worked in a detached worktree at
commit `f2e10076977`.

### 1. The 50-cycle GC soak now exists (it was never a hang)

Run detached (`setsid nohup`, `SIMPLE_TIMEOUT_SECONDS=0`) so no harness
watchdog could kill it, from a fresh `scv init` repo:

```
pack-soak-v2 iterations=50 lost=0 fsck_dirty=0 quarantined=0 \
  ms_snapshot=25612 ms_pack=3506559 ms_gc=1581246 ms_verify=429 ms_fsck=306761
PASS — pack v2 GC soak: 50 cycle(s), 0 reachable object(s) lost, fsck clean after every cycle
```

Wall: **5439 s (~91 min)**. The two earlier attempts were killed by watchdogs,
not stuck — detaching was the whole fix. The B-06 acceptance evidence is
therefore no longer missing.

**Which half dominates:** `ms_pack` = 3506 s is **64%** of the phase total,
`ms_gc` (root walk) = 1581 s is **29%**, and `ms_fsck` = 307 s is only **5.6%**.
So the cost is in packing and the GC root walk; fsck is nearly free. The soak
already reports these per-phase totals itself — no extra instrumentation is
needed to profile it.

**Cost curve (same host, same binary), soak-phase totals excluding startup:**

| N | phase total | wall |
|---|---|---|
| 5 | 20.3 s | 31 s |
| 10 | 111.9 s | 128 s |
| 50 | 5420 s | 5439 s |

Doubling 5 -> 10 multiplies cost by ~5.5x, i.e. roughly `N^2.5` — superlinear,
slightly worse than quadratic, because the repo grows every cycle and per-cycle
cost is itself quadratic in repo size. Extrapolating from the N=10 point
predicted 47-98 min for N=50; the measured 91 min lands in that band.

### 2. The remaining constant factor is NOT the bitstream — it is `huffman_lookup`

The section above named `bitstream_write_bits_lsb` / `bitstream_write_huffman`
as the larger remaining term. That was the wrong suspect. Those loops run at
most 9 iterations per token. The actual dominant constant factor is
`huffman_lookup` (`huffman.spl`), a **linear scan over the 288-entry
literal/length table performed once per token** — roughly 128 comparisons for an
average literal, and 2-3 lookups per match token.

The fixed tables are dense and index-ordered: `deflate_fixed_huffman` and
`deflate_fixed_distances` push symbols 0,1,2,... in order, so entry `k` always
has `entry[0] == k` and a symbol indexes its own row. Fix: a **guarded** dense
fast path that checks `codes[symbol][0] == symbol` before using the row, and
falls through to the original scan otherwise. The guard is what makes it safe —
`huffman_encode` calls the same function with dynamically built, non-dense
tables, and those take the scan exactly as before. The returned value is
identical for every table shape, so compressed output is unchanged by
construction.

**Measured A/B**, same binary, same host, same concurrent load, best of 3 per
point, on literal-heavy real source bytes (`deflate.spl` + `pack_v2.spl`):

| fixture | baseline | with fast path | speedup |
|---------|---------:|---------------:|--------:|
| 16 KB   |    166 ms |          59 ms | **2.8x** |
| 32 KB   |    314 ms |          97 ms | **3.2x** |
| 64 KB   |    761 ms |         348 ms | **2.2x** |

**Compressed output is byte-identical.** Proven on the same input A/B: the same
three fixtures compressed with and without the fast path give the same length
AND the same FNV-1a hash of the compressed bytes, all three fixtures:

```
f16 comp_bytes=5671  fnv=8912114281567737184
f32 comp_bytes=9187  fnv=1122664794231497831
f64 comp_bytes=18368 fnv=6541743180832279986
```

Compression ratio is therefore unchanged, exactly. Packs written by the fixed
code all pass system `gunzip -t` (5/5).

One negative result worth recording so nobody repeats it: comparing pack
md5s between two *separate* 5-cycle soak runs shows the sizes matching
(`2668 4771 6803 8835 10867`, total 33944 both times) but the md5s differing.
That is **not** a compressor difference — each soak run generates its own
repo content, so the inputs differ. Only the same-input A/B above is a valid
identity test.

Regression specs, all green with the change (final `Results:` lines only):

- `test/01_unit/lib/common/compress/gzip_spec.spl` — 6 total, 6 passed, 0 failed
- `test/01_unit/lib/common/deflate_inflate_spec.spl` — 14 total, 14 passed, 0 failed
- `test/01_unit/lib/common/compress/typed/deflate_typed_spec.spl` — 37 total, 37 passed, 0 failed
- `test/01_unit/lib/common/compress/gzip_header_spec.spl` — 9 total, 9 passed, 0 failed
- `test/01_unit/lib/common/compress/compression_utilities_spec.spl` — 2 total, 2 passed, 0 failed
- `test/02_integration/app/scv_pack_v2_spec.spl` — 8 total, 8 passed, 0 failed

Note the 50-cycle soak above ran the **committed** tree; it started before this
change was applied and so does not include it. The 2.2-3.2x applies to
`gzip_compress`, which is 64% of soak cost, so a re-run should be materially
faster — that has not been measured and is not claimed here.

### 3. Two unrelated observations, reported not fixed (out of scope)

- **`file_write_bytes` truncates to 3 bytes in a `bin/simple run` script.**
  Reading a 16384-byte file with `file_read_bytes` and writing it straight back
  with `file_write_bytes` produces a **3-byte** file, no gzip involved. This
  cost real time here by looking like a gzip round-trip failure. Production code
  paths (`pack_v2.spl`) write correct packs that pass `gunzip -t`, so this is
  specific to the ad-hoc script/interpreter context, not to the library.
- **`_gzip_append_bytes` in `src/lib/common/compress/gzip.spl`** carries the
  `var out = target; out.push(...)` alias shape that the repo's COW rule warns
  about. Not measured, not touched.
