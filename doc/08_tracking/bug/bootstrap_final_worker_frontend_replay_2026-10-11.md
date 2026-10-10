# Bootstrap final worker repeats frontend work after HIR warming

Status: OPEN. Phase 3 is not qualified.

The 2026-10-11 isolated Phase 3 attempt used pure-Simple producer SHA-256
`e9e8762c79e47d1c0db418d2a8ff5d5eda7b1ef8744ccff32227ae7463926491`,
constructed from source `57d83549f09b374ff9105018896843d4f8ff00e9`.
The frozen SCV revision was
`f78523f6a0a48ba1ee70115be850db76d2c317510d8d61575de75d715ad3992e`.

The command requested 20 workers on CPUs 0–19. All 20 frontend warming
workers finished successfully; their durable ledger contains 1,171 PASS,
zero failures, and zero unfinished modules. The log contains 21 source-loading
starts, including the final serial native-build worker. Warming children each
construct a complete frontend surface before processing their assigned HIR.

The final worker subsequently replayed the parse stage, surface construction,
alias materialization and surface freezing. Forensics confirmed 1,171 parse
cache hits, zero misses and zero parses; the parse stage reused cached ASTs.
The parse/surface/alias/freeze stages together took 96.8 seconds. At the coordinator's 900-second
deadline, the final worker had reached HIR 1,001/1,171 at its own elapsed
585.6 seconds. It had not completed HIR, monomorphization, MIR or object
generation. There were no fatal or poisoned-module receipts in its final
segment. This is a performance limitation, not evidence of semantic failure
or a successful Phase 3 compiler.

The coordinator exited 124 without the requested compiler artifact. Its
serial child, PID 1334127, remained alive after timeout; the root agent verified
the exact worker command and worktree, sent SIGTERM, and recorded cleanup.
Cancellation must also terminate owned workers reliably.

Evidence is retained under
`build/native_probe/final-integrated/`: `phase3.sh`, `phase3.log`,
`phase3-status.txt`, `phase3-terminal-diagnosis.json`, producer and cleanup
receipts. The attempted construction and source identities remain immutable.

Next investigation: determine which warmed frontend artifacts the final worker
actually consumes, and which source/symbol-owner context prevents reuse.
All 1,171 HIR shard claim keys have stored records in the machine-shared HIR
cache, with matching producer and source headers. Astra is testing decoder
rejection separately from key mismatch; matching headers alone do not establish
successful decoding or safe HIR reuse.

The bounded native probe subsequently proved a serializer defect:
`HirCodecWriter.put_i64(v: i64)` compares its unboxed integer with `nil`,
whose native tag is 3. Valid integer 3 therefore serializes as `N`.
The probe's symbol-table scope count 3 becomes `N`; decoding reads zero and
loses frame alignment. `SIMPLE_HIR_CODEC_ROUNDTRIP=1` reports
`ok=false stable=false bytes=1623 reason=decode`, yet the unusable record is
stored. The candidate fix must preserve mandatory integer 3 and explicit
nullable encodings, and invalidate records from the broken codec.

The proposed trailing-empty-split explanation was disproven: the native probe
retains the expected two split items. Do not relax decoder frame validation
to address this writer defect. Native probe elapsed time was 40.60 seconds,
peak RSS 342,300 KiB; compiler HIR itself took 0.26 seconds and runtime linking
took 36.5 seconds. These are baseline observations, not a paired performance
improvement claim.
Any reuse must preserve exact producer/schema/SCV identities, relocation,
declared type owners, and fail-closed admission. Do not force stale cache hits,
substitute warm-worker receipts for final compilation, or call a timeout PASS.

The current construction scope exhausted three bounded attempts; this report
does not authorize another unchanged build or claim an optimization is fixed.

## Decoder diagnosis, isolated 2026-10-11 follow-up

The original log does **not** show cold parsing in the final worker: its
frontend cache summary is `hits=1171 misses=0 parses=0`. It reconstructs the
ParserModule bridge and surfaces; final source loading completes at 3.684s,
surface construction starts at 57.712s, and surface freeze finishes at 96.825s.
The slower HIR phase is separate from that repeated surface work.

All 1,171 claim rows have corresponding HIR files (1,170 distinct keys). Their
headers bind the exact `e9e8762c...` executable and frontend source identity
`812fc9e5d369511bn188`. They reside in the machine cache, not below the supplied
Phase 3 `--cache-dir`: `hir_cache_dir()` honors `SIMPLE_HIR_CACHE_DIR`, otherwise
defaults to the machine cache. New probes explicitly isolated that override.
No existing cache was rewritten, invalidated or promoted.

A single-file native compilation using that exact executable, one CPU and a
120-second deadline produced:

```
HIRROUNDTRIP ok=false stable=false bytes=1623 reason=decode
[hir-cache] hits=0 misses=1 stores=1
```

Compilation exited zero in 40.60s with maximum RSS 342,300 KiB. Its native
artifact executed and printed `split_count=2`. This is a codec failure despite
successful compilation, and disproves the initial trailing-empty-split theory.

Read-only GDB breakpoints on the same producer establish the cause:

- `HirCodecWriter.put_i64(v: i64)` compares its **unboxed** integer parameter
  against the runtime nil tag. At `0x6d01a0`, the instruction is `cmp x1,#3`;
  the branch at `0x6d01a4` selects the `N` encoding.
- Consequently real integer `3` is serialized as `N`. In the saved tiny record,
  the symbol-table dictionary count at body row 148 is `N`, although the writer
  emitted its entries afterward. A symbol ID with value three is also `N`.
- The decoder interprets `N` as zero, loses field alignment, consumes all 522
  split rows, and invokes `reject_malformed("truncated")`. The first reported
  truncation is in `hc_dec_hir_module` while reading AOP presence markers.
- The shard store checks encoding/publication, not a successful decoder round
  trip. Thus a durable `CACHE_STORED` receipt does not prove the final consumer
  can use the record. Decoder rejection remains correct and must not be relaxed.

Evidence is retained in the isolated worktree
`/home/yoon/dev/simple-final-frontend-cache-replay-20261011` under
`build/native_probe/hir-decode/`, including `receipt.json`, the original probe,
build log, and `cursor.log`, `reject.log`, `counts.log`, `nested-counts.log`.
The debugger did not modify the inferior. No broad build was restarted.

A nullable-parameter alternative was explored in a separate tiny native
fixture. Both inferred and explicitly typed receiver variants compiled, but
their artifacts crashed with SIGSEGV. That alternative is **not validated**.
Three scoped native probe builds are complete; further unchanged retries are
not authorized by this diagnosis.

The added `hir_codec_integer_three_spec.spl` calls the actual production writer
and checks exact signed-integer/count/boolean bytes. The fixture
`test/fixtures/hir_codec_integer_three/main.spl` supplies a real HIR round-trip
and executable check for a successor producer. Neither new regression has yet
run with a corrected compiler. Full HIR round trips, second-build cache hits,
maximum RSS and timings, and genuine Phase 3 completion remain required.

## Minimal correction and qualification boundary

`HirCodecWriter.put_i64` now always encodes its declared `i64` value as decimal
text. Its output/allocation/work admission and chunking are unchanged. The
legacy HIR header advances from v6 to v7 so old corrupt records cannot be
admitted. Valid canonical integer grammar and canonical version remain
unchanged; no symbol renumbering, source identity change or relaxed decoder
check is part of this patch. The boolean writer is unchanged.

Caller audit found no direct `put_i64(nil)` or `put_i64(None)` calls in owned
`src/` or executable tests. The generated encoder frames nullable `b_size`,
`b_lo` and `b_hi` with an explicit presence row and calls `put_i64` only inside
the `if val` branch. The generator's `opt` branch enforces the same sequence.
Collection counts, dictionary keys and enum tags are mandatory integer values.

The old comment promising nil for a declared non-nullable integer was an
invalid typing contract. If a lowerer or interpreter supplies nil to an `i64`
field or argument, that is a separate typechecking/representation bug, not an
alternate spelling of integer three. It remains an explicit follow-up to reject
such invalid values before typed native lowering; this change does not claim
that the compiler enforces that contract everywhere. Actual optional fields
retain their existing presence encoding, with new absent/present regressions.

Parent-authorized next step: one changed-source compiler construction, including
the current release struct-layout fixes, followed by these focused regressions,
real HIR round trips and bounded cache reuse measurements. There is no measured
after-fix speedup or memory result yet. All full compiler/lib/MCP checks and
Phase 3 admission remain pending. `STATUS: WARN` (source repair prepared,
native qualification pending), not release PASS.

## Changed-source qualification: decoding repaired, cache stability failed

The first corrected construction at source
`5ecfff3d23a31e2f7a5b3c3d1be752f14c53f7f1` compiled 1,223 modules with zero
failures. Its immutable pure-Simple executable is
`build/native_probe/hir-cache-v7/simple`, SHA-256
`19fcd4ccac312e83cdb4baee72e43398a08b498de98ac9a620c476abc6a49d21`.

The unchanged integer-three fixture compiled and executed with `count=3`, but
its required cache gate failed:

```
HIRROUNDTRIP ok=true stable=false bytes=1879 reason=reencode
[hir-cache] hits=0 misses=1 stores=1
```

The native build took 7.07 seconds with maximum RSS 199,440 KiB. The failed
self-check returned the original HIR; successful execution therefore does not
prove execution from decoded HIR. No warm-cache probe, RISC-V qualification or
new Phase 3 attempt followed this failed gate. These timings use a different
fixture from the earlier baseline and establish no paired speedup.

The exact-head receipt is retained at
`/home/yoon/dev/simple-final-frontend-cache-replay-20261011/build/native_probe/hir-v7-qualification/phase3/19fcd4ccac312e83cdb4baee72e43398a08b498de98ac9a620c476abc6a49d21/integer-three/receipt.json`.

Subsequent offline debugger examination of the retained record found both
frames contain 569 lines and 1,879 bytes. Only the symbol-table dictionary
segment differs: key order `[3,0,1,2]` becomes `[2,3,0,1]`. Every complete symbol
record, including its key, IDs, types and visibility, has an identical hash;
the prefix and suffix are byte-identical. This proves an ordering defect in
this fixture, rather than lost fields. The generated encoder assumes
dictionary keys retain insertion order, whereas the runtime enumerates hash
buckets. Deterministic typed-key serialization and fail-closed cache
publication/admission are the next correction; accepting unstable frames is
not a remedy.

Release head `74a3eebe81958143aebc14cb525c4e328922a128` adds three plan documents
through PR #2871. The isolated integration branch rebased cleanly onto it.
Compiler sources remain identical to the preceding release snapshot, and the
producer receipt above remains bound to its original source head.

**STATUS: FAIL** for cache qualification. Phase 3 remains incomplete: the last
full attempt ended before MIR/object generation and produced no compiler.
