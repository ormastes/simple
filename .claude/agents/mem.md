# Mem Agent - Memory Usage, Growth, and Corruption

**Use when:** RSS is too high or climbing, an OOM/kill, a heap-growth or leak
suspicion, or an object that reads back wrong (corrupt aggregate).
**Related:** `perf.md` (time), `debug.md` (correctness), `build.md`.

## Two different jobs — decide which one you are on first

| Symptom | This is | Go to |
|---|---|---|
| RSS large or climbing, process alive | **usage/growth** | § Growth |
| Field reads back as 0 / garbage, varies run to run | **corruption** | § Corruption |

They have opposite methods. Do not profile allocation to chase a corrupt read,
and do not chase pointers to explain a big-but-correct heap.

## Growth

Sample rather than trust one reading; RSS is meaningless without a trend:

```bash
grep VmRSS /proc/<pid>/status          # NOT ps VSZ
grep -E '^(State|Threads|VmRSS|VmHWM)' /proc/<pid>/status
cat /proc/<pid>/io | head -4           # rchar climbing with flat CPU = IO-bound
free -g                                # is the HOST actually under pressure?
```

The compiler reports its own heap, which beats guessing from RSS:

```bash
SIMPLE_COMPILER_PHASE_PROFILE=1 SIMPLE_COMPILER_PHASE_PROFILE_FILE=/tmp/p.events <cmd>
# rows carry heap_live_bytes, heap_peak_bytes, rss_kib, hwm_kib per phase
```

`heap_live` flat while `rss` climbs is fragmentation or non-heap mappings, not a
leak. `heap_live` climbing monotonically across phases is retention — find what
holds the reference.

Read the phase profile's LAST row before assuming where it stopped: it is
flushed periodically, so a run that died at 42 GB can leave a final row showing
65 MB. That is a stale sample, not evidence the process was small.

Runtime knobs (see `debug.md` for the full table): `SIMPLE_LEAK_DETECTION=1`
(heap-growth heuristic), `SIMPLE_GC_LOG`, and the allocator pins the bootstrap
already sets — `MALLOC_ARENA_MAX=2`, `MALLOC_TRIM_THRESHOLD_=0`. If you change
those for a measurement, say so; they are part of the number.

**Known-large by design, not automatically a bug:** a Stage-3 self-host worker
running `native_build_worker.spl` interpreted has been observed at tens of GB
RSS on a 121 GB host while making steady progress. Establish the host is
actually under pressure before "fixing" it. Existing budget:
`scripts/check/check-bootstrap-stage3-memory-admission.shs`.

## Corruption

A field that reads back wrong is not a memory-usage problem and allocation
profiling will not find it. What has worked in this repo:

- **Establish whether the object is malformed or merely misread.**
  `rt_heap_ref_wellformed(x)` is the header-only formation probe. It returned
  TRUE in 10/10 failing runs of the ZeroKind defect — so a well-formed header
  does NOT mean the fields are right, and that measurement is what redirected
  that investigation.
- **Do not dereference further fields of a suspect object to diagnose it.**
  Tried twice in `function_lowering.spl`; both times the worker died silently
  mid-`eprint`, destroying the diagnostics already gathered. A span that passes
  both `== nil` and `== 0` yet cannot be dereferenced is itself the finding.
- **The nil sentinel is raw 3, so a ZEROED slot passes `== nil`.** Guard with
  BOTH `== nil` and `== 0` (in-repo idiom: `copy_local_hir_type_metadata`,
  `mir_lowering_types.spl`). A stub that returns 3 is indistinguishable from nil
  — that is exactly how a fabricated `bcmp` stub made every string compare
  unequal (fixed 2026-09-04).
- **Non-determinism is a clue, not noise.** A count that varies across runs on
  byte-identical source points at iteration order (dict key order), address
  dependence, or threads — not at a fixed source site. Chase what varies.
- **Wrong offsets look like "the producer forgot to write it".** If one field
  reads 0 and its neighbour reads garbage, suspect a layout/offset disagreement
  before suspecting an unset field. Root cause of the 2026-09 ZeroKind fatal was
  a lowering context missing `current_module_id`, which disabled a self-owner
  filter and let a type's layout be attributed to the wrong module.

Any diagnostic probe added to a hot path must be **default-off** behind an env
gate (`SIMPLE_MIR_TAG_PROBE` is the pattern), staged so the safe line is emitted
before any risky read, and additive — never alter the existing raise.

## Before you conclude

- Re-run. A memory bug that reproduces once is a rumour.
- State the host: total RAM, free at the time, concurrent load.
- Record the binary identity (`readlink -f bin/simple`, `--version`) — same rule
  as `perf.md`.
- Fix in the same change or file a concrete bug; do not move past it silently.
