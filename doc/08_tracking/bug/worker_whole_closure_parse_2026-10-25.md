# HIR shard workers parse the whole closure to build import surfaces

Status: Fixed for HIR shard workers (2026-10-25); MIR shard workers open.

## Symptom (measured)
Every `--hir-shard` / `--mir-shard` / `--file-worker` child re-parsed the
whole closure in phase 2 (1453 files x ~130 ms) only to build ModuleSurfaces
for import resolution. That per-worker cost and RSS is why workers are capped
at 12 and per-file parallelism cannot reach 80.

## Fix (src/compiler/80.driver/driver_worker_surface_closure_v1.spl)
In a HIR shard worker (`SIMPLE_HIR_SHARD` set; file-worker HIR children
included), on the streaming-surface route:
1. Seeds = the worker's static hash slice (`driver_parse_shard_hash`).
2. Closure = seeds + `use`/`export use`/group-member targets resolved by
   `resolve_module_path` (facades followed through their own imports).
3. Closure modules get a real surface parsed from skeleton text: fresh `.tldr`
   v6 `surface` section, else fresh `<root>/tldr/<rel>.surface` sidecar, else
   `module_surface_skeleton_v1` published by temp file + atomic rename. One
   set-once `TldrTableV1` entry per content key (single-flight in-process).
4. Other modules get an empty-text placeholder surface; identity fields come
   from the source, so `hir_cache_closure_digest` (the HIR cache key) and the
   shard inventory are unchanged.
5. After freeze, the worker claims only modules whose resolved
   import/export-route closure is fully built (`worker_surface_ready_v1`,
   checked in `hir_shard_begin`). Anything else stays unclaimed for another
   worker or the parent, so the text closure is a heuristic, never a
   correctness input.
The done line now carries `surfaces_built= surfaces_loaded= skeleton_parses=`.
Default ON; `SIMPLE_HIR_WORKER_SKELETON=0` restores the old whole-closure,
full-source behaviour. Parent build unchanged.

## Not covered
- `--mir-shard` children: they run mono over the whole program's HIR, so a
  closure-only surface set is not sound there yet.
- The retained (non-streaming) route still builds every surface (skeleton
  text in workers, but no closure restriction).

## Evidence
Spec: `test/01_unit/compiler/driver/worker_surface_differential_spec.spl`
(+ `test/unit` mirror). Not run: on this Windows host the seed fails with
`parse: in ...windows_redirected_process.spl: Unexpected token: expected Fn,
found Colon`. No pass is claimed; no worker timing measured yet.
