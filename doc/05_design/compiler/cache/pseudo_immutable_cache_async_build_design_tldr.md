# TLDR: pseudo-immutable cache + async build (2026-10-26)

Full design: `pseudo_immutable_cache_async_build_design.md`. Base `origin/release/1.0.0` @ `9c97b3cdcea`.

- One engine, one cache protocol, one scheduler core; BuildRunner and TestRunner wrap it, never fork it (R01).
- Default op is src → OBJ in ONE process per file; parse/HIR/MIR/objgen are async tasks inside it (R03/R04). Fiber and process invokers share one `CompileInvoker` trait (R05).
- HIR keeps every `@cfg` arm plus optional OS/CPU hints (None = compatible with all); MIR picks the base target. Hazard: `driver_hir_cache.spl:157` key has no target while `parser_preprocessor.spl:388` strips arms per host — closed by S1-7.
- TLDR = forward declaration; cross-module refs are lazy `(module_id, decl_id)` pointers, single-flight, set once, never eager-loaded.
- Cache entries are packed mmap blobs (`.spab` → `.sphb`/`.spmb`), pointers swizzled to offsets/stable ids, read in place; no replay bridge.
- Identity: ≤3 algorithm-tagged digests per key record, one per-algorithm O(1) index, payload stored once; unknown algorithm = miss. 16/32-bit compact ids are handles guarded by bloom + collision side table, never identity.
- Limits: memory max, storage max, max branches, per-branch per-source COUNT and BYTES on memory and disk; daemon ledger enforces.
- Memory: `BuildSession` frees at end (module scope after obj emit), bounded global dataset, refcounted shared data; no GC, so process exit is the RSS ceiling.
- No-change build: valid OBJ/BIN/LIB/SMF ⇒ zero compile, zero link; missing destination ⇒ materialize.
- Plan order (mandated; details `doc/03_plan/compiler/cache/pseudo_immutable_cache_impl_plan.md`): Wave A/B correctness standalone (A-1 HIR key fold, A-2 digest gate, A-3 audit, B-1..3 no-change build) → Step 1 async nodes + async IO (S1-1..S1-6) → Step 2 one compiler interface + runner wrapper + one invoker, with key record + compact ids alongside (S2-1..S2-7) → Step 3 pseudo-immutable storage, ledger, mmap writer, invalidation inputs (S3-1..S3-7) → P-1 target-neutral HIR, P-2 default flip. Guide = high model, Impl = lower model.

```sdn
graph:
  nodes:
    - {id: cli,     label: "Embedded CLI"}
    - {id: runner,  label: "BuildRunner / TestRunner"}
    - {id: sched,   label: "Scheduler core (CompileInvoker: fiber | process)"}
    - {id: task,    label: "CompileTask(file): parse -> HIR -> MIR -> obj (async, 1 process)"}
    - {id: reader,  label: "Reader {file | cache | daemon} single-flight, atomic rename"}
    - {id: store,   label: "Packed blobs .spab/.sphb/.spmb + OBJ/BIN/LIB/SMF, tagged digests"}
  edges:
    - {from: cli,    to: sched}
    - {from: runner, to: sched}
    - {from: sched,  to: task,   label: "admit by est_bytes"}
    - {from: task,   to: reader, label: "read_src / read_tldr (lazy ptr)"}
    - {from: reader, to: store,  label: "mmap in place / publish tmp+rename"}
```
