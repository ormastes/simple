# Per-file unit lane: two class providers that import each other fail to build

- Status: fix-implemented in source (2026-11-21); NOT proven on a rebuilt compiler
- Severity: P1 (default per-file route, any import cycle whose members use each other's classes)
- Found: 2026-11-21, left open by `unit_import_iface_wait_default_dead_2026-11-21.md`
- Component: per-file unit pick (`src/compiler/80.driver/driver_worker_surface_closure_v1.spl`,
  `driver_source_parse_streaming.spl`)
- Binary: admitted Stage 2 built from `0d8a3269bec`

## Repro (3 files, own git repo, frozen Stage 2)

```
# src/cfx/a.spl
use cfx.b.{CfxBox, cfx_b_base}
class CfxTag:
    code: i64
    fn plus_one() -> i64:
        self.code + 1
pub fn cfx_a_value(n: i64) -> i64:
    val box = CfxBox(value: n)
    box.doubled() + cfx_b_base()
pub fn cfx_a_tag() -> CfxTag:
    CfxTag(code: 0)

# src/cfx/b.spl
use cfx.a.{CfxTag, cfx_a_tag}
class CfxBox:
    value: i64
    fn doubled() -> i64:
        self.value * 2
pub fn cfx_b_base() -> i64:
    val tag: CfxTag = cfx_a_tag()
    tag.plus_one() + 1

# src/cfx/main.spl
use cfx.a.{cfx_a_value}
fn main() -> i64:
    cfx_a_value(20)
```

`SIMPLE_UNIT_IMPORT_IFACE_WAIT_MS=60000 simple-bootstrap native-build
src/cfx/main.spl --backend llvm --target x86_64-unknown-linux-gnu
--runtime-bundle core-c-bootstrap --runtime-path <repo>/src/runtime --source src
--entry-closure --threads 2 --mode one-binary`:

```
[unit-tldr] import interface-hir miss reason=no-sidecar path=.../src/cfx/a.spl
unproven-call-origin: MIR call target lacks proven source/runtime/foreign origin:
callee=cfx.a.CfxTag.plus_one fn=cfx.b.cfx_b_base module=cfx.b
```

With `b.spl` constructing `CfxTag(code: 1)` and reading `.code` instead of
calling the method, the same unit fails
`missing class provider metadata for cfx.a.CfxTag`.

## Root cause

A unit holds an import as interface HIR only when the provider's unit already
published its `.hirkey` sidecar (`hir_unit_import_interface_load_v1`,
`driver_hir_cache.spl`). `worker_unit_pick_order_v1` is deps-first, and its own
comment says a cycle has no such order: one member is picked first. That unit
waits the whole budget for a peer no one is running (the pool was serial here:
62 s), then falls back to the TLDR summary surface. A summary surface gives MIR
free-function call origins only
(`register_surface_callable_origins_v1`, `provider_metadata.spl:252`, skips
methods) and no class metadata, so any use of the peer's class fails.
PR #10628 does not cover it: its provider keys come from HELD HIR, and the
peer's HIR is never held.

## Fix

`worker_unit_pick_v1` is unchanged. The unit now calls
`worker_unit_pick_with_cycle_peers_v1`, which runs it and then, under the
ledger lock again, also picks the free import-cycle peers of each picked row
(`worker_unit_cycle_peers_v1`: rows reachable from it that reach it back), so
the cycle is lowered as one unit with every member a target. The unit raises
`SIMPLE_HIR_SHARD_CLAIM_LIMIT` to the pick count so the extra rows can be
claimed. A cycle with more than `WORKER_UNIT_CYCLE_PEER_MAX_V1` (16) peers keeps
the old pick, to bound one unit's memory.

A peer that another worker already claimed or leased makes
`_worker_unit_try_pick_path_v1` return 0. The peer is skipped and the pick is
still correct: every returned path carries this owner's lease and nothing else
does. It is then partial. The unit holds that peer as an import, exactly as
before this change, so the cycle can still fail when the other worker has not
published the peer's sidecar. The lock is released between the base pick and
the peer pick, so two workers can each take one member of a cycle this way.

## Verified

- Frozen Stage 2, same fixture with `SIMPLE_FILE_WORKER_BATCH=2` (which puts
  `a.spl` and `b.spl` in one unit, the shape the fix produces): builds, exit
  code 42. Six variants (field read, construction, both, a printing entry)
  build the same way.
- The pick functions (lease helpers, `worker_unit_pick_v1`,
  `worker_unit_cycle_peers_v1`, `worker_unit_pick_with_cycle_peers_v1`) copied
  verbatim into one file with the real stdlib and compiled by the frozen
  Stage 2 (`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`; the per-file lane of that binary
  cannot build the stdlib closure), run against a real ledger directory: a
  2-cycle picks `b.spl|a.spl`, the next unit picks `c.spl`, a peer with another
  worker's `.claim` leaves `b.spl` alone, empty `edges` picks nothing extra, an
  empty queue is an error.

## Not verified

- The change itself needs a Stage 2 rebuild; it has not run in a compiler.
  The spec case in `worker_unit_pick_spec.spl` was not run (no full CLI here).
- On the frozen Stage 2 a two-module unit sends two objects to the llc pool,
  which always fails there
  (`process_spawn_value_reads_past_counted_text_2026-11-21.md`); 3 of 12 such
  runs then died with unit exit 255 instead of falling back. Fixed in source,
  not re-measured.
- Cycles above the 16-peer bound still fail as before. Cycle sizes in the
  1258-module closure were not measured.
