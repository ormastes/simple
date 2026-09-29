# Interpreter: `for` cannot iterate `List<T>` — "cannot iterate over this type"

## Re-verified 2026-09-13 — STILL REPRODUCES (left open)

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

```spl
use std.common.core.collections.List

struct Entry:
    v: i64

fn main():
    var xs = List<Entry>(items: [])
    xs.push(Entry(v: 1))
    xs.push(Entry(v: 2))
    var t = 0
    for e in xs:
        t = t + e.v
    print(t)
```

Tree-walk lane — the reported error verbatim:

```
error: semantic: cannot iterate over this type: Object { class: "List",
fields: {"items": Array([Object { class: "Entry", ... }])} }
```

Seed JIT lane — **worse than reported**: exits 0 and prints `0`. The loop
body never runs and nothing is diagnosed, so `for e in <List<T>>` is a
silent wrong answer on the default `run` lane, not just an error on the
interpreter lane. Any composition path that sums or collects over a `List`
(e.g. `compositor/stacking.spl::flatten_to_paint_order`) therefore produces
an empty result rather than failing loudly.

Fix site located (not applied here — a bootstrap was running and
`src/compiler_rust/**` edits abort it): `iter_to_vec` in
`src/compiler_rust/compiler/src/interpreter_helpers/collections.rs:506-562`
accepts Array / FrozenArray / ByteArray / FixedSizeArray / Tuple / Str /
Generator / Dict / FrozenDict / the builtin Range object, and rejects every
other `Value::Object` — including `List<T>`, whose payload is the plain
`items` array. The JIT lane needs the matching change wherever it lowers
`for`, since it currently degrades to an empty iteration instead.

Date: 2026-07-02
Status: open
Severity: P2
Found by: W6c lane agent (HUD-over-3D composition)

## Symptom

`error: semantic: cannot iterate over this type` for any `for e in list`
where `list: List<T>` in the self-hosted interpreter. `while + .get(i)`
works. Reproduced with a bare `for e in List<DisplayEntry>`.

## Impact

Breaks `surface_layer.composite_order` and
`compositor/stacking.spl::flatten_to_paint_order` (both `for`-iterate
Lists), i.e. the real 2D/3D LayerTree composition path. A stale seed-era
note in `test/01_unit/lib/engine/surface_layer_spec.spl` documents the
same limitation — still broken in the self-hosted binary.

## Related second bug (same lane)

`Scene3DLayer.attach(mut tree, ...)`: class params are pass-by-copy in
the interpreter even with `mut` — the `next_id` advance inside `attach`
is lost and subsequent `tree.create_layer` returns colliding layer ids
(both 0). A `mut` param on a class value silently mutates a copy.

## Workaround

`examples/11_advanced/game3d_hud/main.spl` uses LayerTree only for ids +
`z_paint_order`, and composites via a direct SoftwareBackend blit.
