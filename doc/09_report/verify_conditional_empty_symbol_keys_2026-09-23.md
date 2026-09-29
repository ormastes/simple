# Conditional empty-array symbol keys: isolated seed regression

STATUS: PASS for the scoped Rust bootstrap-seed fix. No full bootstrap,
release, candidate promotion, or self-hosted compiler acceptance is claimed.

## Fault and correction

The Rust seed took an ordinary conditional expression's type from its then
branch. In `if empty: [] else: symbols.keys()`, the default `[i32]` type of
`[]` therefore reached the loop variable even when the selected branch held
`SymbolId` struct keys. The resulting integer narrowing could truncate a
pointer passed to `hc_enc_symbol_id`.

The correction contextualizes only syntactic `Expr::Array([])` from an array
sibling, in either branch order. Both branches retain the sibling element
type, the empty branch retains size zero, and the conditional has unknown
size. Populated arrays, unrelated tuples, and typed zero-repeat arrays are
not silently reinterpreted. Independent review caught and resolved an initial
HIR-only predicate that also matched typed zero-repeat arrays.

If-val expressions, strict empty-collection rejection, and recursive
contextual inference remain outside this narrow fix.

## Retained verification

Evidence root: `/Users/ormastes/simple-tmp/hir-symbol-codec-pointer-20260923/build/native_probe`.

| Check | Evidence | Result |
| --- | --- | --- |
| Baseline native fixture | `red-executable/run.status`, `run.log`, `run.rss.env` | Exit 139 |
| Final HIR tests | `tests-final.log`, `tests-final.status`, `tests-final.rss.env` | 2 passed; exit 0 |
| Final private seed build | `seed-final.log`, `seed-final.status`, `seed-final.rss.env` | Exit 0 |
| Patched native fixture build | `green-final/build.log`, `build.rss.env` | 1 compiled, 0 cached, 0 failed; exit 0 |
| Patched native fixture execution | `green-final/run.log`, `run.status`, `run.rss.env` | Exit 0; `conditional-empty-symbol-keys: PASS cases=4` |

The HIR tests cover both empty-array branch orders, inferred loop-variable and
branch element types, unknown conditional length, incompatible populated
arrays, unrelated tuples, both branches empty, preserving a typed zero-repeat
array, and contextualizing `[]` from a typed zero-repeat sibling. The native
fixture checks both branches of both orders using a struct field above 32 bits.

The final Rust tests and private seed build completed before recovery and were
not rerun. Recovery performed only the pending final native build and execution
via `sh build/native_probe/run-native.sh green-final <private-seed>`.
That wrapper sets `SIMPLE_NO_STUB_FALLBACK=1`, uses Cranelift and
`core-c-bootstrap`, a private output/cache directory, and bounded resource
monitoring. The checked-in native execution helper also passed shell syntax
validation; this recovery run used the retained wrapper, not that helper.

All four final resource receipts report complete status, exit 0,
`quiescent=1`, enforced RSS cap 5,859,375 KiB, verified session helper,
zero observer errors, and no unexpected session PIDs. Observed process-tree
RSS peaks were 3,515,888 KiB for tests, 2,653,376 KiB for the seed build,
186,992 KiB for native fixture compilation, and 2,384 KiB for execution.
These are observed enforced-cap results, not a kernel hard memory limit
(`hard_memory_limit=0`). Native build/execution timeouts were 180/60 seconds.

## Final artifact binding

SHA-256 values measured after the final seed build completed:

| Artifact | SHA-256 |
| --- | --- |
| `src/compiler_rust/compiler/src/hir/lower/expr/control.rs` | `5d2d8cddec49fe2c499f300e1f0c6db7575f80baed980ca9c4465409fe9869d3` |
| `test/fixtures/native/conditional_empty_symbol_keys.spl` | `c838d88f51211b6ba8ead026c3a3a401133928b205e3b99a741f807d7885def1` |
| Private `rust-target/aarch64-apple-darwin/bootstrap/simple` | `3569b415fdf87a10b191af41deff8a6525aada442e2b99864625ad944472725f` |
| `green-final/fixture` | `960b4af64bf5c35738ff0028035101b14c64d41b4b89a0b3e4282388f9e066bf` |

The earlier `producer-artifacts.sha256` seed entry predates this final binding
and must not identify the final seed. Baseline executable digest recorded there
is `e704737697df50f010d1b2f47a787e24ce6ba410abb3422c8374e43fcd19426b`.

Independent code review is PASS after the AST predicate correction. The
working-tree direct-env guard passed before recovery; executable spec count
under `doc/06_spec` is zero. This change introduces no public language feature,
runtime facade dependency, packaging change, or SPipe manual change.
