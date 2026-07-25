# Native-Codegen Frontier Map — Numeric / Error-Handling / Stdlib Battery

Worktree: `/tmp/wt_fmap_num` @ 7107f142d75 (origin/main), seed binary copied from main checkout's
`bin/release/x86_64-unknown-linux-gnu/simple` as compiler+oracle. Oracle = `bin/simple run`;
native = `env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry <f> -o <out> --clean` then execute under `timeout 8`.

| # | Feature | Oracle (interp) | Native | Verdict | Class |
|---|---|---|---|---|---|
| a | f64 arithmetic + comparison | rc=0 (correct: 3.5*2.0+1.0=8.0, not >8.0) | rc=0 | **PASS** | — |
| b | int/float mixed + explicit cast | rc=17 (7*2.5=17.5 as i64→17) | rc=17 | **PASS** | — |
| c | int div/mod, negative operands | rc=211 (-7/2=-3, -7%2=-1, exit wraps mod 256) | rc=211 | **PASS** | truncating div confirmed |
| d | u8/i32/u64 fixed-width overflow | rc=4 (wraps correctly: 250+10→4(u8), 2^31-1+1→INT_MIN(i32), u64::MAX+1→0) | **BUILD-FAIL** | **BUILD-FAIL** | **FIXABLE-BUG**: `llc` rejects generated IR — `error: multiple definition of local value named 'l3'` (duplicate SSA value in LLVM backend, same shape as known #131 N-ary-phi dup-SSA class) |
| e | bitwise `& \| ^ << >>` | rc=82 (8+14+6+48+6) | rc=82 | **PASS** | — |
| f | `Result<T,E>` + `?` propagation | rc=6 (**WRONG**, expected 41) | rc=41 (**correct**) | **INTERP-BUG** (native is right, oracle is wrong) | **INTERP-BUG**: any `i64` that is an exact multiple of 8 gets silently divided by 8 when bound out of `Ok(v)` (match or `?`) — reproducible tag-shift-by-3 corruption (16→2, 40→5, 64→8, 96→12, 200→25; non-multiples-of-8 pass through untouched). Matches the known heap-handle `BoxInt<<3` tag-mangling pattern from prior sweeps, but here caught live in the seed's own interpreter (`bin/simple run`), not just native codegen |
| g | `panic("msg")` builtin | rc=1, prints `error: semantic: panic: boom` | **BUILD-FAIL**: `unresolved name: panic` | **BUILD-FAIL** | **FEATURE-GAP**: `panic` builtin resolves in the interpreter but HIR lowering for native-build doesn't know the name |
| h | `defer` ordering (block-form, 2 defers) | prints `body / end-body / defer2 / defer1 / defer2 / defer1` — **each deferred block runs TWICE** | **BUILD-FAIL**: parser rejects `defer:` block form (`unexpected token in expression: ':'`) | **INTERP-BUG + FEATURE-GAP** | Interpreter: genuine **INTERP-BUG**, LIFO-correct order but double-executes every deferred block. Native: **FEATURE-GAP**, block-form `defer:` doesn't even parse (single-line `defer stmt` form DOES build+run correctly natively, rc=1, matching interpreter rc=1 for that form — return value captured before defer mutates, consistent semantics) |
| i | stdlib call `math.sqrt` via `use std.math` | **ORACLE-BROKEN**: `Unknown variable: math` → falls back, then `method sqrt not found on type dict` | **BUILD-FAIL**: `unresolved name: math` | **FEATURE-GAP** (or wrong import form) | Both paths fail identically on this import spelling; inconclusive whether `use std.math` is simply the wrong stdlib path or a genuine gap — flagged, not chased further given time budget |
| j | i64 boundary (near 2^63) | rc=55 (2^63-1 - 1 == 2^63-2 check) | rc=55 | **PASS** | — |

## Highlights or the parent agent

- **INTERP-BUG (f, silent-wrong-value class)**: the interpreter oracle itself is wrong for any `Ok(multiple-of-8)` extracted via `match` or `?` — divides the payload by 8. Native codegen does NOT have this bug (produces the correct 41). This means the seed's `bin/simple run` is unsafe as an oracle for Result-payload values that happen to be multiples of 8; future sweeps should sanity-check oracle output against hand math before trusting it, exactly like this sweep did.
- **INTERP-BUG (h, double-execution)**: block-form `defer:` with two stacked defers runs each deferred block twice in the interpreter (LIFO order is right, count is wrong). This is a distinct bug from (f) and is a correctness bug in its own right, independent of native codegen.
- **BUILD-FAIL / FIXABLE-BUG (d)**: fixed-width overflow arithmetic hits an LLVM backend bug producing invalid IR (duplicate SSA name `l3`), rejected by `llc`. Worth filing — likely the same SSA-dup class already tracked as #131.
- **FEATURE-GAPs (g, h-native, i)**: `panic`, block-form `defer`, and the `math` stdlib import all fail to lower/resolve in the native path even though (for panic/defer) the interpreter recognizes them.

No HANGs or silent MISCOMPILEs (both-produce-plausible-but-different-wrong-values) were found in the native path itself; the one genuine silent-wrong-value case (f) is isolated to the interpreter oracle, with native codegen shown to be correct by cross-check.
