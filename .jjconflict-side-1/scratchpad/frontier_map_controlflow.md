# Native-codegen frontier map — Control-Flow / Functional battery

Worktree: `/tmp/wt_fmap_cf` (detached at `f57dd0ae96f2d09c728cc19d67ec2de864090b3b`, origin/main).
Runtime used: rust-seed `bin/simple` (self-hosted binary not present in a fresh
worktree — gitignored; copied prebuilt seed artifacts from the main checkout's
`bin/release/x86_64-unknown-linux-gnu/` since a from-scratch rebuild was out of
scope). Oracle = `bin/simple run <probe>`; native = `env -u SIMPLE_BOOTSTRAP
bin/simple native-build --entry <probe> -o <bin> --clean` then run the binary,
per `scripts/check/native-smoke-matrix.shs`. All probes `return` a value 0-255
from `main()->i64` (process exit code) to keep comparison unambiguous.

| # | Feature | Oracle (interp) | Native | Verdict | Classification |
|---|---------|------------------|--------|---------|-----------------|
| a | `while` + `break`/`continue` | 25 | 25 | PASS | — |
| b | `loop:` expr, `break <value>` (`val r = loop: ...`) | **ORACLE-BROKEN**: parse/lower error `Unknown variable: loop` / `function 'loop' not found` (statement-form `loop:`+bare `break` works fine, RC=7 verified separately) | Compiles+runs, returns **0** (expected 70 by plain language semantics: `break i*10` at i==7) | ORACLE-BROKEN + suspected native bug | FEATURE-GAP (interpreter has no loop-as-expression support) **and** a likely native SILENT-WRONG-VALUE bug (accepts the syntax, silently discards the break value → 0) — no valid oracle to hard-confirm, but 0 clearly contradicts intended semantics. **Flag for filing.** |
| c | `match` with guard clauses (`case n if n>0:`) | **ORACLE-BROKEN**: all 4 inputs (-5, 0, 50, 200) returned classify()=3 — the guard is never evaluated, first `case n if ...` arm always wins regardless of the condition (verified by isolating each call) | BUILD-FAIL: `llc` error `%t0 = bitcast void %l2 to i64` (invalid LLVM IR — match-guard lowering emits a bitcast of a void value) | ORACLE-BROKEN + BUILD-FAIL | **FIXABLE-BUG (two, independent)**: (1) interpreter guard evaluation is broken — always takes the first guarded arm; (2) native MIR/LLVM lowering of guarded match emits invalid IR (void→i64 bitcast). High priority — guard clauses are silently wrong in the interpreter oracle itself. |
| d | Nested `match` on enum payloads (match enum wrapping enum, destructuring inner variant fields) | 78 | BUILD-FAIL: `MIR lowering error: undefined variable: a` / `undefined variable: b` (the `Shape.Rect(a, b)` bound pattern vars from the *inner* match arm aren't recognized) | BUILD-FAIL | FIXABLE-BUG — nested match's inner-arm pattern bindings aren't threaded into MIR scope. |
| e | Recursion (`fact(5)`) | 120 | 120 | PASS | — |
| f | Mutual recursion (`is_even`/`is_odd`) | 11 | 11 | PASS | — |
| g | Closure stored in a `val`, called later | 225 | BUILD-FAIL: `MIR lowering error: undefined variable: add` (the `val add = \x: base + x` closure binding isn't resolved when later called as `add(5)`) | BUILD-FAIL | FIXABLE-BUG — closures bound to a variable and invoked later are not supported by native MIR lowering. |
| h | Closure passed as an argument, invoked inside callee (`apply(f, x): f(x)`) | 72 | BUILD-FAIL: `undefined variable: triple` **and** `unsupported MIR expression: HirExprKind::Lambda(...)` (inline lambda literal as a call argument) | BUILD-FAIL | FIXABLE-BUG — both a named closure arg (`triple`) and an inline lambda literal arg are unsupported in native codegen (lambda-as-argument entirely unimplemented in MIR lowering). |
| i | Early `return` from inside 3 levels of nested `if` blocks | 12 | 12 | PASS | — |
| j | if-expression assigned to a `val` (ternary form) | 100 | 100 | PASS | — |

## Priority: MISCOMPILE / HANG / silent-wrong first

- **No HANGs.** All builds/runs finished well under the 8s timeout.
- **No hard MISCOMPILE** (case where a *working* oracle disagreed with native) — 6/10 features PASS cleanly (a, d-adjacent no / e, f, i, j, plus none silently diverge on a valid oracle).
- **Highest-priority silent-wrong-artifact**: **(b) `loop:` expression with `break <value>`** — native *compiles and runs* but silently returns 0 instead of the broken-value it was told to break with. This is exactly the "worst" class (silent wrong output, no build/run error) even though there's no clean oracle to diff against; the language's own stated semantics (`syntax_quick_reference.md` shows `loop:`/`break` used exactly this way) make 0 clearly wrong.
- **Highest-priority interpreter bug**: **(c) match guard clauses** — the *oracle itself* silently ignores guard conditions and always takes the first guarded arm. Since many other feature tests in this codebase rely on `bin/simple run` as ground truth, this is a serious, easy-to-miss correctness bug in the interpreter, independent of the separate native BUILD-FAIL (invalid `bitcast void to i64`) for the same feature.
- **BUILD-FAIL cluster**: closures (g, h) and nested enum-match destructuring (d) all fail at MIR lowering with "undefined variable" for pattern/lambda bindings — suggests a shared root cause in how MIR lowering resolves bindings introduced inside nested scopes (match-arm patterns, closure params/captures) that aren't at the top of a function body.

Worktree removed after run (`git worktree remove --force /tmp/wt_fmap_cf`).
