# ADR-006: Panic-free safe code

Document revision: 3 — final-session consolidation; not a language, ABI, or schema version

**Status:** accepted policy (2026-11-04, user decision); implementation at rollout
phase P1 (warnings). Source: user design doc rev 3, "Simple: Safe-by-Default
Panic Prevention and Semantic Refactoring", sections 1, 3, 4, 5 and 15.
Evidence baseline: `97700b29e10`.

## Policy (verbatim)

> Safe Simple code is panicfree by default within the defined language/runtime guarantee. Potential panic paths produce warnings during migration and errors after enforcement. Programmers do not need `requires` clauses or a separate `no_panic` annotation. The compiler must infer, check, or conservatively reject; it must not silently assume safety.

## Final decisions

| ID | Decision |
|---|---|
| SAF-01 | Safe = memory safe + no language-defined panic on accepted paths, under documented runtime/FFI assumptions. |
| SAF-02 | No user-facing `no_panic`. Internal effect metadata is allowed. |
| SAF-03 | No mandatory `requires`. Safety is inferred from code, types, flow and verified dependencies. Optional contracts stay for documentation and domain rules. |
| SAF-04 | Warn now, error later. The warning phase does **not** confer the guarantee. |
| SAF-05 | Unknown analysis, unknown callee effects, stale evidence or an unsupported backend never count as proof. Strict builds fail closed. |
| ERR-01 | `nil` is the only canonical absence literal of `T?`. There is no competing `none`/`None` absence literal. `notinit<T>` is separate. `Result<T, E>` carries informative errors. No silent optional-to-value conversion. `??` is a lazy fallback; `?` distinguishes optional from `Result` propagation. |
| PERF-01 | Cheap analysis on the ordinary path (no heavyweight solver). Remove a check only when it is proven; keep the minimum check for a fallible op. |
| MIG-01 | Refactoring tools rewrite real source to the new API. No permanent compatibility wrapper or alias layer. |
| MIG-02 | The collection/CUDA lane owns collection implementations. This ADR supplies the contract and migration tooling only. |

## Guarantee boundary

**Covered:** every accepted path of safe code: no language-defined panic, no
trap, no abort from a partial operation, identically in debug and release.

**Outside the guarantee, stated honestly:**

- **`unsafe:` blocks.** `unsafe` transfers *memory-proof* duties to the
  programmer. It does **not** erase a panic effect: a panic site inside
  `unsafe:` is still in the function's effect summary and still reported.
  Autofix never inserts `unsafe`. `@skip_index_range_check` is not a safe-code
  escape hatch.
- **Resource exhaustion:** allocation failure (OOM) and stack overflow abort the
  process. These are explicit aborts, not language panics, and are reported as
  `explicit_abort` / `resource_effects` in the summary.
- **External code:** C/FFI callees and their documented assumptions.
- **Explicit process exit** (`exit(n)`, `abort()` called on purpose) and explicit
  `panic`/`todo`/`unreachable`, which are user-declared aborts. In safe code
  they are reported, never silently assumed unreachable.
- **Not promised:** that code is error-free. Errors are values (`T?`,
  `Result<T, E>`), and the language never converts an error to `nil` or a zero
  fallback for you.

## Non-goals

No error-free promise; no automatic conversion of errors to `nil`; no automatic
zero fallback; no automatic public return-type change; no disabling checks in
release; no catch-and-continue; no renaming a panic as an abort; no rewrite of
the collection lane's APIs; no mutation of live compiler caches through the
editor API.

## Safety model

- A **partial op** is accepted only if proven safe. Proven-bad is rejected.
  Unknown is a warning now and an error after enforcement. Each diagnostic
  suggests a checked API, a guard, or a typed-error refactor.
- A **total checked op** (`get -> T?`, `checked_div -> Result`) is accepted even
  when it always fails, and may be constant-folded.
- A runtime guard that traps is migration-only.
- **SafetySummary per function:** `language_panic`, `explicit_abort`,
  `returned_errors`, `resource_effects`, `obligations`, `dependencies`,
  `evidence` (revision-keyed). It includes implicit calls: drop/defer,
  conversions, allocator, operators, iterators, formatting, hash/eq callbacks,
  closures, task poll, AOP advice. It is computed as a bounded, conservative
  fixed point over call-graph SCCs. An unknown-effect callee is rejected in
  strict mode.
- **Backends** keep the same success/failure semantics: they check before C UB
  (signed overflow, division, shift), emit no unjustified `nsw`/`inbounds`, mask
  SIMD lanes, separate CUDA launch from completion, and have no barrier
  divergence.

### Accepted proofs

The compiler accepts a proof that dominates the site in the same function:

| Proof | Discharges |
|---|---|
| `for i in 0..xs.len()` / `0..<xs.len()` / `range(xs.len())` | `xs[i]` in the loop body |
| `if i < xs.len()` (also as an `and` conjunct, `if`/`elif`/`while`) | `xs[i]` in the block |
| early exit: `if i >= xs.len(): return` / `continue` / `break` | `xs[i]` after it in the same block |
| `if not xs.is_empty()` / `xs.len() > 0` | `xs[0]`, `xs[xs.len() - 1]` |
| a constant index on a known-length array literal or fixed array type | `xs[k]` with `k < N` |
| a non-zero literal divisor (other than `-1` for signed `MIN`) | `a / k`, `a % k` |
| `if d != 0` / `d > 0`, or early `if d == 0: return` | `a / d`, `a % d` |
| `if val v = x`, `x.?`, `x != nil`, `x.is_some()`, or early `if x == nil: return` | the value use, `x.unwrap()` |
| a refinement type (`NonZero`, `Positive`, `Bounded`, `NonEmpty`, `ValidIndex`) | its predicate |

The P1 lint implements every row except the constant-index and refinement
rows, which need type information; until then those sites still warn.

A fact is invalidated by any write to its subject or owner between the proof
and the site (length-changing mutation, reassignment). Facts from a closure or
another task do not flow in.

## Panic-source inventory and handling matrix

Inventory sources are repo-wide, not just a grep for `panic`. Every site gets a
diagnostic family, a span, a cause, an alternative, a status and SSpec IDs. An
unregistered site counts as **unknown**. Today's runtime behaviour is listed
with evidence (file:line on `origin/release/1.0.0`, 2026-11-04).

| # | Source | Today | Rule: inferred safe when | Safe alternative | Code |
|---|---|---|---|---|---|
| 1 | `xs[i]` read | `rt_array_get` returns the nil word (3) out of range (`runtime_native.c:10467`); JIT/native bounds trap | proof table above | `xs.get(i) ?? d`, `if val v = xs.get(i)` | PANIC-W-INDEX |
| 2 | `xs[i] = v` write | `rt_array_write_span_fail_range` exits(1) (`runtime_native.c:10685`) | same | `xs.set(i, v) -> bool` | PANIC-W-INDEX |
| 3 | slice `xs[a..b]` | range-checked | `0 <= a <= b <= xs.len()` proven | `xs.slice_checked(a, b) -> [T]?` | PANIC-W-INDEX (counted with index) |
| 4 | `map[k]` | `rt_dict_get` lookup (`runtime_native.c:12899`) | key inserted on all dominating paths, or `map.contains(k)` guard | `map.get(k) ?? d` | PANIC-W-INDEX |
| 5 | `.unwrap()` / `.expect(m)` | `rt_unwrap_or_trap` prints and `abort()` (`runtime_native.c:20160`) | presence proof | `x ?? d`, `if val v = x`, `?` propagation | PANIC-W-UNWRAP |
| 6 | integer `/`, `%` by zero | unchecked in C runtime (C UB); interpreter error (`10.frontend/core/interpreter/ops.spl:95`) | non-zero literal or guard | `checked_div(a, b) ?? d`, `checked_rem` | PANIC-W-DIV |
| 7 | signed `MIN / -1`, `MIN % -1` | unchecked (C UB) | divisor proven `!= -1` or dividend proven `!= MIN` | `checked_div` | PANIC-W-DIV (P2: dedicated sub-code) |
| 8 | arithmetic overflow `+ - *`, negation, `abs(MIN)` | unchecked in lowering; required by `00.common/assurance/flight_rules.spl:307` | range facts | `checked_*`, `wrapping_*`, `saturating_*` | reserved PANIC-W-OVERFLOW |
| 9 | shift by `>= width` or negative | unchecked | constant or bounded shift count | `checked_shl`, `wrapping_shl` | reserved PANIC-W-SHIFT |
| 10 | text `s[i]` (code point, ADR-005) | runtime index-out-of-bounds abort | same as #1 with `s.len()` | `s.char_at_checked(i) -> char?` | PANIC-W-INDEX |
| 11 | narrowing / float-to-int casts | unchecked | value range proven | `T.try_from(x) -> T?` | reserved PANIC-W-CAST |
| 12 | `assert`, `todo`, `unreachable`, `panic(msg)` | `rt_panic` -> `spl_panic` (`runtime_native.c:18881,18892`) | statically discharged condition | typed `Result` error | reserved PANIC-W-EXPLICIT |
| 13 | `step_by(0)`, `chunks(0)`, `windows(0)`, range step 0 | oversized range abort (`runtime_native.c:10630`) | non-zero literal or guard | reject the literal 0; `Result` for a dynamic 0 | reserved PANIC-W-STEP |
| 14 | `insert`/`remove`/`split_at`/`drain` out of range | per-API | index proof | `-> bool` / `-> T?` forms | PANIC-W-INDEX (P2) |
| 15 | `first`/`last`/`pop`/`min`/`max`/`find` | `rt_array_pop` returns nil word (`runtime_native.c:12192`) | — they become total (`-> T?`) | `?? d`, `if val` | none once total |
| 16 | non-exhaustive `match`, unresolved method dispatch | MIR emits `rt_panic` + `Abort` (`50.mir/_MirLoweringExpr/switch_operators_calls.spl:5233-5322`, `method_calls_literals.spl:2296`); runtime `exit(70)` (`runtime_native.c:4247`) | exhaustiveness and resolution are compile errors | fix the match/type | compile error, not a warning |
| 17 | null `str.*` receiver | `exit(70)` (`runtime_native.c:6865`) | `nil` is rejected outside `unsafe` | `T?` + `if val` | NIL-UNSAFE-001 |
| 18 | text length overflow (concat/pad/replace) | `spl_panic` (`runtime_native.c:4711,6696,7437`) | — | resource effect, outside the guarantee | summary only |
| 19 | contract violations | `abort()` (`runtime_contracts.c:30,45`) | contract proven | — | summary only |
| 20 | `rt_trap_unimplemented` | `abort()` (`runtime_native.c:20131`) | — | unregistered = unknown | summary only |

Compiler-emitted `rt_panic` sites (MIR): `mir_data.spl:1385,1403`,
`text_extern_abi.spl:63`, `global_initializer_guard.spl:61`,
`method_calls_literals.spl:830,1106,1265,1978,2296,5867`,
`builtin_method_extras.spl:106`, `expr_dispatch.spl:4036,4088,6908`,
`result_tuple_payload.spl:353`, `switch_operators_calls.spl:2452,2508,5113`,
`mir_lowering_stmts.spl:4587`. Each one is an inventory row for P0.

## Nil and optional contract (section 5)

- `nil` is the only absence literal of `T?` (ERR-01). Fix-its spell absence
  `nil`, never `None`.
- A total `get(i) -> T?` that always returns `nil` is accepted.
- There is no implicit `T?` to `T` conversion. The ways out are `??` (lazy
  fallback), `if val v = x`, `match`, and `?` propagation.

## Collection-interface consequences

The collection lane implements these (MIG-02); this ADR fixes the contract.

- One `collections` namespace.
- `first`, `last`, `get`, `pop`, `min`, `max`, `find` return `T?` (the nullable
  word: element or `nil`, as `rt_array_first` does today), not `Option<T>`.
- Out-of-range writes (`set`, `insert`, `remove` by index) return `bool` (or
  `T?` for `remove`).
- `get_unchecked` and the panicking forms (`xs[i]` with no proof, `unwrap`) are
  allowed only inside `unsafe:`, and are still reported in the effect summary.
- Migration rewrites call sites to the new API (MIG-01). There are no
  compatibility aliases.

## Diagnostics and fix-its (phase P1, implemented)

Rule `panic_free` in the existing static lint table
(`src/compiler/90.tools/lint/rules/panic_free_rule.spl`, registered in
`static_rules.spl`, level `warn` in `_LintMain/config_and_model.spl`). It reuses
the existing diagnostic path and lint-to-fix routing; each finding's hint
carries the fix-it after `fix-it: `, and the shared fix engine registers these
codes as built-in closures. Fix-its are *not* machine-applicable: they contain a
`<default>` placeholder, because the language never invents a zero fallback.

| Code | Site | Fix-it |
|---|---|---|
| PANIC-W-INDEX | unguarded `xs[i]` / `m[k]` / `xs[a..b]` | `xs.get(i) ?? <default>`, or guard `if i < xs.len():`; writes: `xs.set(i, <value>)` (returns bool) |
| PANIC-W-UNWRAP | `.unwrap()` / `.expect(..)` without presence proof | `x ?? <default>`, or `if val v = x:` |
| PANIC-W-DIV | `/`, `%`, `/=` by a divisor not proven non-zero | `checked_div(<lhs>, d) ?? <default>`, or guard `if d != 0:` |

It is conservative by construction. It reads cheap declared-type hints only
(`x: f64`/`f32` params and locals, float-literal initialisers, `m: Dict<..>`,
`val m = Dict.new()`/`{}`) and skips float division (IEEE, never panics) and
indexing of a declared `Dict` (`rt_dict_get` returns `nil` on a miss: a total
`get`). Everything else with an unknown type still warns; the diagnostic text
says "upper bound". Warnings exit 0, so `scripts/check/lint-cached.shs`
(which caches on exit status) still caches files whose only findings are
`panic_free` warnings. It never assumes safety it has not seen. Spec:
`test/01_unit/compiler/lint/panic_free_rule_spec.spl` (true positives, guarded
negatives, exact fix-it text).

**Migration size (P0 count, 2026-11-04, 12,520 files in `src/lib` + `src/app`; an UPPER BOUND -- the rule reads only cheap declared-type hints, so undeclared float division and dict indexing still count; first pass without hints was 51,571 / 1,581 / 3,481):**

| Code | Sites |
|---|---|
| PANIC-W-INDEX | 49,344 |
| PANIC-W-UNWRAP | 1,581 |
| PANIC-W-DIV | 2,790 |
| **total** | **53,715** (upper bound) |

## Rollout

| Phase | Content | Exit condition |
|---|---|---|
| P0 | Baseline + inventory, no semantic change. Every site classified; unregistered = unknown. | Inventory table above has an owner and SSpec ID per row. |
| P1 | Warning diagnostics with stable codes (this ADR, `panic_free`). | Codes stable; fix-its routed through the shared engine. |
| P2 | Shared tooling (parallel): one semantic query/edit engine for LSP, CLI, MCP; first thin vertical slice (bounds diagnostic -> `get`/guard proposal -> preview -> version-checked apply -> reanalysis). | Slice green on LSP and CLI. |
| P3 | Foundational migration, bottom-up (stdlib first). | `src/lib` has zero `panic_free` warnings outside reviewed `unsafe:`. |
| P4 | Enforced-safe CI lane: strict mode on `src/lib` and `src/compiler`; `simple.sdn` `[lints] panic_free = "deny"` per package. | CI lane green for one release. |
| P5 | Default error. | P4 green **and** language phase 3 (self-hosted stage3) landed. |
| P6 | Maintenance; new partial ops must ship with a code and a proof rule. | — |

**Enforcement flip (P4 -> P5):** after phase 3 lands **and** `src/lib` is
clean (zero `panic_free` warnings), the default level of `panic_free` changes
from `warn` to `deny` in `config_and_model.spl`. Until then a package opts in
early with `simple.sdn` `[lints] panic_free = "deny"` (the existing per-package
lint switch). SDN config: `enforcement: migration-warn | enforce`, analysis
budget, target coverage, reviewed baseline. **A baseline or `allow` entry does
not discharge an obligation**; it only defers the diagnostic.

**Release gate:** a release may claim "safe code is panic-free" only for
packages built in `enforce` mode with no reviewed-baseline entries, on a
supported backend, with current (non-stale) evidence.

## Superseded

- The earlier idea that **`xs[i]` "fails fast"** (out-of-range index is an
  acceptable runtime abort in safe code). An unknown-range `xs[i]` is now
  warn-now / reject-later.
- **ADR-005 item 7** ("`s[i]` outside `-len..len` is a runtime index out of
  bounds error") is superseded *as a safe-code contract*: the runtime check
  stays as a migration-only trap, and the site is PANIC-W-INDEX.
- `doc/07_guide/quick_reference/syntax_quick_reference.md` (`s[99]` row)
  updated accordingly.
