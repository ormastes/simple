# MC/DC Codegen Auto-Instrumentation (cert C1)

Make Modified Condition/Decision Coverage **measurable on real Simple programs
automatically** — not just via the hand-written `std.mcdc` self-test — and do
it in a way that is **verifiable today** on the frozen deployed compiler
(`bin/release/x86_64-unknown-linux-gnu/simple`).

## Summary of deliverable

A **source-to-source instrumenter** plus a small **auto-instrumentation runtime**
in `std.mcdc`:

1. `scripts/check/cert/mcdc_instrument.spl` — reads a `.spl` file, parses every
   compound boolean decision in an `if` / `elif` / `while` header into an
   operator tree, and rewrites the decision site into a single
   `mcdc_eval(id, [atoms...])` call, prepending the decision registrations and
   appending a per-decision MC/DC report. Emits the instrumented program to
   stdout.
2. New `std.mcdc` runtime: `register_decision_tree`, `mcdc_eval`,
   `mcdc_atom/mcdc_not/mcdc_and/mcdc_or`, `clear_mcdc_trees`. `mcdc_eval`
   replays short-circuit evaluation over the registered tree to derive BOTH the
   decision outcome AND the per-condition `evaluated` (masking) vector, then
   calls the existing `record_evaluation`. This is exactly the recording an
   instrumenter needs to emit — automatically, without hand-written masks.

Chosen over a compiler codegen pass precisely because the instrumenter + lib
runtime run on the frozen binary and are verifiable **now**; a `SIMPLE_COVERAGE`
codegen pass would compile into the binary and be redeploy-frozen (see
"Codegen-pass alternative" below).

## Root cause: why MC/DC was NOT measurable before

Reproduced on `bin/release/x86_64-unknown-linux-gnu/simple`. The `std.mcdc`
analysis existed but did not actually run on real programs, for several reasons:

1. **`analyze_mcdc` / `check_mcdc_coverage` returned nothing (interpreter path).**
   They used `[...].filter(...)` and `.map(...)`. On the frozen binary a plain
   `.spl` run tries JIT, falls back to the **interpreter**, and there
   `Array.filter` returns an empty array and `Array.map` is "not found". So the
   evaluation set filtered to empty → 0% / no decisions matched.
2. **`_find_independence_pair` hung on real data (both paths).** It used
   `continue` inside a range-`for`. The frozen compiler does not advance the loop
   counter on `continue` → infinite loop. This hangs `analyze_mcdc` on any
   non-empty evaluation set — confirmed: on the unmodified library
   `simple test .../mcdc_report_spec.spl` **times out**; with the fix it passes
   in ~190 ms.
3. **`false` in a bool array read back truthy (both paths).**
   `[false, true, true][0]` used directly in `if`/`not` is truthy; only
   `== true` recovers the real value. This corrupts any masking logic built from
   `[bool]` vectors (the auto-instrumentation feeds atom values as `[bool]`).
4. **`{x:.1f}` float formatting printed garbage bits (both paths).** The report
   percentage rendered as e.g. `579592161419329536%`.

These are **frozen-compiler defects**. The fix here works around all of them at
the **library level** (`src/lib/**`, active immediately, verifiable now) so MC/DC
functions today; the underlying compiler fixes are tracked as redeploy-pending
(see below).

## Fix approach

### Library fixes (`src/lib/nogc_sync_mut/mcdc.spl`) — active now

- `analyze_mcdc`: replace `_evaluations.filter(...)` with an explicit `for` loop.
- `_find_independence_pair`: replace `continue` with an inverted
  `if outcome != outcome` guard; replace `.map(_.value)` with `for` loops.
- `check_mcdc_coverage`: replace `_decisions.filter(...)` with a `for` loop.
- `record_evaluation`: normalize array-bool reads with `== true` before storing
  into `ConditionEval`, so every downstream reader sees a correct bool.
- Report rendering (`print_mcdc_report`, `get_mcdc_summary`,
  `format_decision_report`): render an exact integer percentage via
  `_mcdc_pct_int(covered, total)` instead of the broken `:.1f` float format.

### Auto-instrumentation runtime (`src/lib/nogc_sync_mut/mcdc.spl`) — active now

- `struct MCDCNode { kind, atom_index, left, right }` (kind: 0 atom, 1 not,
  2 and, 3 or; root = last node in the array) + constructors
  `mcdc_atom/mcdc_not/mcdc_and/mcdc_or`.
- `register_decision_tree(expr, conditions, operator, file, line, nodes)` —
  registers the decision and stores its tree. Uses **push only** (array element
  assignment `arr[i] = x` does not persist in the compiled path).
- `mcdc_eval(id, atom_values)` — fully traverses the tree with a `reached`
  flag encoding left-to-right short-circuit, collecting the reached atom indices
  into a module list (push only), builds the masking vector, calls
  `record_evaluation`, and returns the outcome. Atom reads normalized via
  `== true`.

Exposed through the tier facade `src/lib/nogc_async_mut/mcdc.spl` (the gc\_\*
facades re-export via `*`).

### Instrumenter (`scripts/check/cert/mcdc_instrument.spl`) — active now

Recursive-descent parser over the boolean subset:

```
decision := or_expr
or_expr  := and_expr ("or"  and_expr)*
and_expr := not_expr ("and" not_expr)*
not_expr := "not" not_expr | primary
primary  := "(" or_expr ")" | ATOM
ATOM     := token run containing no parentheses and none of and/or/not
```

For each block-form header (`if`/`elif`/`while`, trimmed line ends with `:`)
whose condition has ≥ 2 atoms it emits `kw mcdc_eval(id, [atom0, atom1, ...]):`
and a `register_decision_tree(...)` call. Because a `main` function is
auto-invoked by the runtime (loose top-level statements are then ignored), the
instrumenter renames a target `main` to `__user_main` and drives
`__mcdc_init → __user_main → __mcdc_report` from a wrapper `main`; targets
without `main` are bracketed with loose init/report statements. Output goes to
stdout (the runtime's `write_file` is currently non-functional).

Usage:

```bash
simple scripts/check/cert/mcdc_instrument.spl input.spl > input.inst.spl
simple input.inst.spl        # runs program, then prints the MC/DC report
```

### Supported grammar / documented limitations

- Atoms must not contain parentheses (no call expressions like `f(x)` inside a
  decision); the instrumenter leaves such headers unchanged rather than emit a
  broken rewrite.
- Only block-form headers ending in `:` are instrumented (no inline
  `if c: stmt`, no trailing comments on the header line).
- Atoms must be side-effect free (the standard MC/DC assumption): `mcdc_eval`
  evaluates all atom values eagerly at the call site and derives masking from the
  tree, so masking is exact only for pure conditions. Coupled conditions are
  handled via masking MC/DC, identical to the existing `track_mcdc_*` helpers.

## Test plan

- `src/lib/nogc_sync_mut/test/mcdc_auto_instrument_spec.spl` (active) — exercises
  the automatic path (`register_decision_tree` + `mcdc_eval`) for
  `A and (B or C)`: the adequate vector set reaches 100% with A, B, C covered;
  removing the C-independence vector drops to 2/3 and names C uncovered; the
  rendered report names the uncovered condition.
- `scripts/check/cert/sample_and_or.spl` — canonical example input for the
  instrumenter end-to-end check.

## Verified now (on the frozen binary)

- `simple test src/lib/nogc_sync_mut/test/mcdc_auto_instrument_spec.spl` → **3
  examples, 0 failures** (compiled path).
- `simple test src/lib/nogc_sync_mut/test/mcdc_report_spec.spl` → **3 / 0**
  (was **hanging** on the unmodified library — regression proof for the
  `continue` fix).
- End-to-end via the instrumenter (interpreter path):
  - full adequate set → `MC/DC: 100% (3/3) … Covered: a, b, c`
  - drop the `[T,F,T]` vector → `MC/DC: 66% (2/3) … Uncovered: c`
- Instrumenter parses other shapes correctly: `(x or y) and z` and
  `not a or b` produce correct atom lists and operator trees.

## Verify-pending-redeploy (frozen-compiler root fixes)

MC/DC is functional today via the library workarounds above. The **underlying
compiler defects** these work around should be fixed in `src/compiler/**` and
verified after a rebuild/redeploy:

1. `Array.filter` returns empty and `Array.map` is missing in the interpreter
   execution path.
2. `continue` inside a range-`for` does not advance the loop counter (hangs) in
   both interpreter and compiled paths.
3. A `bool` read from an array element is always truthy in an `if`/`not` context
   (both paths); `== true` is the workaround.
4. Array element assignment `arr[i] = x` on a module-level array does not persist
   in the compiled path.
5. `{x:.1f}` float format specifier prints raw bits (both paths).
6. `text.starts_with(...)` returns `nil`; runtime `write_file` returns `false`
   (used to justify the stdout-based instrumenter design).

None of these are required for MC/DC once the library avoids them, but each is a
real correctness bug worth a compiler-side fix.

## Codegen-pass alternative (redeploy-pending, not chosen)

A `SIMPLE_COVERAGE=mcdc` compiler pass would treat each `if`/`while`/ternary HIR
decision node as a decision, walk its boolean sub-tree to enumerate conditions,
and emit `record_evaluation` probes around the lowered short-circuit branches
(the masking vector is available directly from the control-flow graph, with no
eager-evaluation caveat). This is the more general design but compiles **into**
the frozen binary and could not be verified now, so it is deferred; the
source-to-source instrumenter above delivers the same measurement today.
