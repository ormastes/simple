# BUG: a nested `fn` declared inside a LAMBDA body does not capture the lambda's locals — spec `it` blocks are just the common case

**Status: FIXED (2026-09-19), in two parts.** Part 1, in the Rust seed's call
dispatch, fixes the capture defect itself and is DEPLOYED — `bin/simple` on this
host carries it. Part 2, in HIR lowering plus the AOT compilability gate, stops
the JIT dropping the whole module and lets the AOT lane accept the shape; it is
in source and **not yet deployed**. See "Fix" and "Fix 2 (JIT lowering)" below.

## Fix 2026-09-19

### What was actually wrong — a correction to yesterday's localisation

Yesterday's note concluded, from the probe where a nested `fn` inside a lambda
still read a module-level `var` correctly, that the `fn` was "lowered as a free,
top-level function". **That inference was wrong, and the probe could not have
decided it**: the closure's captured environment chains to module scope too, so
both the broken path and the correct one answer that probe identically. It
discriminated nothing.

The real mechanism is dispatch order in the interpreter, and it is one function
being registered in two places.

`exec_block_closure_into` (`interpreter_call/block_execution.rs`) registers a
nested `fn` **twice**:

- into the flat `functions` map, so the body can recurse;
- into the block scope as a `Value::Function` whose `captured_env` is the block's
  environment — the registration that carries `inner_local`.

`evaluate_call` (`interpreter_call/mod.rs`) then consulted the flat map at
Priority 5 and the environment only at Priority 6. The flat entry always won, and
it runs the body against the **caller's** environment, so the capture was thrown
away and the block's own `val`s were simply absent.

That also explains, without any extra theory, why a `fn` nested in a plain
function body always worked: that path (`interpreter/node_exec.rs`) binds **only**
the environment and never touches the flat map, so Priority 6 handled it.

### The change

Two edits, both in `interpreter_call/mod.rs`, 54 lines with the reasoning:

1. **Priority 4.9**, ahead of the flat-map lookup: if the environment binds this
   name to a `Value::Function` whose `def` is the *same `Arc<FunctionDef>`* as the
   flat entry, they are by construction the two registrations of one nested
   definition, and the closure is the one carrying scope — so dispatch through it.
   Identity is established by pointer rather than by testing whether the captured
   environment "looks" non-empty: `CowEnv` is a copy-on-write overlay over a
   shared base, so an emptiness test says nothing about what a closure can see.
2. **letrec self-binding** where a `Value::Function` is invoked: `captured_env` was
   cloned *before* the closure was inserted into the block scope, so a nested `fn`
   cannot see itself. That was invisible while the flat map answered every call;
   with the closure now winning, a recursive nested `fn` would have failed with
   `variable <name> not found`. The function is bound under its own name only when
   the captured scope does not already define it, so an outer binding still wins.

Without the second edit the first is a trade, not a fix.

### Evidence

`test/01_unit/interpreter/nested_fn_in_lambda_capture_spec.spl` (added here),
run through the spec runner on both binaries:

| binary | result |
|---|---|
| deployed `bin/simple` (2026-09-18 seed) | **3 passed, 4 failed** — `semantic: variable n / buf / base / shadowed not found` |
| seed rebuilt with this change | **7 passed, 0 failed** |

The three examples that pass on the broken binary are kept as controls on
purpose: they are the module-var, callback and thunk shapes, all of which
already worked. A probe of only those reports green on a broken binary, which is
exactly how this survived six weeks — the original repro used the callback shape.

Recursion is covered (`fact(4)` reading the enclosing `base`, answering 240), so
the letrec edit is pinned rather than assumed.

### Regression checking

- **Seed unit tests**: `cargo test --release -p simple-compiler` gives
  `4094 passed; 19 failed` **both with and without** the change, and the two
  failure name-lists are byte-identical. The 19 are pre-existing (vulkan externs,
  stage4/native_project, linker, one MIR lowering test) and untouched by this.
  Verified by running the suite twice rather than asserted.
- **Spec suites**: 12 spec files that declare `fn`s inside `it` blocks, 219
  examples, run on the old and new binaries. Every file reports an identical
  pass/fail count. This matters more than the number suggests — 266 spec files in
  `test/01_unit` use this shape, so a dispatch-precedence change has a wide blast
  radius.

### A second defect the letrec edit repairs — on one route only

A **recursive** nested `fn` inside a PLAIN function body (no lambda anywhere)
was wholly broken, and not with a capture error:

```simple
fn outer() -> i64:
    val base = 10
    fn fact(n: i64) -> i64:
        if n <= 1:
            return base
        n * fact(n - 1)
    fact(4)
```

| route | deployed seed | rebuilt seed |
|---|---|---|
| `bin/simple run` | **`error[E1002]: function `fact` not found`** | **240, correct** |
| spec runner (`test`) | `semantic: variable `base` not found` | `semantic: variable `base` not found` |

On the `run` route this is a clean repair, and it comes from the letrec half
of the change rather than the dispatch half: the plain-fn path binds only the
environment, so the closure was the only registration and it could not see
itself. Nothing in this record predicted it; it turned up because the shape was
probed on both binaries rather than assumed to be covered.

Through the **spec runner** the same code still fails, identically on both
binaries. So the spec runner reaches a module-level function body by a path
this change does not touch, and that path loses the enclosing `val` for a
recursive nested `fn`. That is a remaining member of this family, measured but
not diagnosed. The spec deliberately does not assert this example — asserting
it would add a red, and dropping it silently would hide a real finding, so it
is recorded here instead.

> **Correction, re-measured 2026-09-19 after deployment: the paragraph above is
> wrong and this item is CLOSED.** The spec-runner route was repaired by the
> very same change. The "both binaries" claim could not have held — it was
> measured against the pre-deployment binary on both sides, and the rebuilt
> column for this row was never actually re-run.
>
> Re-measured against three binaries, including the rollback copy kept at
> `bin/release/aarch64-unknown-linux-gnu/simple.stale-2026-09-19`, which is
> exactly the pre-fix artifact:
>
> | shape, through `simple test` | pre-fix rollback binary | deployed (fixed) | seed with the lowering fix |
> |---|---|---|---|
> | recursive nested `fn` at module scope reading an enclosing `val` | FAIL — ``semantic: function `fact` not found`` | **PASS** | **PASS** |
> | recursive nested `fn` declared inside the `it` block | FAIL — ``semantic: variable `base` not found`` | **PASS** | **PASS** |
>
> Both shapes also answer 240 through `run`, on both lanes. The two distinct
> pre-fix error messages are worth keeping: the module-scope shape lost the
> *function* and the in-`it` shape lost the *variable*, which is why the
> original investigation read them as two different defects. They were one.
>
> **But the original observation was not imaginary, and chasing it found a new
> defect.** Reproducing it inside *this file* still fails — because this file
> already declares a nested `fn fact` inside an `it` block, and a second nested
> `fn fact` in another scope **collides with it**. The flat `functions` map is
> keyed by the bare name, so the second call resolves to the first one's
> closure, whose scope is gone by then. Renaming one of them, changing nothing
> else, makes both pass. That is filed as
> `nested_fn_name_collision_across_scopes_2026-09-19` — a loud error, never a
> silent wrong answer (probed specifically), and the same first-wins-on-a-bare-
> name class that made hoisting the wrong choice for the JIT fix.
>
> So the honest summary is: the lane split is closed, and what was actually
> being observed through it was a name collision that nobody had isolated.
>
> The lesson this cost is a re-measurement discipline, not a code change: a
> "still fails on both binaries" row is only true if both binaries were run
> after the fix landed. Deploying changes what `bin/simple` means mid-session,
> and a table column written before the swap silently describes the old
> artifact.

### Deployed 2026-09-19 09:09 KST

`bin/release/aarch64-unknown-linux-gnu/simple` — the target of the `bin/simple`
symlink and the binary every session on this host runs — was replaced with a seed
built from `origin/main` **42413e40caf plus this fix**, so the deployed artifact
is current rather than carrying the fix on a stale base.

| | before | after |
|---|---|---|
| sha256 | `308de6af84db5c26e2c08713…` | `350328bab5142ff443505ceb…` |
| size | 51,645,288 B | 51,607,912 B |
| built | 2026-09-18 | 2026-09-19 |

Method, unchanged from the 2026-09-18 redeploy: the new binary was staged beside
the target, its sha256 compared against the build output, and only then moved
over the target with `mv -f`. The rename is atomic, so the **29** processes
already running the old inode (MCP servers across several sessions) were not
disturbed; they pick the new binary up on their next start. The previous binary
is kept for rollback at
`bin/release/aarch64-unknown-linux-gnu/simple.stale-2026-09-19` (gitignored), and
restoring it is a single `mv` back over the same path. The target had a single
hard link, verified before the swap, so no sibling directory entry was broken.

Verified **before** the swap, on the candidate:

- `scripts/check/check-deployed-binary-optional-unwrap.shs --binary <candidate>`
  — `PASS — 6 row(s) checked, default and interpret lanes agree`.
- `nested_fn_in_lambda_capture_spec.spl` — 7/7.
- Five spec files (157 examples) run on the candidate and on the then-deployed
  binary: identical pass/fail counts on every one.

Verified **after** the swap, through `bin/simple` itself:

- the guard again — `PASS — 6 row(s) checked on /home/yoon/dev/simple/bin/simple`;
- `nested_fn_in_lambda_capture_spec.spl` — 7/7;
- the lambda repro from this record now prints `7` instead of failing with
  `semantic: variable ... not found`.

What deployment does **not** change: the spec-runner route still loses the
enclosing local for a recursive nested `fn` in a plain function body. That
remains open. The JIT half was a separate defect and is **now fixed too** — see
"Fix 2 (JIT lowering)" below; the bullet further down that says it is untouched
describes the state on the day the interpreter fix landed and is kept for that
history.

### What this does NOT fix, measured

- **`test/01_unit/os/acpi/acpi_test.spl` still fails its same 3 examples.** This
  record has claimed since August that the acpi spec is the silent-zero arm of
  this defect. **It is not.** A minimal probe of the acpi shape — a nested `fn`
  capturing a local `[u8]`, forwarding to a module-level `_buf_read32`, passed as
  a callback — passes on the OLD binary as well as the new one. The callback shape
  was never broken. Whatever fails in the acpi spec is a different defect and
  needs its own investigation; it should not be tracked here.
- **The JIT still drops the whole module to the interpreter** for this shape
  (`unresolved external symbol '<nested fn>'`, ~100-1000x). That is a separate
  defect in HIR lowering: `stmt_lowering.rs` answers `Node::Function(_f) =>
  Ok(vec![])` with the comment "Nested function definitions are ignored in native
  lowering for now". This change is interpreter-only and deliberately does not
  touch it, so the perf cliff remains.
- **Deployment — done 2026-09-19**, see the section above. `bin/simple` on this
  host now carries the fix. This bullet is kept rather than deleted because the
  gap it named was real for part of the day: the fix landed in source before the
  shared binary carried it, and anything measured against `bin/simple` in that
  window saw the old behaviour.

## Fix 2 (JIT lowering) 2026-09-19 — the module no longer drops

The second half of this record, tracked above as "a separate defect in HIR
lowering", is fixed. `hir/lower/stmt_lowering.rs` no longer answers
`Node::Function(_f) => Ok(vec![])`; a nested `fn` is lowered as a local closure
binding — `val <name> = \<params>: <body>` — and handed straight back to the
`Node::Let` arm.

### Why a closure, and not a hoist

Hoisting a nested `fn` to module scope was considered and rejected. It needs
either name mangling plus call-site rewriting through the body, or first-wins on
collision — and first-wins is precisely the defect class that
`duplicate_impl_method_definitions_silent_first_wins_2026-08-08` records: two
outer functions each declaring `fn helper` with different bodies, one silently
winning. The closure route needs none of that, and the probes below show the
closure path already compiles every capability a nested `fn` needs: capture of
an enclosing local, a direct call, and being passed as a value.

### The recursion guard, and why it is a correctness guard

HIR closures have no letrec. Inside a converted body the fn's own name is
unbound, so a self-recursive nested `fn` would either fail to resolve or —
materially worse — silently resolve to a module-level function of the same name
and compile a call to the **wrong body**. That would turn a perf cliff into a
wrong-answer defect, so self-recursion is detected at lowering time (via the
existing free-read collector `collect_identifiers_function`, which is
scope-aware and needed no new walker) and deliberately left on the fallback
path, where the interpreter answers correctly. The same missing letrec is what
makes a recursive **lambda** fail outright on both engines
(`val fact = \n: ... fact(n-1)` → `error[E1002]: function 'fact' not found`);
that is a distinct pre-existing defect and is not addressed here.

### Measured, before and after

Both columns are the same four probe files, run through `SIMPLE_JIT_STRICT=1`
(exit 0 = the whole module compiled; non-zero = it dropped) and through both
lanes for the value. "before" is the binary deployed earlier the same day, which
already carries the interpreter fix above — so this table isolates the lowering
change and nothing else.

| shape | before: strict | after: strict | value, both lanes |
|---|---|---|---|
| non-capturing nested `fn` | drops (`unresolved external symbol 'helper'`) | **compiles** | 42, unchanged |
| capturing nested `fn` | drops (`... 'at'`) | **compiles** | 42, unchanged |
| nested `fn` reading a `var` rebound later | drops (`... 'readx'`) | **compiles** | 1, unchanged |
| self-recursive nested `fn` | drops (`... 'fact'`) | drops (guard) | 24, unchanged |
| nested `fn` passed as a value | already compiled | compiles | 33, unchanged |

Two things this table is chosen to show beyond "it compiles now":

- **No answer changed anywhere.** The defect was always a silent ~100-1000x
  cliff with correct output, so an answer that moved would be the regression to
  fear, not the fix.
- **Capture semantics did not diverge.** The `var x = 1; fn readx(): x; x = 5`
  row is the one at risk: the interpreter snapshots the scope at the declaration
  point (the open question below), and a compiled closure capturing by reference
  would answer 5 instead of 1. Measured, the compiled closure answers **1**, the
  same as the interpreter, on both lanes. So this change inherits the existing
  semantics rather than introducing a lane split.

### Mutual recursion: unchanged, and worse than assumed

Two nested `fn`s calling each other still fails — but **not** because of this
lowering, and not only on the JIT. Measured on both binaries and both lanes, it
fails identically:

```
error[E1002]: function `is_odd` not found
```

The interpreter registers a nested `fn` when its statement executes, so a
forward reference from an earlier sibling has nothing to resolve against. That
is a pre-existing defect on the interpret route that this record's earlier
analysis did not know about; it is unaffected in either direction here.

### Scope

43 files under `src/` carry 157 nested `fn` declarations, so this was not a rare
shape.

### The AOT lane needed a second change, and measuring caught the assumption

The first draft of this section asserted that the standalone/native lane, having
no interpreter to fall back to, was hitting link errors that the lowering fix
would clear. **That was wrong, and measuring it is what showed so.** `compile`
refused all three shapes identically before *and* after the lowering change, and
not with a link error:

```
cannot compile to standalone SMF: 1 function(s) contain constructs that
require the interpreter:
  - outer: [Closure]
```

The refusal comes from a separate AST-level gate, `compilability.rs`, which sat
upstream of HIR lowering and flagged **every** nested `fn`:

```rust
Node::Function(_) => {
    // Nested function definitions
    add_reason(reasons, FallbackReason::Closure);
}
```

What makes that no longer defensible is the arm a few hundred lines below it:
`Expr::Lambda` is deliberately **not** flagged, with a comment saying closures
lower fine through MIR `ClosureCreate` and that a blanket fallback here
"prevents valid native code from being emitted at all". After the lowering
change those two are the *same construct* — and the inconsistency was directly
measurable: a capturing lambda compiled to standalone SMF while the
byte-equivalent nested `fn` was refused.

So the gate got the matching change: the nested-fn arm now analyzes the body on
its own merits (an interpreter-only construct *inside* the nested fn must still
flag the enclosing function, or it would be admitted to an artifact with nothing
to fall back to) and re-adds the `Closure` reason only for the self-recursive
case, using the same predicate as the lowering guard. Measured after:

| shape | `compile` before | `compile` after |
|---|---|---|
| non-capturing nested `fn` | refused `[Closure]` | **compiles** |
| capturing nested `fn` | refused `[Closure]` | **compiles** |
| self-recursive nested `fn` | refused `[Closure]` | refused `[Closure]` (correct — still interpreter-only) |
| capturing lambda (control) | compiles | compiles |

### The field-loss hypotheses, all probed, all refuted

A `FunctionDef` carries fields a `LambdaParam` does not, so the obvious worry
about this conversion is that one of them is silently dropped and turns a perf
cliff into a wrong answer — the same inversion the recursion guard exists to
prevent, on a different axis. Every candidate was probed rather than guarded
against on suspicion. All of them answer correctly on both lanes and now compile
whole (`SIMPLE_JIT_STRICT=1` exit 0):

| hypothesis | probe | result |
|---|---|---|
| a parameter default is lost | `fn helper(a: i64, b: i64 = 5)`, called `helper(37)` | 42 — default applied |
| `return` returns from the ENCLOSING fn | early `return` in an `if`, both paths exercised | 120 — returns from the closure |
| generic params are lost | `fn pick<T>(a: T, b: T) -> T` | 42 |
| variadics are lost | `fn total(items: i64...)`, called `total(10, 32)` | 42 |

So no additional guard was added for them: an unfalsified suspicion is not a
reason to widen the fallback set, and each of these would have been a shape left
needlessly on the slow path.

One shape does fail — a nested `fn` carrying a `requires` contract clause
prints nothing at all — but it fails **identically on both binaries and both
lanes**, so it is pre-existing and untouched here, not a consequence of this
change.

### What could not be measured on this host

Whether the newly-admitted AOT artifacts *execute* correctly is unverified,
because SMF execution is broken here for everything: a closure-free
`fn main(): print "value=42"` compiled to `.smf` dumps core when run, on the
deployed binary and on the one carrying these changes alike. That is the
already-tracked stage-binary SEGV
(`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18`,
and the `check-stage-binaries-runnable.shs` guard that is honestly RED), and it
is orthogonal to this change in both directions. What IS verified for the AOT
lane is admission at `compile`; end-to-end execution has to wait for that defect.

### Guard

`scripts/check/check-nested-fn-jit-lowering.shs` — four shapes through
`SIMPLE_JIT_STRICT=1`, with the values cross-checked between lanes. A spec
cannot guard this: `bin/simple test` runs specs on the interpret route, where
the defect does not exist, so a value-asserting spec passes identically before
and after (both measured). Verified to discriminate: `FAIL — 4 shape(s)
checked, 3 wrong` on the binary without this change, `PASS — 4 shape(s)
checked` with it.

The recursive row is pinned as *still falling back* on purpose. If letrec for
HIR closures ever lands, that row starts compiling and the guard FAILs — the
signal to re-measure and update it, the same two-way staleness rule the repo's
ratchets use.

The AOT half is pinned by three unit tests in `compilability.rs` rather than by
the shell guard, since they need no binary: a non-recursive nested fn must be
compilable, a self-recursive one must keep the `Closure` reason, and an
interpreter-only construct inside a nested fn body must still flag the enclosing
function.

### Regression evidence

`cargo test -p simple-compiler --release` was run on a clean worktree at `HEAD`
and on the tree carrying both changes. Both report `4094 passed; 19 failed`, and
the sorted failure NAME lists are **byte-identical** — so the 19 are pre-existing
and this change introduces none. (Counts alone would not have shown that; same
count with different names is the failure mode the diff exists to catch.) The
three new `compilability.rs` tests pass on top of that, and
`test/01_unit/interpreter/nested_fn_in_lambda_capture_spec.spl` is still 7/7 on
the new binary, which is what closes "did the AOT change disturb the interpreter
fix".

### One question left open, deliberately not asserted

A nested `fn` does **not** see a local rebound *after* the `fn` was declared — the
closure captures the block scope by value at the declaration point, so a later
`total = 5` is invisible. Whether that snapshot is the intended semantics or a
second defect is not settled here, and the spec says so at the point where such
an example would sit rather than blessing either answer.

---

## Investigation history, retained


**Status: OPEN — re-verified 2026-09-18 on a freshly redeployed seed. Not a stale-binary artifact.**

## Re-verification 2026-09-18, and a much smaller repro

This matters because the host's deployed seed was found to be 12 days stale that
same day and was replaced (see
`seed_jit_optional_unwrap_returns_enum_box_2026-09-18.md`), which invalidated
every measurement taken against the old binary. Several records checked in that
pass turned out to describe already-fixed behaviour. **This one does not.** Both
arms still reproduce on a seed built from `origin/main` on 2026-09-18.

**Arm B, loud, in three lines — no lambda and no callback required.** Every
earlier repro in this record went through an `it`-block lambda handing a closure
to a function under test, which framed this as a closure-passing defect. It is
simpler than that: a nested `fn` cannot see the enclosing block's locals at all.

```simple
use std.spec

describe "nested fn captures the it-block local":
    it "reads a captured array through a nested fn":
        val buf: [i64] = [7, 8, 9]
        fn r(i: i64) -> i64:
            buf[i]
        expect(r(1)).to_equal(8)

    it "reads a captured scalar through a nested fn":
        val n = 42
        fn g() -> i64:
            n
        expect(g()).to_equal(42)

    it "reads the captured array inline (control)":
        val buf: [i64] = [7, 8, 9]
        expect(buf[1]).to_equal(8)
```

```
✗ reads a captured array through a nested fn
    semantic: variable `buf` not found
✗ reads a captured scalar through a nested fn
    semantic: variable `n` not found
✓ reads the captured array inline (control)
3 examples, 2 failures
```

Three facts this adds to the record:

- **It is not array-specific.** A plain `i64` local fails identically. The
  original write-up's `[u8]` fixtures made this look like a container-capture
  problem; it is not.
- **It is a SEMANTIC-phase error, not a runtime one.** The message is
  `semantic: variable ... not found`, so the nested `fn`'s body is resolved
  against a scope that never contained the block's locals. That places the fix in
  name resolution, not in closure capture or environment copying.
- **The inline control passes**, so the local itself is bound correctly; only the
  nested `fn`'s view of it is missing.

**Arm A, the silent one, also still reproduces.** This record's named victim
`test/01_unit/os/acpi/acpi_test.spl` was re-run on the new seed and still fails
with the exact numbers quoted below:

```
✗ extracts MMIO base from GAS address at offset 48   expected 0 to equal 4275044352
✗ reads legacy PM_TMR_BLK at offset 76 ...           expected 0 to equal 45064
✗ prefers X_PM_TMR_BLK GAS at offset 208 ...         expected 0 to equal 47104
10 examples, 7 passed, 3 failed
```

So the two arms are one defect seen through two call shapes: calling the nested
`fn` **directly** raises the loud resolver error, while handing it to another
function as a callback yields the dangerous silent zero. Any fix must be checked
against both, and the three-line repro above is the cheaper of the two to iterate
on.

## Root cause, localised 2026-09-18 — it is NOT about spec blocks

The title and every repro in this record put the defect inside a spec `it`
block. That framing is wrong and has kept the search in the spec runner. Three
probes, each 12 lines and none of them using `std.spec` at all:

| where the nested `fn` is declared | what it reads | result |
|---|---|---|
| inside a plain `fn` body | that fn's `val` | **42, correct**, both lanes |
| inside a lambda body | that lambda's `val` | **`semantic: variable ... not found`** |
| inside a lambda body | a module-level `var` | **99, correct** |

So a `fn` nested in a **plain function** captures correctly, and the same `fn`
nested in a **lambda** resolves against module scope only. A spec `it` block is
simply a lambda, which is the whole of its involvement. Anything that nests a
`fn` inside any closure hits this, spec or not.

```simple
fn call_it(f: () -> i64) -> i64:
    f()

fn main() -> i64:
    val blk = \:
        val inner_local = 7
        fn nested() -> i64:
            inner_local          # semantic: variable `inner_local` not found
        nested()
    print call_it(blk).to_text()
    0
```

Read together, the three rows say the nested `fn` is lowered as a FREE,
top-level function: it keeps module scope and is handed no enclosing-lambda
environment. The lowering path for a `fn` inside a function body clearly does
thread the enclosing scope; the path for a `fn` inside a lambda body does not.
That is the fix site, and it is narrower than "closure capture" as a whole.

### A second, silent cost nobody had noticed

Both lambda probes also print this before the interpreter ever runs:

```
[jit-fallback] unresolved external symbol 'nested': whole module dropped to the
interpreter (expect ~100-1000x slowdown).
[INFO] JIT compilation failed, falling back to interpreter: ... would NULL-jump
in JIT; deferring to interpreter

```

The nested `fn` is not in the module symbol table either, so the JIT cannot
resolve it and **drops the entire module to the interpreter**. That happens even
in the module-scope probe, which returns the RIGHT answer — so a file carrying
one nested `fn` inside one lambda silently loses JIT for everything in it, with
the correct result masking the cliff. Every spec file using this shape has been
paying that.

## Scope note on the earlier "out of scope for this lane" verdict

The 2026-08-09 re-confirmation below closed with "no `.spl`/`.shs` root-cause fix
is available at this layer", on the standing "fix Simple, not Rust" rule. That
reasoning still holds about WHERE the defect lives, but the conclusion that it
cannot be worked has weakened: a Rust-seed fix was authored and landed on
2026-09-18 (`src/compiler_rust/.../mir/lower/lowering_stmt.rs`, PR #1090) when
that was where a defect actually was. Seed work is therefore available for this,
with the usual cost that it needs a seed rebuild to verify.

---

## Original record, retained

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN

**Re-confirmed 2026-08-09:** independently re-verified rather than assuming the
sibling's family-match. Ran a fresh minimal repro (nested `fn r8` capturing an
`it`-block `val buf`, passed as a callback) through `bin/simple test
--no-cache --no-cover-check` on the deployed Rust seed
(`bin/release/x86_64-unknown-linux-gnu/simple`, seed banner confirmed via
`--version`). The run is consistent with this doc's existing Arm A/B repros
(same seed, same construct class: nested `fn` inside an `it`-block lambda
referencing a lambda-local). Root cause and scope are unchanged from the
original write-up: this lives in the Rust seed's interpreter closure/scope
handling (`src/compiler_rust/compiler/src/interpreter*`), not in any `.spl`/
`.shs` source this lane may edit, and fixing it would require a seed rebuild
mid-session while other sessions are live in this tree — squarely against the
"Fix .spl not Rust" / "Pure Simple First" standing rules. No `.spl`/`.shs`
root-cause fix is available at this layer.
**Verdict: confirmed, left OPEN — architectural (Rust-seed interpreter),
out of scope for this lane.**
**Found:** 2026-08-04
**Severity:** high — the silent arm produces **wrong values with no error**, so
affected specs fail with plausible-looking assertion mismatches that read like
product bugs. `test/01_unit/os/acpi/acpi_test.spl` (3 failed) is one victim;
the pattern ("build a `[u8]` fixture, hand `read8`/`read32` closures to the
function under test") is a common way to unit-test byte-parsing kernel code.

## Symptom

Two arms, same construct. Both reproduce on the interpreter lane that
`bin/simple test` uses.

### Arm A — silent zero (the dangerous one)

`test/01_unit/os/acpi/acpi_test.spl`:

```
✗ extracts MMIO base from GAS address at offset 48
    expected 0 to equal 4275044352
✗ reads legacy PM_TMR_BLK at offset 76 for ACPI 1.0 FADT
    expected 0 to equal 45064
✗ prefers X_PM_TMR_BLK GAS at offset 208 for ACPI 2.0+ FADT
    expected 0 to equal 47104
```

Minimal self-contained repro (run with
`bin/simple test --no-cache --no-cover-check <file>`):

```
use std.spec
use os.kernel.acpi.hpet_table.{acpi_hpet_base_raw, GAS_SPACE_SYSTEM_MEMORY}

fn _make_hpet_table(mmio_lo: u32, mmio_hi: u32) -> [u8]:
    var buf: [u8] = []
    var i: u64 = 0
    while i < 64:
        buf = buf + [0]
        i = i + 1
    buf[44] = GAS_SPACE_SYSTEM_MEMORY
    buf[48] = (mmio_lo & 0xFF) as u8
    buf[49] = ((mmio_lo >> 8) & 0xFF) as u8
    buf[50] = ((mmio_lo >> 16) & 0xFF) as u8
    buf[51] = ((mmio_lo >> 24) & 0xFF) as u8
    buf

fn _buf_read8(buf: [u8], off: u64) -> u8:
    buf[off as i64]

fn _buf_read32(buf: [u8], off: u64) -> u32:
    val b0 = buf[(off + 0) as i64] as u32
    val b1 = buf[(off + 1) as i64] as u32
    val b2 = buf[(off + 2) as i64] as u32
    val b3 = buf[(off + 3) as i64] as u32
    b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)

describe "acpi repro":
    it "fixture bytes are right":                     # PASSES
        val buf = _make_hpet_table(0xFED00000, 0)
        expect(_buf_read32(buf, 48) as u64).to_equal(4275044352)
    it "product fn via nested-fn callbacks":          # FAILS: expected 0 to equal 4275044352
        val buf = _make_hpet_table(0xFED00000, 0)
        fn r8(off: u64) -> u8: _buf_read8(buf, off)
        fn r32(off: u64) -> u32: _buf_read32(buf, off)
        val result = acpi_hpet_base_raw(r8, r32, 0)
        expect(result as u64).to_equal(4275044352)
```

The first example proves the fixture and the arithmetic are correct — the same
buffer read directly yields `4275044352`. Only the route through the nested-fn
callbacks yields `0`.

### Arm B — hard error

Calling the nested fn *directly* inside the same `it` block instead of passing
it on:

```
it "val-bound: via nested fn":
    val buf = _mk()
    fn r8(off: u64) -> u8: _rd8(buf, off)
    expect(r8(3) as u64).to_equal(77)
# ✗ semantic: variable `buf` not found
```

## What was ruled out (each probed, each refuted)

This took four wrong hypotheses; recording them so nobody re-walks them:

| hypothesis | probe result |
|---|---|
| `.push()`/array writes don't persist (value-type arrays) | **Refuted.** `.push()` mutates in place; discard vs. reassign both give `len=1`, interpreter *and* JIT |
| the u32 byte-split/recombine math is wrong | **Refuted.** Standalone probe: bytes `0,0,208,254`, recombined `4275044352`, `mmio_phys` `4275044352` |
| nested-fn closure capture is broken generally | **Refuted.** Inside a plain `fn main`, all of direct-index / via-helper / via-nested-fn / nested-fn-passed-as-arg return `77` |
| imported module-level `val` constants resolve to 0 | **Refuted.** `HPET_TBL_OFF_GAS == 44` and `HPET_TBL_GAS_OFF_ADDRESS == 4` assert green when imported into a spec |

The distinguishing variable is the **enclosing scope**: the identical nested-fn
construct works inside `fn main` and fails inside an `it` block. `it` bodies are
lambdas, so capture of a lambda-local by a nested `fn` declared in that lambda
is the broken case.

Note one further wrinkle, not yet explained: a nested fn passed as a callback
that is invoked with a *constant* offset **does** work
(`use_cb(r8)` reading offset 3 returned `77`), while the acpi case — where the
callee computes the offset (`base + HPET_TBL_OFF_GAS + …`) — returns 0. So Arm A
may be a second, distinct arm rather than the same capture failure; whoever
picks this up should bisect that boundary before assuming one fix covers both.

## Root cause

Not isolated to a specific line. The construct is a nested `fn` declaration
inside a lambda (`it` block) referencing a binding from the lambda's scope.
Arm B's `semantic: variable X not found` shows the capture environment for the
nested fn simply does not include the enclosing lambda's frame; Arm A shows a
path where, instead of erroring, the read yields `0`.

The failing lane is the seed interpreter — `bin/simple` here is the Rust
bootstrap seed (57MB, 2026-08-04, prints the seed banner) and specs run
`[mode: interpreter]`.

## Why not fixed now

The fix is in interpreter scope/closure handling in the **Rust seed**
(`src/compiler_rust/compiler/src/interpreter*`), which is outside this lane's
scope (`src/os/`, `src/lib/nogc_async_mut_noalloc/`) and against the standing
"Fix .spl not Rust" / "Pure Simple First" rules; it also forces a seed rebuild
while other sessions are live in this tree.

It must **not** be papered over by rewriting `acpi_test.spl` to avoid nested
fns: `acpi_hpet_base_raw` takes `read8`/`read32` function parameters by design
(`src/os/kernel/acpi/hpet_table.spl:40`) precisely so it can be unit-tested
against a fixture instead of real MMIO. Removing the callbacks would delete the
only hosted test of that parser.

The product code itself is **not** implicated: `acpi_hpet_base_raw`
(`hpet_table.spl:40-54`) reads correctly when driven by the same helpers
outside a lambda.

## Collateral: three acpi examples pass for the wrong reason

Because the silent arm yields `0`, `mmio_phys` comes out `0` and the function
returns `nil` — which is what the three negative tests assert. So
`returns nil when address_space_id is not SystemMemory`,
`returns nil when MMIO address is zero`, and the FADT equivalents are currently
**green regardless of the product's behaviour**. They will need re-checking
once the capture defect is fixed.

## Measurement note

`--no-cache --no-cover-check` are mandatory: without them a directory can report
`No test files found … Results: 0 total` and exit 0 (concurrent runs rewrite a
shared path-scoped manifest), and a missing `@cover` annotation aborts the run
so zero specs execute. Treat any `0 total` as **unmeasured**, not passing.

