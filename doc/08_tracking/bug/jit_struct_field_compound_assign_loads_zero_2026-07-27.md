# Bug: JIT silently loads 0 for the read side of `obj.field += v` (struct-field compound assignment)

- **Date:** 2026-07-27
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  The title is wrong and is kept only for searchability: nothing loads zero, and
  nothing is struct-field-specific. The operator was being discarded.
- **Severity:** CRITICAL — silent wrong results, default execution engine, long-standing
- **Found by:** lane PMS (interpreter place-model work), independently reproduced and
  characterized by the coordinator

## Symptom

On the JIT/native path — the **default** engine — a compound assignment to a struct
field discards the field's current value and computes `0 <op> rhs`:

```
struct Counter:
    n: i64

var s = Counter(n: 5)
s.n += 2        # -> 2   (expected 7)

var t = Counter(n: 5)
t.n = t.n + 2   # -> 7   (correct; explicit form is fine)
```

The store works; the **load side of the compound assignment** yields 0 instead of the
field's value. The explicit read-modify-write spelling of the identical operation is
correct, which is what makes this so easy to miss in review.

Depth makes it worse but is not required — **one hop is already wrong**:

| expression (start value) | JIT | interpreter | expected |
|---|---|---|---|
| `s.n += 2` (n=5), one hop | **2** | 7 | 7 |
| `c.mid.inner.n += 4` then `+= 3` (n=0) | **3** | loud error | 7 |
| `arr[1] += 10` on `[1,2,3]` | **10** | loud error | 12 |
| `t.n = t.n + 2` (n=5) | 7 | 7 | 7 |

The interpreter is *correct at one hop* and *fails loudly* on nested/indexed forms
(`invalid assignment: deeply nested augmented field access requires intermediate
variables`). Only the JIT is silently wrong — the reverse of the usual
"interpreter is the defective engine" story from
[selfhost_two_hop_field_method_mutation_lost_2026-07-27.md](selfhost_two_hop_field_method_mutation_lost_2026-07-27.md).

## Scope

- **Not a regression.** Identical results on the deployed seed `bin/simple` and on the
  older self-hosted build `build/native_probe/simple` (Jul 23), so it predates this
  session's work.
- **Not caused by** the ECS `me`-form conversion (7d08f651ca7). ECS contains **zero**
  struct-field compound assignments, verified by grep — checked precisely because that
  change moved ECS-importing programs onto the JIT.
- ~82 candidate `x.f += ...` sites exist in owned `src/` (some are inside string
  literals in code generators and are not real). Confirmed real instances include
  `src/compiler/10.frontend/parser_extensions.spl:224` (`self.count += 1`) — i.e. the
  compiler's own source relies on the broken form.

## Suspected mechanism

Per lane PMS: the store re-resolves the place while the load does not, so the read
side never reaches the resolved field slot and contributes 0. The fix belongs at the
compound-assignment lowering site — the load must resolve the same place as the store,
once, and both must address identical storage.

## Reproduce

```
bin/simple run build/jit_compound_probe.spl                          # JIT: wrong
SIMPLE_EXECUTION_MODE=interpreter bin/simple run build/onehop_probe.spl   # correct at one hop
```
(probe sources: `build/jit_compound_probe.spl`, `build/onehop_probe.spl`)

## Workaround until fixed

Spell it explicitly: `x.f = x.f + v` (and `a[i] = a[i] + v`). Verified correct on both
engines at every depth tested.

## Next step

1. Fix the load side of compound-assignment lowering in the JIT/MIR path so it resolves
   the same place as the store; add a regression spec covering one-hop, nested, and
   indexed forms on BOTH engines with absolute expected values.
2. Audit the ~82 candidate sites for real instances and convert or fix them.
3. Give the interpreter the nested/indexed compound-assign place path it currently
   rejects (lane PMS has this change written; it is redeploy-blocked).

---

## CORRECTION + audit results (lane CAUDIT, 2026-07-27)

Full audit: `.spipe/compound_assign_audit/state.md`.
Evidence: `build/caudit_probe/EVIDENCE.txt`, probes `build/caudit_probe/probe{,2,3}.spl`.

Two claims above are contradicted by measurement. **The title and the
"`0 <op> rhs`" model are both wrong**, and the blast radius is much larger.

### 1. The result is `target = rhs`, not `0 <op> rhs`

Every example in the sections above uses `+=`, where `0 + rhs` and `rhs` are
indistinguishable. Testing other operators disambiguates:

```
var y = 100 ; y -= 7   -> 7    # "0 - 7" would be -7; correct is 93
var s = S(n: 10); s.n *= 3     -> 3    # "0 * 3" would be 0; correct is 30
```

The load **and the operator** are discarded; the RHS is simply stored. So the
"suspected mechanism" (load contributes 0 to a real operation) does not fit —
the arithmetic is not being performed at all.

### 2. Plain local variables are affected too — this is not struct-field-specific

```
var x = 100 ; x += 7               -> 7    (expected 107)
var sum = 0 ; for k in 0..5: sum += k  -> 4    (the final k; expected 10)
```

This invalidates "audit the ~82 candidate `x.f +=` sites" as the containment
strategy: there are 367 in-scope compound assignments (741 repo-wide) and the
overwhelming majority are locals. Source-level conversion is not a viable
remedy — it would mean abandoning the feature. The fix must be in the compiler.

### 3. `parser_extensions.spl:224` is NOT a real instance

Cited above as proof that "the compiler's own source relies on the broken form".
It is inside a `"""` docstring — the `Example:` block of `parse_actor_body`'s doc
comment — and is not executable code.

Of 24 field/index-shaped hits in scope, **20 are false positives**: docstrings,
`#` comments, and string literals in code generators emitting Rust/C/PTX
(`sffi_gen`, `native_profile_counter`, `os/ml/kernels.spl`, `os/crypto/*`).
The remaining 4 are all in `src/app/interpreter/`, which is **removed/dead code**
(`src/app/__init__.spl:33`). They were converted to the explicit form
(`debug.spl:195`; `macros.spl:73,80,85`), but since the module is dead this
**removed zero live exposure**. There are no live struct-field/index compound
assignments in the audited scope.

### 4. Caveat: seed-only measurement

"Identical results on the deployed seed `bin/simple` and on the older self-hosted
build `build/native_probe/simple`" — both of those binaries print
*"this Rust-built Simple binary is a bootstrap seed only"*. `bin/simple` is
seed-clobbered (→ `bin/release/x86_64-unknown-linux-gnu/simple`) and no genuine
self-hosted binary is currently available. **Both data points are the same class
of seed**, so "not a regression / long-standing" is not yet established, and
neither is the claim that this affects the default production engine.

Against it affecting production: 343 in-scope local `+=` sites exist, including
in the compiler itself; a universal compound-assign failure would be impossible
to miss. **Before acting on the CRITICAL severity, re-run
`build/caudit_probe/probe3.spl` on a real self-hosted binary.** If it reproduces
there, the severity is if anything understated; if it does not, this is a seed
defect and should be retitled accordingly.

---

## Root cause + fix (lane FABLE, 2026-08-01) — FIXED

Base: `8fdc21c67b5725f3dfa4256b3ae7a486b58fa652`.
The CAUDIT correction above was right on both counts. This section supplies the
mechanism, the located site, and the fix.

### Root cause — the operator is dropped in HIR lowering

`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`, `Node::Assignment` arm.

`HirStmt::Assign` has only `{ target, value }` — **there is no operator field**.
The AST node does carry one (`assign.op: AssignOp`), and the lowering never read
it. It ran its diagnostics and then unconditionally emitted
`HirStmt::Assign { target, value }`, so every augmented assignment became a plain
store of the bare right-hand side. `p.f += 5` lowered to `p.f = 5`.

This is *not* a JIT bug and *not* a codegen bug. It is a front-end lowering bug in
the shared HIR path, which is why it looked identical on every compiled backend.
The tree-walking interpreter was correct only because it never uses this path —
it reads `assign.op` itself in `interpreter_control.rs`.

### Three-lane table (repro `var p = Point(10, 100)`, seed at the base commit)

| statement            | expected | interpret | cranelift JIT (before) | cranelift JIT (after) |
|----------------------|----------|-----------|------------------------|-----------------------|
| `p.f += 5`           | 15       | 15        | **5**                  | 15                    |
| `p.f += 5` (again)   | 20       | 20        | **5**                  | 20                    |
| `p.g -= 40`          | 60       | 60        | **40**                 | 60                    |
| `p.g *= 2`           | 120      | 120       | **2**                  | 120                   |
| `c.a += 4` (class)   | 13       | 13        | **4**                  | 13                    |
| `n += 5` (plain local)| 15      | 15        | **5**                  | 15                    |
| `xs[0] += 5` (index) | 6        | loud error| **5**                  | 6                     |
| `p.f = p.f + 5`      | 12       | 12        | 12                     | 12                    |

`-=` giving `+40` and `*=` giving `2` are the discriminating measurements: a
zeroed load would give `-40` and `0`. The stored value is always exactly the RHS.

The **LLVM JIT lane (`SIMPLE_EXECUTION_MODE=llvm`) segfaults** on this reproducer
both before and after the fix. That is a separate, pre-existing defect and is not
covered here.

### Fix

Desugar `x op= v` to `x = x op v` at the lowering site, after the existing
diagnostics so they still see the user-written RHS. Covers `+= -= *= /= %=`.

Verified: all eight shapes above correct on cranelift after the fix, interpreter
output unchanged, and self-referencing (`n += n` -> 10, `m *= m` -> 49) and
index (`xs[i] += 10`) targets correct.

### Suspension compound assignment — FIXED 2026-08-01 (was the remaining gap)

`AssignOp::SuspendAddAssign` / `SuspendSubAssign` / `SuspendMulAssign` /
`SuspendDivAssign` (`~+=`, `~-=`, `~*=`, `~/=`) were **still dropped to a plain
store** by this same site after the original fix, which mapped only the five
plain forms. The shape of the defect was identical, so this was a sibling left
behind by an incomplete sweep, not a separate bug.

**Measured at `19f3241f568` before the fix** (release build of `simple-driver`,
`SIMPLE_EXECUTION_MODE=jit`, 0 JIT fallbacks, exit 0, no diagnostic):

| expression | start | want | JIT before | interpreter |
|---|---|---|---|---|
| `s.n ~+= 2` | 5 | 7 | **2** | 7 |
| `s.n ~-= 2` | 5 | 3 | **2** | 3 |
| `s.n ~*= 3` | 5 | 15 | **3** | 15 |
| `s.n ~/= 4` | 20 | 5 | **4** | 5 |
| `x ~+= 2` (plain local) | 5 | 7 | **2** | 7 |

Every wrong value is exactly the right-hand side — the operator-dropped
signature, not a load returning zero.

**The deferral reason did not survive checking.** Folding these does *not*
change async lowering: suspension is a separate axis carried by `assign.op`
itself, which `compound_assign_binop` only reads and never rewrites. The
tree-walking interpreter has folded all four to the same `BinOp`s since before
this bug was filed — `interpreter/node_exec.rs::exec_augmented_assignment`
computes its `is_suspend` await decision *independently* of `bin_op`. The fix
therefore makes the JIT match an existing reference behaviour rather than
inventing one. `~=` (`SuspendAssign`) stays unfolded: it is a bare
await-assignment with no arithmetic operator, exactly like plain `=`.

The `_ => None` catch-all was also replaced with an **exhaustive** match, so a
future `AssignOp` variant is now a compile error instead of another silently
dropped operator. That is the class of change that prevents a third sibling.

Standing coverage: `test/fixtures/jit_differential/suspend_compound_assign.spl`,
registered `known_good: "both"`. **Non-vacuity proved against the
implementation** (not a shim): the harness reports `unexpected failures: 1 /
REGRESSION` on the unfixed origin-tip binary and `0` on the fixed one.

### Interpreter gap found while probing — `xs[i] += v` (LOUD, not silent)

Separate and pre-existing at `19f3241f568`: the **interpreter** rejects an
indexed compound-assignment target outright —
`error: semantic: invalid assignment: unsupported augmented assignment target`,
rc=1 — for `arr[1] += 10`, which the JIT computes correctly (12). This is the
mirror image of the bug above and is recorded rather than smoothed over. It
**fails loudly**, so it is not a silent-wrong-answer defect and was left
unfixed here; it is out of scope for this bug and needs its own entry.

### Specs cannot gate this — read before trusting a green run

`test/01_unit/compiler/compound_assign_lowering_spec.spl` was added with this fix.
**It passes on the UNFIXED compiler**, including under
`SIMPLE_EXECUTION_MODE=cranelift SIMPLE_JIT_STRICT=1`, while the plain
`print`-based reproducer of the very same expressions fails there. The `describe`
/ `it` blocks execute at module initialization, which the seed always runs
interpreted, so the functions they call are evaluated interpreted too — the lane
that was already correct.

That is the structural reason this survived since at least 2026-07-27 despite
367 in-scope compound assignments: **no spec in this suite can observe the
compiled lanes.** The spec is therefore documentation and an interpreter-path
guard, *not* an active gate for this bug. The real evidence is the reproducer
table above. Anyone claiming a compiled-lane fix from a green `simple test` run
is reading a false green.
