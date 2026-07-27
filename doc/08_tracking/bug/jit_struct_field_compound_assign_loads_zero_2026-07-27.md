# Bug: JIT silently loads 0 for the read side of `obj.field += v` (struct-field compound assignment)

- **Date:** 2026-07-27
- **Status:** open
- **Severity:** CRITICAL — silent wrong results, default execution engine, long-standing
- **Found by:** lane PMS (interpreter place-model work), independently reproduced and
  characterized by the coordinator

> **CORRECTED 2026-07-27 (lane CAUDIT + lane JITCA).** Three claims in the
> original write-up below were wrong. (1) The result is `target = rhs` — the
> **operator is dropped too**, not just the load: `var y=100; y -= 7` gives `7`,
> not `-7` or `93`; `s.n *= 3` with `n=10` gives `3`. `+=` cannot distinguish
> `0+rhs` from `=rhs`, which is why the first characterization stuck.
> (2) **Plain local variables are equally affected** — `var x=100; x += 7` → `7`;
> a `for` loop accumulator `sum += k` → the last `k`. So "convert the call sites"
> is NOT a containment strategy; the fix must be in the compiler.
> (3) `parser_extensions.spl:224` is **inside a `"""` docstring**, not live code —
> the "compiler's own parser miscounts" claim was false. Of 741 hits in owned
> `src/**`, 367 were in scope, 24 field/index-shaped, **20 of those false
> positives** (code generators emitting Rust/C/PTX, comments) and the 4 real ones
> all in removed/dead `src/app/interpreter/`. **Live exposure found: zero.**
>
> **Root cause (JITCA), exact:** `src/compiler/50.mir/mir_lowering_stmts.spl`,
> `MirLowering.lower_assign` — the `case Field` and `case Index` arms accept
> `op: HirAssignOp?` and **never read it**, emitting the same MIR as a plain `=`.
> There is no load in the MIR at all. The sibling `lower_assign_var` handles `op`
> correctly, which is why locals looked different at first. Fix written, blocked
> on redeploy.
>
> **Severity caveat:** every measurement here was taken on Rust bootstrap **seed**
> binaries (`bin/simple` is seed-clobbered; no self-hosted binary currently
> exists). Re-run `build/caudit_probe/probe3.spl` on a real self-hosted binary
> before acting on the CRITICAL rating.

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
