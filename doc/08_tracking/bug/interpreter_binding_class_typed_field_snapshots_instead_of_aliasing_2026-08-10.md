# Binding a class-typed FIELD to a local snapshots it — interpreter only

> **Root cause lives elsewhere — see
> `interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md`**,
> the canonical record for the class-value-identity family (list index / field
> bind / dict get). This record is retained in full: its symptom, its P1-P6
> probe matrix, its `SjClient` production consequence and its history are
> independent discovery evidence and are NOT superseded in content.
>
> **Correction (2026-08-17, source-verified).** The closing triage section of
> this file attributes the did-not-reproduce result to "the
> `ClassInstance(Arc<ClassInstance>)` shared-identity value variant added in
> `a155bff913f4`". That mechanism claim is **false**. `Value::ClassInstance` has
> **zero producers**: `grep -rn "ClassInstance::new" --include=*.rs
> src/compiler_rust` returns 0, there is no `Arc::new(ClassInstance` and no
> `ClassInstance { .. }` literal outside its own declaration at
> `src/compiler_rust/compiler/src/value.rs:1114`. Every interpreter site
> consumes or re-wraps an instance that nothing ever builds. Source `class`
> values are therefore still `Value::Object`, the copy-on-write struct carrier,
> exactly as the "Why it happens" section below says — that analysis stands and
> was NOT superseded by the triage note. The triage note's *observation* (the
> fixture printed `field=42`) rests on an execution run and is left as filed; only
> its causal attribution is retracted here.

> **CONTRADICTION OPEN (2026-08-18): the blocked spec is still RED.** The
> CLOSED/DID-NOT-REPRODUCE disposition below rests on a minimal two-class
> fixture. The `Blocks:` spec was never re-run after that closure. It has now
> been re-run and the blocked example still fails with the original signature —
> see the dated section at the end of this file. The disposition line is left
> as filed (a minimal fixture passing is a real observation), but it is
> **not consistent with the tree**: either the fixture is too small to exercise
> the defect, or the spec is red for a second, different reason. Resolving this
> requires narrowing the gap between the two, not re-adjudicating either from
> the other. This record was NOT reopened unilaterally.

- **Status (single authoritative line, 2026-08-17): CLOSED — DID NOT REPRODUCE.**
  Basis: EXECUTION evidence — two independent 2026-08-17 reproducer runs of the
  doc's own bind-then-mutate (P6) shape under the interpreter both show the local
  ALIASING the field (`back_through_root=1`; `field=42 / local=42`). See the two
  dated sections at the end of this file.
  - *Mechanism is NOT established.* The closing triage section attributes the
    change to `Value::ClassInstance(Arc<..>)`; the header Correction above
    retracts that attribution on SOURCE evidence (zero producers). Execution
    evidence and source evidence are different kinds and neither overrides the
    other here: the OBSERVATION (aliasing works) stands, the CAUSE is unknown.
  - *What would reopen this row:* a reproducer run — not a source reading — in
    which the P6 shape prints `back_through_root=0` under
    `SIMPLE_EXECUTION_MODE=interpreter` on a stated binary.
- ~~Status: OPEN (P1)~~ — **SUPERSEDED.** Written 2026-08-17 06:41 by
  `1d52c95627b` (reformat of the original 2026-08-10 `OPEN — engine divergence`
  filing). That same commit's message already records this row as behaving; the
  line was reformatted, not re-adjudicated, and 35 minutes later `e5083c948b0`
  appended the DID NOT REPRODUCE section without updating it. Stale line, kept
  for history.
- ~~Status re-verified 2026-08-17 by source inspection (triage shard 02).~~ —
  **SUPERSEDED**, same commit, same reason.
- **Filed:** 2026-08-10
- **Scope note for everything below this block:** the sections that follow
  (Blocks / What diverges / Production consequence / Why the spec is left RED /
  Unblock condition / Root cause located) are the ORIGINAL 2026-08-10 filing and
  its root-cause work, preserved verbatim as discovery evidence. Their
  present-tense "remains RED" / "still OPEN" wording describes 2026-08-10, not
  today's disposition. This header block is the current status.
- **Blocks:** `test/{02_integration,integration}/app/sj_daemon_mutual_exclusion_spec.spl`
  example *"sees the lease through SjClient -> fallback_exec -> handle_cli_args"*,
  deliberately left **RED**.

## What diverges

A `class` is a reference type, so passing one around must preserve identity.
It does — except when the value is obtained by **reading a field of an
aggregate and binding it**, and then mutated. Under the interpreter the root
does not observe the mutation; under the JIT it does.

`build/q18/probe_nesting.spl`, one file, both engines, with an absence control:

| probe | expression | interpreter | JIT |
|---|---|---|---|
| P1 | local class val, `c.bump()` | 1 | 1 |
| P2 | class in a **struct**, `s.c.bump()` | 1 | 1 |
| P3 | class in a **class**, `co.c.bump()` | 1 | 1 |
| P4 | two levels, struct-in-struct, `s2.inner.c.bump()` | 1 | 1 |
| P5 | two levels, class-in-class, `c2.inner.c.bump()` | 1 | 1 |
| **P6** | `val mid = c3.inner` … `mid.c.bump()`; read back `c3.inner.c.n` | **0** | **1** |
| — | NEGATIVE CONTROL: untouched instance | 0 | 0 |

Every in-place chained form agrees. Only the **bind-then-mutate** form (P6)
splits, and the negative control is 0 in both engines, so no engine is
trivially answering "1".

Note this is the mirror image of the usual advice: the documented workaround
for erased-receiver chains is "introduce an intermediate typed `val`". For a
class-typed field that workaround is precisely what breaks identity under the
interpreter.

## Production consequence — the RED example

`src/app/sj/client.spl:38` is exactly the P6 shape:

```
fn exec_args(client: SjClient, argv: [text]) -> SjResult:
    _wrap(fallback_exec(client.handler, parsed.argv, rt_getpid()))
```

`client.handler` is read out of the `SjClient` struct and handed on. Under the
interpreter each such read yields a handler whose `LeaseManager` is a fresh,
empty instance, so no request through `SjClient` can observe a lease taken by
another. Measured after `LeaseManager` was made a class
(`build/q18/probe_client.spl`, interpreter):

```
D1.acquired=true count=1                       # handler held in a local val — OK
D2.acquired=true count_chained=0               # via client.handler.lease_manager — LOST
D3.acquired=true count_via_val=1  back_through_client=0
D4.fallback_exit=0                             # fallback_exec(c2.handler, …)  -> no exclusion
D5.fallback_via_val_exit=75                    # fallback_exec(h2, …)          -> exclusion works
```

D5 vs D4 is the whole bug in two lines: identical call, one through a bound
field, one through a local.

**This is NOT fixed by making the containers classes.** Converting
`SjRequestHandler` and then `SjClient` from `struct` to `class` was tried and
changed nothing (D2 stayed 0 in both cases); those edits were reverted rather
than shipped as no-op churn. The defect is in how the interpreter materialises
a class-typed field read, not in the container's kind.

## Why the spec is left RED, not softened

Per repo rule, a correctly-failing spec pinning a real defect is not weakened,
marked pending, or deleted. The three examples that do not depend on this
defect (direct-handler exclusion, its negative control, lease release) are
GREEN and guard the fix that did land.

## Unblock condition

Interpreter materialises a class-typed field read as the same instance the
aggregate holds. Then P6 reads 1 in both engines and the RED example goes
green with no change to its assertions.

---

## Root cause located (2026-08-10) — still OPEN, fix is a value-model change

### Reproduction re-confirmed, with lane attribution actually checked

`build/q18/probe_nesting.spl`, deployed seed, both lanes in one session:

| lane | P6 | NEGCTL | `[jit-fallback]` lines on stderr |
|---|---|---|---|
| interpreter (`SIMPLE_EXECUTION_MODE=interpret`) | `back_through_root=0` | 0 | — |
| JIT (default `run`) | `back_through_root=1` | 0 | **0** |

The JIT run was confirmed to be a genuine JIT run (zero `[jit-fallback]`
diagnostics), so the divergence is real and not a mis-attributed fallback.

### Why it happens

The interpreter is the **Rust seed**, and it has no true reference values. In
`src/compiler_rust/compiler/src/value.rs:1114` a class instance is

```rust
Object { class: String, fields: Arc<HashMap<String, Value>> }
```

— an `Arc` used for cheap cloning with **copy-on-write** mutation via
`Arc::make_mut`. Struct and class instances share this one representation.
Binding `val mid = c3.inner` clones the `Value`, so the `Arc` is now shared;
the first mutation through `mid` calls `Arc::make_mut`, which **clones the map
because it is shared**, and the root never observes the write.

Reference semantics are not modelled; they are *simulated* at call boundaries
only. `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:953`
defines `is_value_type_struct` over `ClassDef::is_value_type` (declared in
`src/compiler_rust/parser/src/ast/nodes/definitions.rs:393`, whose own doc
comment states structs are VALUE types and `class` are REFERENCE types), and
lines 1065/1088 use it to **copy the callee's value back** into the caller after
a call. That machinery covers only `ArgSource::Ident` and `ArgSource::Field`
argument positions.

That is exactly why P2–P5 pass and only P6 fails: `co.c.bump()` resolves as a
*place* rooted at the real variable (`interpreter/place.rs:90` pushes
`Projection::Field`), so the mutation lands on the root. `val mid = c3.inner`
severs that provenance — `mid` is a fresh root with no record that it came from
`c3.inner`, and no copy-back path exists for local bindings.

### Why this is not a small patch

1. **There is no other interpreter to fix.** `src/compiler/10.frontend/core/interpreter/eval.spl`
   is a constant-expression evaluator — it contains no `FieldAccess`/`Object`
   handling at all. User programs run on the Rust seed, so this cannot be fixed
   in pure `.spl`, which collides with the repo's "fix .spl not Rust" rule and
   needs an explicit ruling.
2. **A correct fix changes the value model.** Genuine aliasing needs shared
   interior mutability (e.g. `Arc<RwLock<..>>`) for class instances; there are
   **210 non-vendor `Value::Object` match sites**. The alternative — recording
   alias provenance for local bindings and propagating writes back up the field
   path after every mutating statement — keeps the model but extends an already
   ad-hoc copy-back simulation into local scopes.
3. **An existing test locks the current behaviour.**
   `interpreter/node_exec.rs::field_assignment_cow_protects_struct_local_alias`
   asserts that aliasing an object to a second local and mutating through it must
   NOT leak. It builds its object with an **empty `classes` map**, so
   `is_value_type_struct` returns false and the instance is treated as a
   reference type — meaning a naive "non-value-type objects alias" fix breaks
   this test. Any fix must consult a populated class registry and keep unknown
   classes on value semantics, and that test should be updated to register its
   `Point` as `is_value_type: true` to say what it actually means.
4. **It sits on the deferred axis.** This is adjacent to the open
   struct deep-copy-vs-shared-handle question, which is reserved for the repo
   owner. `class` is unambiguously a reference type, but the *mechanism* chosen
   here will determine the struct answer too, so it should be decided together.

### Status

Root-caused with file:line, not fixed. The blocked example in
`sj_daemon_mutual_exclusion_spec.spl` therefore **remains RED**, correctly, and
was not touched or softened.


## 2026-08-17 CORE-P1 triage: DID NOT REPRODUCE / fix present in current source

Verified against CURRENT SOURCE (content, not SHA ancestry) during the crit_01
CORE-P1 sweep. REPRODUCER RUN GREEN. Fixed by the `ClassInstance(Arc<ClassInstance>)` shared-identity value variant added in `a155bff913f4` (2026-08-15), which gives source `class` values reference semantics distinct from the copy-on-write `Object` carrier used for `struct` values (`src/compiler_rust/compiler/src/value.rs:1234-1240`). That commit PREDATES the currently deployed seed, so it is testable with the deployed binary today. Fixture: bind a class-typed field to a local, mutate through the local, read back through the field --\n\n```\nclass Inner:\n    n: i64\nclass Outer:\n    inner: Inner\nfn main():\n    val o = Outer(inner: Inner(n: 0))\n    val bound = o.inner\n    bound.n = 42\n    print("field=" + o.inner.n.to_string())\n    print("local=" + bound.n.to_string())\n```\n\n`bin/simple run` -> rc 0, `field=42` / `local=42`. The local ALIASES the field as a class value must; the reported snapshot behaviour is gone.

---

## 2026-08-18 — the `Blocks:` spec was re-run: still RED, original signature

The 2026-08-17 closure above cites execution evidence, but that evidence is a
**minimal 2-class fixture**, not the spec this record names in its `Blocks:`
line. Nothing in the file showed that spec had been re-run after the closure, so
it was re-run now.

**Spec location.** Present under its exact original name, in both live mirror
trees, byte-identical (`diff` clean, 91 lines each):

- `test/02_integration/app/sj_daemon_mutual_exclusion_spec.spl`
- `test/integration/app/sj_daemon_mutual_exclusion_spec.spl`

No rename had occurred, so the re-run is against the intended file.

**Command** (detached `nohup setsid` + sentinel, never wrapped in `timeout`):

```
bin/simple test test/02_integration/app/sj_daemon_mutual_exclusion_spec.spl
```

**Binary identity** — recorded before AND after; byte-identical across the run,
so the result does not span a redeploy:

```
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
59621024 2026-08-17 20:28:24.151268554 +0000
```

(Still the Rust seed, per `.claude/rules/commands.md`.)

**Result** — quoted verbatim:

```
Results: 5 total, 4 passed, 1 failed
```

The single failure is **exactly** the example this record names in `Blocks:`,
and no other:

```
sj daemon - exclusion survives the by-value SjClient caller chain
  ✗ sees the lease through SjClient -> fallback_exec -> handle_cli_args
    expected 0 to equal 75
  ✓ NEGATIVE CONTROL: same chain with no lease held is NOT 75
```

### This is the class-aliasing signature, not something else

The failure matches the documented shape precisely rather than merely being red:

- The lease is acquired through `client.handler.lease_manager`, then
  `fallback_exec(client.handler, ...)` returns `exit_code 0` instead of `75` —
  the mutation is not observed through a second read of the same field. That is
  the `D4` row of the "Production consequence" table above (`D4.fallback_exit=0`),
  reproduced unchanged.
- Its paired **negative control passes**, so the example is not satisfiable by a
  handler that answers `0` unconditionally; the two examples still discriminate.
- The three examples that never depended on this defect (direct-handler
  exclusion, its control, lease release) are all still GREEN — matching "Why the
  spec is left RED, not softened" exactly. A general regression would not leave
  precisely those three green and precisely this one red.

So this is **deliberately-red-on-purpose still being red**, not a new regression
and not a different defect. The distinction matters: nothing here says the tree
got worse; it says the closure was never checked against the artifact it blocks.

### What would resolve the contradiction (neither side is decidable alone)

1. Re-run the closure's minimal fixture and this spec **on one stated binary in
   one session**, recording the engine lane explicitly. The 2026-08-17 fixture
   run does not state whether it ran interpreter or JIT; this record's whole
   claim is an interpreter/JIT *divergence*, and `bin/simple test` does not print
   its execution lane in the spec log. A fixture that passed under JIT would be
   consistent with this spec failing under the interpreter and would dissolve the
   contradiction without either observation being wrong.
2. If both are on the same lane, extend the minimal fixture toward the spec's
   real shape (field read passed as a **call argument**, not just bound and
   mutated in the same frame) until it flips — the delta that flips it is the
   actual remaining defect.
3. Only then re-adjudicate the status line. Do not close on the fixture alone
   again, and do not reopen on this run alone.

Not done here, deliberately: the spec was **not edited**, no source was changed
to make anything pass, and the disposition line above was **not flipped**.
