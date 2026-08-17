# The engine-divergence guard hardcodes `bin/simple`, so it cannot see divergences

**Status:** OPEN (P1)
**Filed:** 2026-08-17
**Component:** `test/01_unit/engine_divergence/check-engine-divergence-probes.shs`
**Class:** vacuous guard — it passes by construction, and rows were retired on it

## Symptom

The guard pins its binary at line 37:

```
SIMPLE="$ROOT/bin/simple"
```

`bin/simple` is the **Rust seed built 2026-08-16 22:59**, not a binary built from
current source. So the guard reports on the seed's behaviour no matter what the
tree contains, and a divergence introduced or exposed by current source is
invisible to it.

## Measured

`probes/alias_value_semantics_probe.spl`, with `SIMPLE_EXECUTION_MODE` pinned,
across three binaries:

| binary | interp | jit |
|---|---|---|
| `bin/simple` (stale seed, 2026-08-16 22:59) | 777 | 777 |
| fresh build (08:33) | **42** | **777** |
| fresh build (09:37) | **42** | **777** |

A real interpreter/JIT divergence, reproduced on **two independent** fresh
builds — so it is not an artifact of one build. The stale seed shows `777/777`
and the guard duly reports `PASS — 5 probes, 0 divergences`.

`42` is the exact value documented by the drop-characterization row that was
retired on this guard's green.

## Consequence: four rows were retired on evidence that cannot exist

Commit `e21824a4ed4` retired 4 rows — including
`struct_field_aliases_under_jit` and `jit_class_mutation_drop_characterization`
— citing `PASS — 5 probes, 0 divergences`. That PASS is structurally incapable of
being anything else while the binary is hardcoded to a stale seed.

**Those 4 rows should be reopened.**

## Why this is the worst shape of guard failure

A guard that fails loudly wastes time. A guard that **passes by construction**
retires real defects and leaves a green audit trail behind them. This one sits
directly on the axis the campaign was hunting: the same source is correct under
one engine and wrong under the other, and three separate lanes mis-attributed
JIT-only defects to the interpreter today because a bare `bin/simple run` JITs.

## Fix direction

Make the binary injectable — `SIMPLE="${SIMPLE_BIN:-$ROOT/bin/simple}"` — and
have the guard REFUSE to pass when the binary it used is older than the newest
source file it is probing, reporting `ERROR — nothing was checked` (exit 2)
rather than a green. Absence of a current binary is absence of evidence.

## Open question, deliberately not answered here

The two engines disagree (`interp 42` vs `jit 777`); which one is **correct**
under the language's alias/value semantics has not been established. The
reopened rows need that decided before either engine is called the defect.

## Not verified

- Whether the other 4 probes in the suite would also diverge on a fresh binary
  (only `alias_value_semantics_probe.spl` was run across all three).
- Whether any other guard in `scripts/check/` or `test/**` hardcodes the same
  path; a census was not run.

Found by a read-only audit of this campaign's own results.

## ANSWERED 2026-08-17 — the INTERPRETER is the wrong one, and one retired row is misnamed

The open question above ("which engine is correct?") is settled by the probe's own
structure. `Counter` is a `class`; `SCell` is a `struct`. Arms B/C/D are all
struct and both engines agree (`0/0/0`). Arm A is the only divergence and the
only `class` case:

```
interpreter  A=42   B=0 C=0 D=0
jit          A=777  B=0 C=0 D=0
```

`var c = arr[0]; c.val = 777` must be visible through `arr[0]` if classes are
references. `doc/08_tracking/bug/struct_param_mutation_semantics_2026-07-03.md`
already treats that as settled — the "copied by default" rule "applies to
`struct`, not `class`", no document claims `class` instances are value types, and
it requires consistency "between the interpreter and the compiled/JIT path".

So **`777` is correct: the JIT is right and the interpreter is wrong**, deep-copying
a class instance on array read and dropping the mutation.

**Consequence for the reopened rows:** the row titled
`jit_class_mutation_drop_characterization` **names the wrong engine**. The JIT is
the correct one; the drop is the interpreter's. It should be retitled before it is
worked, or someone will "fix" the engine that is already behaving.

Note the direction is feature-specific, not a general "engine X is better": on
`val` block scope the divergence runs the other way — the interpreter is correct
and the JIT leaks the binding
(`jit_does_not_enforce_val_block_scope_2026-08-17.md`).
