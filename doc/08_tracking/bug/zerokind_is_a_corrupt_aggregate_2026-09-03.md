# E-MIR-TYPE-ZeroKind is a CORRUPT AGGREGATE, not an unset field

**Status:** OPEN — root cause characterised, fix not yet identified
**Filed:** 2026-09-03
**Severity:** P0 — sole remaining blocker for Stage-3 self-host on aarch64-apple-darwin

## Why this record exists

Five separate hypotheses were pursued and refuted before the defect was measured
directly. All five asked the same wrong question — *"which construct forgot to
write `kind`?"* — because the fatal's own text says "the `kind` field is raw 0
(never written) ... fix the PRODUCER that left kind unset". The measurement says
the object is bad wholesale, so that guidance sends every reader down the wrong
path.

## The measurement

Raise-site probe (`function_lowering.spl`, gated by `SIMPLE_MIR_TAG_PROBE=1`),
live on an 8,924,312-byte Stage-3 log:

```
[mir-zerokind-raise] seq=1 module= disc=-1 kindzero=true kindnil=false
                     spannil=false spanzero=false scope_hint=scope-tail:...
[mir-zerokind-raise] seq=2 ... identical
```

| field | value | reading |
|---|---|---|
| `kindzero` | true | `kind` is raw 0 |
| `kindnil` | **false** | genuinely zeroed, NOT absent |
| `disc` | **-1** | not a valid `HirTypeKind` discriminant |
| `spannil` / `spanzero` | false / false | span passes BOTH `== nil` and `== 0` |
| span deref | **silently swallowed** | …yet cannot be read |
| `module` | **empty** | `current_module_id` unset at the raise |

`at=` appears **ZERO** times — in that log and in the 492,027-byte full stderr —
while the run continued and exited normally. The second staged line was
swallowed mid-`eprint`.

## The conclusion

A pointer that passes both nil-checks and still faults on read is a **dangling
read**. Combined with `disc=-1` and an empty module id, the whole `HirType` is a
corrupt aggregate. It is NOT a producer that forgot one field.

This is independently corroborated by the file's own prior finding, recorded
above the probe: *"Round 2 REVERTED (2026-08-30) ... round 1 had already PROVEN
this object is corrupt (`kind` is not an enum, disc=-1), so dereferencing further
fields of the same object is not a safe read."* Two independent investigations,
a month apart, reached the same conclusion.

## Hypotheses refuted (do not re-run these)

1. **`aop: Any` in `pipeline_fn.spl`** — rested on reading the scope-tail label as
   the offending function. That label is a program-wide CONSTANT
   (`bootstrap_globals.spl:652/:776` append the whole name list last), identical
   for every raise. It localises nothing.
2. **Quadratic `rt_transient_heap_promote`** — promote has ONE call site inside
   `parse_all_streaming_surfaces_in_place_impl`, which runs once over the file
   set. Retracted.
3. **Stolen `unwrap` at `expression_core.spl:50`** — was a REAL defect of that
   class and the `if val` fix is correct, but ZeroKind persisted after it.
4. **Omitted Optional at `driver_vhdl_artifact_build.spl:146`** — also real, also
   fixed (`assurance_policy: nil`), also did not clear the class.
5. **Signature-parameter transport** — the param-path probe reported ZERO lines
   across a run that raised the fatal, with truncation excluded. Genuine
   elimination: the kind-0 HirType does not arrive via a signature parameter.

## Also unexplained, and load-bearing

The fatal count **varies between 2 and 6 across runs on byte-identical source**.
A fixed set of source sites cannot do that. Whatever produces the corrupt
aggregate is order- or state-dependent, which is itself a strong hint and should
not be dismissed as noise.

## What the next investigation should do

Stop looking for a producer that omits a field. Look for where a `HirType` is
COPIED or TRANSPORTED such that the destination is not a valid object — a
by-value aggregate crossing, a reclaimed/reused buffer, or a cache returning a
freed slot. `phase3:streaming_source_reclaim` runs immediately before the phase
that raises and reports `sources=760 owners=0`; the relationship between that
reclaim and MIR-lowering's retained `HirType`s is unexamined.

Diagnostic wording should also be corrected: "the PRODUCER that left kind unset"
asserts a cause that the evidence contradicts.

## Reproduction

Stage 3 on aarch64-apple-darwin reaches `hir 760/760` (0 fatals), passes
`phase4:monomorphize`, enters `phase5:mode_dispatch`, then raises 2-6 of these
and exits 1. Requires ~30 GB free disk sustained for ~90 minutes; below that the
run dies with `os error 28` before reaching the fatal.

---

## CONFIRMED 2026-09-03 (second run, probe fully functional)

The earlier reading rested on ONE swallowed line. After removing the unsafe span
deref (#337) the probe emits both staged lines cleanly, and the finding now holds
across EVERY raise rather than being inferred from an absence:

```
[mir-zerokind-raise] seq=1 module= disc=-1 kindzero=true kindnil=false
                     spannil=false spanzero=false
[mir-zerokind-raise] seq=1 span=non-nil-non-zero-but-UNDEREFERENCEABLE
[mir-zerokind-raise] seq=2 ... identical
[mir-zerokind-raise] seq=3 ... identical
```

6 probe lines / 3 raises, on an 8,930,201-byte log with `hir-fatals=0`. The
corrupt-aggregate conclusion is now measured, not deduced.

## NEW SIGNAL: `module=` is EMPTY on every raise

`self.current_module_id` renders as the empty string at the raise point, in all
three cases. That field is a plain `MirLowering` member (`mir_lowering_types.spl:61`)
and is `eprint`ed successfully elsewhere in the same file, so this is not a
formatting artefact — the lowering context genuinely has no module id set when
the fatal fires.

Taken together — `disc=-1`, an undereferenceable span, AND an empty module id —
the evidence points at the **MirLowering context itself** being in an invalid
state at this point, not merely one bad `HirType` flowing into a healthy lowering.
That is a materially different target from "find the construct that produced a
bad type", and it is where the next investigation should start:

- who sets `current_module_id`, and can the raise be reached on a path where it
  was never set (or was reset)?
- is this lowering reached via a route that skips normal per-module setup?
- does the same route explain how a `HirType` with a garbage span reaches it?

## Still unexplained

The count varies 2 / 4 / 6 across runs on byte-identical source. An
order-dependent or state-dependent producer remains the best explanation, and it
is consistent with a context-initialisation defect rather than a fixed set of
source sites.
