# Native lane: `rt_enum_discriminant` returns the constant 1337030607 for every receiver shape

Status: **OPEN** — measured, unfixed. Makes a live recovery branch in MIR lowering dead code.
Date: 2026-08-17

## Symptom

Under `native-build`, `rt_enum_discriminant(receiver.kind)` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1069` returns
the value **1337030607** — the same garbage constant — for *every* receiver
shape fed to it. It never returns a small tag index, and in particular never
returns the `-1` that the code downstream is written to expect.

## Measurement (not inference)

A probe print added to the unresolved-static arm during the
`undefined variable Widget` investigation emitted, verbatim:

```
unresolved-static method=stat srn='' disc=1337030607 found=false
```

`srn=''` is the separate owner-recovery defect fixed in `b9a68e7eebd`.
`disc=1337030607` is this defect, and is independent of it: the constant is
returned regardless of whether the receiver is a `NamedVar`, a `Var`, or
anything else.

## Consequence — a dead recovery branch

`method_calls_literals.spl:2752`:

```simple
if static_method_id == nil and (static_receiver_kind_disc < 0 or static_receiver_name == ""):
```

The `static_receiver_kind_disc < 0` disjunct is the "we could not identify the
receiver kind, fall back" recovery path. Because the call always yields a large
POSITIVE integer, that disjunct is **never true on the native lane**. The
branch is reachable today only via the second disjunct
(`static_receiver_name == ""`), which is a different condition testing a
different thing. The comment already parked at lines 2711-2712 records the
assumption this defect violates.

This is a fail-open shape: the guard does not report that it cannot identify
the receiver kind, it silently claims it can.

## MECHANISM — largely explained by an already-filed row (added 2026-08-17)

`doc/08_tracking/bug/rt_enum_discriminant_is_enum_id_blind_name_hash_2026-08-08.md`
documents, with a measured truth table, that `rt_enum_discriminant(v)` returns
`hash_variant_discriminant(<variant name>)` — a Rust `DefaultHasher` over the
**variant name string**, truncated to 32 bits — and that it returns `-1`
**only** for a value that is not a `HeapObjectType::Enum`.

That reframes this row substantially, and the reframing is better supported
than the original "garbage" wording:

- **1337030607 is almost certainly not garbage.** It has the exact shape of the
  values in that row's measured table (`465620071`, `3803938095`, `810919283`,
  `1457792540` — all large positive 32-bit name hashes). It is most likely the
  name hash of whichever `HirExprKind` variant the receiver actually is.
- **The `< 0` guard is therefore unreachable by DESIGN, not by corruption.**
  `-1` is reserved for "not an enum at all". A well-formed `receiver.kind` is
  always an enum, so it can never be negative. The lowering code was written
  against an assumption (`-1` means "kind not identifiable") that the runtime
  contract never offered.

This makes the branch dead code just as originally reported, but it means the
fix belongs in the LOWERING code's use of the sentinel, not in the runtime
returning a wrong number.

**Still genuinely unexplained, and the reason this row stays OPEN:** the report
that the *same* constant comes back for **every receiver shape**. Under the
name-hash mechanism, different variants must hash differently. Either the probe
only ever observed one receiver variant (likely — the probe fired on a single
call shape, `method=stat`), or something upstream is collapsing distinct kinds.
That distinction is **not measured** and should be settled by probing at least
two provably different receiver variants before anyone acts on this row.

Note also the enum_id-blindness in that same 2026-08-08 row: `HirExprKind` is
explicitly listed among the collision-eligible families, so two different enum
families sharing a variant name (`Named`, `Tuple`, …) yield identical
discriminants. `method_calls_literals.spl:1180-1181` compares two discriminants
directly and is exactly the shape that trap targets.

## Scope of what is verified

- **Verified:** the returned value is 1337030607, on the native lane, for the
  receiver shapes exercised by the `Widget.stat(2)` repro.
- **NOT verified:** whether the interpreter lane is affected; whether the
  constant varies across builds or is stable; whether `rt_enum_discriminant`
  is wrong at the runtime boundary (an `Any`-erasure/tag-read defect) or is
  being handed an already-corrupt `receiver.kind`. No one has read the emitted
  code for this call site.
- **NOT verified:** whether any *other* `rt_enum_discriminant` call site is
  equally affected. Note `method_calls_literals.spl:1180-1181` compares two
  discriminants to each other — if both are the same garbage constant, that
  comparison silently returns `true` for unrelated types. This is an untested
  hypothesis, listed so it is not forgotten, not a finding.

## OPEN cross-reference — shared root is a QUESTION, not a conclusion

A live stage-3 blocker has the same *failure signature*: a garbage positive
integer appearing where a small tag or index belongs. There, an enum-payload
dependency lookup resolves to an arbitrary unrelated symbol via
`self.symbols.symbols[existing_raw]` — a bracket read on a class-field `Dict`
with class-typed values, reached through chained `self` hops, which is a
documented open native-codegen `Dict` gap (see
`doc/07_guide/language/dict_native_pitfalls.md`).

**Whether the two share a root cause is OPEN and unproven.** Signature
similarity is not identity: one is an `Any`-erased enum tag read, the other a
class-field `Dict` bracket read, and no evidence has been gathered that links
them. Do not treat them as one bug. The reason to record the cross-reference at
all is that if a single erased-value/tag-decode defect *is* underneath both,
fixing it clears two lanes — and if it is not, someone should be able to see
quickly that the question was asked and left unanswered.

## Repro pointer

Fixture and lane: `scripts/check/check-native-trailing-default-param.shs`
(static-method call shape); the `Widget.stat(2)` case in that fixture is what
drove the probe.

## Fix direction (not attempted)

Do not paper over this by changing `< 0` to some other sentinel test — that
hides a runtime defect behind a lowering workaround. `rt_enum_discriminant`
must either return a real discriminant or a documented failure value.
