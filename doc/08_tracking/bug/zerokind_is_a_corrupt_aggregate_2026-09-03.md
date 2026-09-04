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

## Also reproduces on aarch64-unknown-linux-gnu (2026-09-04)

Same fatal, same shape, on a second aarch64 platform:

```
error: bootstrap MIR lowering: E-MIR-TYPE-ZeroKind: lower_type received a
well-formed HirType whose `kind` field is raw 0 (never written) while lowering
'scope-tail:compiler.driver.pipeline_fn.compile_specialized_template_release'
-- fix the PRODUCER that left kind unset, not lower_type
```

Emitted 3 times, consistent with the "count varies across runs" note above. Per
this file's own warning the `scope-tail:` name is a fixed tail of a
whole-array-assigned `current_function_names` and does NOT name the offending
function; it is recorded here only to show the label is identical on this host
too, i.e. it carries no host-specific information either.

**Why this datapoint matters.** The header scopes this P0 to
aarch64-apple-darwin. It is not OS-specific: this run is Ubuntu 24.04 on
aarch64, glibc, clang/LLD 23.1.0, mold as `ld`, LLVM 18 for `llvm-sys`. The
common factor across both failing hosts is the **architecture**, not the OS or
the toolchain, while x86_64 continues to self-host. That narrows the search to
aarch64-specific lowering/codegen or an aarch64 ABI assumption, and argues
against the source-level "which construct forgot to write `kind`" framing that
this record already refuted on other grounds.

**This run was not confounded by the stub defect fixed the same day.** Stage 2
here was built strict: its native-build log reports `Generating 1 compatibility
aliases for resolved symbols` (not fabricated stubs), and the admitted Stage-2
binary carries `U bcmp` — resolved from libc, not a weak stub. See
`fix(native-build): stop weak-stubbing 58 real libc symbols`. So the corrupt
aggregate is upstream of that defect, not a consequence of it.

Environment and evidence:

- Stage 2 admitted and independently verified non-vacuous (152 MB, 515 dynamic
  symbols, reports `simple-bootstrap 1.0.0-rc.1`, not the seed banner).
- Full worker stderr (487,854 bytes, untruncated):
  `build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage3-tmp/native-build-stderr-294420.log`
- The copy in `logs/aarch64-unknown-linux-gnu/stage3-native-build.log` is NOT
  usable for this: `SIMPLE_COMPILER_PHASE_PROFILE=1`, set unconditionally for
  the Stage-3 run by `scripts/check/lib/bootstrap-stage3/runner.shs:83`, turns
  on the `[mir-lower]` trace, which produced 9,955,950 bytes of stderr; the
  native-build entry then dropped 9,943,950 bytes **from the middle** — taking
  the three `error:` lines with it. The diagnostic that survives is the one in
  the separately-saved full stderr. A trace whose volume evicts the error it
  exists to surface is worth fixing independently of this bug.

## PARTIAL FIX (2026-09-04): the ZeroKind fatal is gone; corruption is not

Commit "fix(mir): set current_module_id on the lowering paths that skip
lower_module" sets `current_module_id` on the three BOOTSTRAP-FLAT paths in
`bootstrap_globals.spl` and on the lambda-lift sub-lowering in
`switch_operators_calls.spl`. Before it, `lower_module` was the ONLY assignment
of that field, and none of those four paths call it — so a bootstrap build,
which is what Stage 3 is, ran the entire lowering with the `""` initialiser.
That is the "empty module id" this record measured at every raise and listed as
its open question.

**Measured effect on aarch64-unknown-linux-gnu, same tree, same command:**

| | before | after |
|---|---|---|
| `E-MIR-TYPE-ZeroKind` raises | 3 | **0** |
| furthest phase reached | died in `[mir-lower]` of the entry module | `phase3:hir_typecheck:done` → `phase4:monomorphize:start/done` → `phase5:mode_dispatch:start` → `aot:lower_to_mir:start` |
| Stage 3 result | fail | fail (later, different symptom) |

So the fix is real and load-bearing — it clears the fatal this record is named
for and carries the build through monomorphization — but it is **not** the whole
defect.

### What is still wrong, and why it matters for the next session

Stage 3 now fails after `aot:lower_to_mir:start`, and 16 instances of

    [post-mono-verify] unhandled HirTypeKind variant at walk_type

appear first. That walker is deliberately written without a semantic wildcard
and names all 27 `HirTypeKind` variants, and its `case _` carries the comment
"The value reaching this arm is already malformed". So **a malformed HirType
still reaches post-mono verification** — the corrupt aggregate is not
eliminated, only displaced past MIR lowering.

Two readings, and they have different fixes:

1. `current_module_id` was one of several inputs to the wrong-layout path, and
   another remains.
2. The corruption has a different source entirely, and the empty module id was
   an independent defect that happened to make it fatal earlier.

Evidence that would separate them, cheaply, next time: the transport-receipt
print in that `case _` did NOT fire (0 occurrences in BOTH the stage-3 build log
and the untruncated worker stderr) even though the arm ran 16 times. This is not
a limit or counter problem — both prints sit on the same path under the same
guard (`transport_receipts < 16`, incremented only inside `hit_unreachable`), so
if the guard admitted the 16 `unreachable_variant` prints it admitted the
transport print too.

**Ruled out by direct probe on this host (native-built by the admitted Stage 2,
so the same codegen that runs the verifier):**

- string interpolation of a plain field, of an arithmetic expression
  (`{self.n + 1}`), of a module-level `val`, and of several in one string — all
  print correctly;
- a guarded `print` nested inside an `if` inside a `case _` arm of a `match`,
  followed by a method call that mutates the receiver — prints correctly, twice,
  with the counter advancing as expected;
- a Rust-side emitter of the same text — none exists (`grep` over
  `src/compiler_rust/**`, vendored code excluded); the line matches the Simple
  source byte for byte.

So the swallow is narrower than "print does not work in that position". The
remaining differences between the two prints are the `{self.symbol}` (`text`
field) interpolation and the receiver's state at that moment — note the verifier
holds a `Dict<i64, text>` field, and the object being walked is already known to
be malformed. That this specific diagnostic vanishes while its neighbour
survives is the same "silently swallowed mid-eprint" signature recorded in
`function_lowering.spl`'s round-2 comment, which is itself evidence about the
receiver rather than about `print`.

Fixing that instrumentation is still the cheapest next step, because it is the
one probe already sited where a malformed type is known to arrive and it costs
no extra bootstrap run.

Do NOT re-derive the "which construct forgot to write kind" framing; this record
already refuted it, and the `current_module_id` finding is further evidence that
the defect is in how a type's LAYOUT is attributed, not in a producer.
