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

---

## 2026-09-04 (second session): the transport print was NEVER swallowed, and the producer is TUPLE element types

### 1. The "swallowed" print actually ran — it rendered as an EMPTY LINE

Not a codegen swallow, not a guard problem. In the untruncated worker stderr
`build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage3-tmp/native-build-stderr-354080.log`
there are **exactly 16 blank lines in the whole 483,113-byte file**, at lines
3972, 3974 … 4002 — strictly alternating 1:1 with the 16
`[post-mono-verify] unhandled HirTypeKind variant at walk_type` lines, and
bounded by `[mono] …` (3971) and `phase4:monomorphize:done` (4004). Each blank
immediately PRECEDES its report, which is exactly the source order of
`post_mono_verify.spl:222-224`. The arm ran; the formatted string collapsed to
"". Do not spend another session hunting a dropped `print`.

Ruled out as the collapse mechanism, by native-built probes (admitted Stage 2,
`/tmp/zkprobe/probe{,2,3,4}.spl`): a faithful 27-variant-enum replica of the
whole `walk_type` shape (recursive payloads, real arm bodies, same field order,
same format string) prints correctly; nil interpolation prints the literal parts;
symbol lengths 16…16384 and `$ % s % n` in the symbol print correctly. The
collapse is value/state-dependent, not structural. Instrumentation hardened at
`post_mono_verify.spl:222-236`: a literal-only marker line first (cannot
collapse), then receipt and symbol on separate lines.

### 2. A 30-second reproducer that needs NO bootstrap

```
SIMPLE_BOOTSTRAP=1 SIMPLE_RUNTIME_PATH=<stage2-runtime-authority> \
  build/bootstrap/stage2/<triple>/simple compile --format=smf <file>.spl -o /tmp/x.smf
```
Run from the repo root. This reproduces BOTH symptoms — the 16 capped
`[post-mono-verify]` reports AND `E-MIR-TYPE-ZeroKind` — in ~31 s. Note the
verifier that runs is the one baked into the Stage-2 binary, so source edits to
`post_mono_verify.spl` do not take effect here; the INPUT is the free variable.

### 3. The producer: tuple destructuring and tuple element access

The Stage-2 transport receipts name the owning symbols (this is the first time
this defect has ever been localised to a function). On the real closure they are
`file_ops.spl._file_shell_{bool,int,output}` (4 each),
`signal_stubs.spl.{signal_dispatch_pending,_store_signal_handler}`,
`parser_types_expr.spl.tensorsuffix_from_string` — every one of them a tuple
destructure or `.N` tuple access.

Minimal reproduction (`/tmp/zkprobe/tup{,2,3}.spl`, 20 lines each) gives an exact
count law:

| construct | malformed HirTypes |
|---|---|
| `val t = three()` (bind only, no destructure) | **0** |
| `t.0` / `t.2` tuple index | **1** per access |
| `val (a,b) = (1,2)` literal destructure | **2** (= N names) |
| `val (a,b,c) = ("x","y",7)` literal destructure | **3** (= N names) |
| `val (a,b,c) = f()` call destructure | **4** (= N names + the `__tuple_destr` temp Let) |
| `val (a,b,c) = t` where `t` is a **parameter** | **4** |

`E-MIR-TYPE-ZeroKind` fires on the same functions in the same runs
(`scope-tail:…zz_c_field0`, the tuple-index probe), so the ZeroKind fatal and the
post-mono `case _` are consistent with the same corrupt object seen at two
stages.

Relevant code: `src/compiler/20.hir/hir_lowering/statements.spl:295-345`
(`lower_tuple_destructure`, `td_elem_types`, `td_idx_type`),
`statements.spl:198-253` (literal fast path), the element-type tables
`local_tuple_types` / `fn_tuple_returns`
(`statements.spl:104,308-309,328-329`; `expression_support.spl:200-201`;
`module_declarations_bootstrap.spl:157`). The parameter row above is the sharp
one: there `td_elem_types` is empty and every `td_idx_type` is `nil`, yet 4
malformed types still appear — so this is NOT a bad readback out of those Dicts,
and it is NOT "a producer forgot to write `kind`" either. Something downstream
materialises a per-binding `HirType` for a tuple element as a ZEROED aggregate
(`disc=-1`, `kind` raw 0, span non-nil/non-zero/undereferenceable) rather than
leaving it absent — `walk_type` early-returns on a true `nil`, so a genuine nil
would report 0.

### 3a. MECHANISM (measured): the Rust seed's aarch64 codegen materialises
`Optional<struct> = nil` as a NON-NIL zeroed aggregate

One probe, `/tmp/zkprobe/opt.spl` (~30 lines: a `Ty?` local, a `Ty?` enum
payload, `[Ty?]`, a `Dict<i64, Ty?>` miss), built twice from BYTE-IDENTICAL
source and run on this host:

| slot | built by Stage 2 (pure-Simple codegen) | built by the **Rust seed** |
|---|---|---|
| `val direct: Ty? = nil` | nil-ok | **NON-NIL** |
| enum payload `SKind.Let(_, ty: nil, _)` read back | nil-ok | **NON-NIL** |
| `[Ty?] = [nil, nil]` element read back | nil-ok | **NON-NIL** (x2) |
| `Dict<i64, Ty?>` miss | nil-ok | nil-ok |

Seed recipe (the runtime path must be the ARCHIVE, not its directory, or the
link fails):
`SIMPLE_BOOTSTRAP=1 SIMPLE_RUNTIME_PATH=build/bootstrap/stage3/<triple>/stage2-runtime-authority/deps/libsimple_runtime.a src/compiler_rust/target/bootstrap/simple native-build --source src/app/cli --source src/lib --entry-closure --entry <probe> -o <out>`

This is the mechanism, and it closes every open thread in this record:

- The running Stage-2 compiler is machine code the **Rust seed** generated, so
  its `HirType?` slots behave this way. `lower_tuple_destructure` writes a
  literal `nil` type into the `__tuple_destr` temp Let and into every element
  Let whose type it cannot resolve — each of those reads back as a non-nil,
  all-zero `HirType`.
- `walk_type`'s `if ty == nil: return` therefore does NOT fire, the match runs
  on a zero `kind`, and `case _` is taken: **1 report per nil `HirType?` slot**,
  which is exactly the count law in the table above.
- `lower_type` sees the same object and raises `E-MIR-TYPE-ZeroKind`
  ("`kind` field is raw 0"). `kindzero=true / kindnil=false`, `disc=-1`, and a
  span that is neither nil nor zero yet cannot be dereferenced are all just
  descriptions of a zeroed aggregate.
- x86_64 self-hosts while both aarch64 hosts fail — consistent with an
  AAPCS64-specific by-value Optional-aggregate representation in the seed.
- The 2/4/6 variation across byte-identical runs is whatever lands in the
  discriminant byte, not a set of source sites.

The fix therefore belongs in `src/compiler_rust/**` (seed aarch64 codegen for
`Optional<aggregate>`), which is outside this session's scope. A defensive
`.spl`-side mitigation is possible — never store a bare `nil` into an
`HirType?`/`HirStmt` type slot — but it treats a symptom that will resurface
anywhere else a nil Optional-of-struct crosses a seed-generated boundary.

### 4. Bonus corruption signal, same runs

Two byte-identical runs of the same command emitted
`E-SFFI-016: missing return in non-unit function 'flag_template' at :29:46` and
`… function 'walk_interpolations' at :29:46` — same location, DIFFERENT function
name. A name read from a wrong slot is the same layout-attribution class this
record describes, and it is a second, cheap handle on it.

### Codegen attribution — read this before quoting any "ruled out" above

Probes built with the Stage-2 binary exercise **Stage 2's pure-Simple driver
codegen**, NOT the seed codegen that generated the running compiler. Every
negative result in §1 (interpolation, nested guarded print in a `case _`, string
length, special characters, the 27-variant `walk_type` replica) is therefore a
statement about Stage-2 codegen only. §3a is the counter-example that proves the
distinction matters: the identical probe passes under Stage 2 and fails under the
seed. The input bisection in §3 is unaffected — it feeds the real running
compiler — so the count law and the owner symbols stand.

Equally: the 30-second reproducer's only free variable is the INPUT. The verifier
and the HIR lowering it runs are baked into the Stage-2 binary, so editing
`post_mono_verify.spl` or `statements.spl` changes nothing there (confirmed: after
this session's edit, the reproducer still printed the OLD single-line transport
format). Compiler-side instrumentation needs a Stage-2 rebuild.

### Next step

Fix `Optional<aggregate> = nil` in the Rust seed's aarch64 codegen
(`src/compiler_rust/**`) so a nil Optional of a struct reads back nil, and
re-run the 30-second reproducer on `/tmp/zkprobe/tup2.spl`: the count law
predicts every report and every `E-MIR-TYPE-ZeroKind` disappears.

## After the `Optional<aggregate>` codegen fix (2026-09-04, later)

`fix(codegen): stop turning a nil Optional<aggregate> into a zeroed aggregate`
was applied to `emit_aggregate_block_copy`
(`src/compiler_rust/compiler/src/codegen/llvm/functions/objects.rs`), the seed
was rebuilt, Stage 2 was rebuilt by it and re-admitted, a fresh planner receipt
was produced, and Stage 3 was run again — the last time with the machine to
itself.

**The ZeroKind class is gone.** Across every run after the fix, in the
untruncated worker stderr:

    E-MIR-TYPE-ZeroKind      : 0   (was 3)
    [post-mono-verify] ...   : 0   (was 16)

Stage 3 nevertheless still does not complete, and the remaining failure is a
DIFFERENT and much more ordinary one:

    [ERROR] phase 3 FAILED
    HIR lowering error in src/compiler/driver/driver_compile_vhdl_expr.spl:
      unresolved name: _is_decimal_digit

That name is not missing from the source. It is defined at
`src/compiler/80.driver/driver_compile_vhdl_util.spl:17` and is explicitly
imported by the failing file at `driver_compile_vhdl_expr.spl:14-15`
(`use compiler.driver.driver_compile_vhdl_util.{ _is_decimal_digit, ... }`), the
same way three sibling files import from that module. So this is a
name-resolution failure in the compiler, not a source defect, and it is the next
thing to chase.

### The open question the next session must settle FIRST

Is this resolution failure NEW (introduced by the aggregate-copy fix) or
PRE-EXISTING and merely unmasked?

Evidence for "new": the run immediately before the fix reached
`phase3:hir_typecheck:done` and `phase4:monomorphize:done`; runs after it stop
inside phase 3. That is a real ordering change.

Evidence for "unmasked": phase 3 previously emitted a large number of
`[hir-reexport-chase-unresolved]` warnings whose own text says "a later
`unresolved type`/`unresolved name` will be reported against an importing module
instead". Resolution was already degraded; the corrupt-aggregate behaviour may
have been letting a failed lookup fall through to a zeroed object rather than an
error.

This was NOT determined here, and the older stage-3 stderr logs are rotated
away, so it cannot be settled by re-reading them. Settle it by reverting the
objects.rs hunk alone, rebuilding seed + Stage 2, and re-running Stage 3: if
`_is_decimal_digit` still fails, it is pre-existing.

Reviewing the hunk on its own terms: it returns the source unchanged when the
source is not `(tag == TAG_HEAP && ptr != 0)`. For the nil sentinel and for
inline specials that is strictly more correct than fabricating a zero block. The
one case that changes shape is a heap-tagged NULL pointer, which was already
malformed. No mechanism is known by which it would break import resolution — but
"no known mechanism" is not a measurement, which is why the revert test above is
specified rather than assumed away.

### Operational notes for the next attempt

- Two Stage-3 runs were REAPED WITHOUT A NORMAL EXIT ("KILLED ... NOT a compile
  failure") at ~57 minutes of worker time while a second heavy build was running
  concurrently and writing into `build/bootstrap/mcp-native-cache`. No kernel OOM
  appears in `dmesg`, worker RSS at the time was only ~9.6 GB of 121 GB, and
  `bootstrap-progress-watch.shs` states it never kills anything. Running Stage 3
  with the machine to itself produced a clean `exit 1` compile failure instead.
  Do not run a second native build inside `build/bootstrap/**` during a
  bootstrap; the cause of the kill was not identified and is worth its own
  record if it recurs.
- Stage 3 takes ~57-65 min of single-core worker time here. It is invoked with
  `--threads 20` and runs at `cpu_pct=100`; see
  `doc/08_tracking/bug/native_build_step5_serial_threads_ignored_2026-09-04.md`.
