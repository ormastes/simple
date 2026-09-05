# E-MIR-TYPE-ZeroKind: the last Stage-3 producer is the tree's only remaining omitted-Optional struct field

- **Filed:** 2026-09-03
- **Status:** FIX LANDED, UNVERIFIED ON THIS HOST (no runnable compiler here — see Verification)
- **Supersedes the "source-edit avenue is CLOSED" conclusion of**
  `zerokind_roams_between_victims_avoidance_edits_are_not_fixes_2026-09-02.md`
- **Related:** PR #274 (`a387009e6c7`), PR #295, PR #291,
  `self_hosted_symbol_table_hirtype_garbage_at_rest_2026-08-31.md`

## Symptom

Stage 3 completes `phase1:load_sources` -> `phase3:hir` (760/760, hir-fatals=0)
-> `hir_typecheck` -> `streaming_source_reclaim` -> `phase4:monomorphize` ->
`phase5:mode_dispatch`, then exits 1 with exactly TWO:

```
error: bootstrap MIR lowering: E-MIR-TYPE-ZeroKind: lower_type received a
well-formed HirType whose `kind` field is raw 0 (never written) while lowering
'scope-tail:compiler.driver.pipeline_fn.compile_specialized_template'
```

`scope-tail:` is a fixed tail label of an installed `current_function_names`
array (`function_lowering.spl:1144-1152` documents this) and names no victim.

### Proof that the label carries no module information either

This matters, because the fix below is in a module the label does not name. The
bootstrap path — and the fatal's own prefix is literally "bootstrap MIR
lowering:" — installs the list at `bootstrap_globals.spl:652` and `:776`, and in
both cases the whole-program `_bootstrap_function_value_names` is appended
**LAST**, after this module's own names:

```
        for function_name in _bootstrap_function_value_names:
            function_names.push(function_name)
        lowering.current_function_names = function_names
```

So `[len-1]` is the final entry of a **program-wide** array, identical for every
module lowered in the run. A ZeroKind raised while lowering
`driver_vhdl_artifact_build` reports exactly the same `pipeline_fn` tail as one
raised anywhere else. (`bootstrap_globals.spl:390` installs that program array
bare; `module_lowering.spl:1181` is the non-bootstrap path.)

This also explains the roaming that runs B–F mistook for progress: every one of
those runs EDITED `pipeline_fn.spl`, which reshuffled the tail of the
program-wide list — so the reported name changed while nothing about the
producer did.

## The producer

`src/compiler/80.driver/driver_vhdl_artifact_build.spl:146` constructs
`VhdlArtifactInput(...)` and omits exactly one declared field:
`assurance_policy: VhdlArtifactAssurancePolicySnapshot?`
(`driver_vhdl_artifacts.spl:100`). The module is in the compiler's own closure
(`driver_aot_vhdl_output.spl:16` imports it).

An omitted Optional field does not lower as "absent". It routes through
`lower_struct_construct`'s fill path
(`switch_operators_calls.spl:3697-3702`), which calls
`ensure_option_handle(raw_nil, field_hir_types[fi])` -- a `HirType` read out of
an ARRAY ELEMENT held in a `Dict<text, [HirType]>` and passed as an AGGREGATE BY
VALUE across a method boundary -- and then on into `remember_local_hir_type`
(`mir_lowering_types.spl:559`), by value again. That is the exact shape the
neighbouring `copy_local_hir_type_metadata` documents as unsafe under the
admitted Stage 2 native ABI ("Keep both method arguments scalar and copy the
aggregate only while it remains an element of this owner's aligned local
arrays"). The callee receives a zero-filled `HirType`: a well-formed heap object
whose `kind` slot was never written. The `!= nil` guards on that path cannot
screen it, because the nil sentinel in this runtime is raw **3**, not 0.

This is byte-for-byte the mechanism PR #274 identified and fixed for
`CompiledUnit.entry_point`. #274 cleared 4 of the original 6 occurrences; this
is the same defect at the one remaining site.

Fix: name the field explicitly (`assurance_policy: nil`), which keeps it off the
fill path entirely. That is #274's fix verbatim, not an avoidance edit: it
repairs the construction that feeds the crossing, changes no type, deletes no
use, and adds no consumer-side guard. `input.assurance_policy == nil`
(`driver_vhdl_artifacts.spl:529`) reads identically either way, so behaviour is
unchanged.

## Why this is the only candidate left (the negative results)

All sweeps ran against `origin/main` @ `dcb322dc971`, over `src/**` excluding
vendored trees, with balanced-paren parsing (not line greps) and a control count
for every zero.

1. **No source construction mints kind 0.** All **364** `HirType(...)`
   constructions in `src/compiler` supply `kind:`. The only two that do not are
   positional pattern matches (`mir_lowering_stmts.spl:237,241`), which bind
   `kind`. Of the 364, only **13** supply a non-literal `kind:` expression, and
   every one resolves through a helper that terminates in a defended arm
   (`HirTypeKind.Error` / `.Unit` / `.Infer(0,0)`): `lower_named_kind`
   (`types.spl:732`, tail `HirTypeKind.Error`),
   `hir_type_kind_from_simple_name` (`lowering_helpers.spl:515`, `case _:
   HirTypeKind.Unit`), `hc_dec_hir_type_kind` (unknown tag raises via
   `hc_bad_tag`, no fallthrough), and the already-fixed `prim_kind_v`.
   **Zero** `kind:` expressions derive from a bare `.unwrap()`, directly or one
   assignment hop away.

2. **Only one omitted-Optional struct literal remains.** Sweeping every
   keyword-style literal of every optional-bearing struct/class type in `src/`:
   **1,177 checked, 1 offender** — the `VhdlArtifactInput` site above.

3. **The `expr_dispatch.spl` rows carried forward as "known-open" are the wrong
   defect.** `:282`, `:4664/4666/4668`, `:4832/4834/4835`, `:4851/4853/4854`
   unwrap `LocalId` / unwind-target / unwind-payload / global-static optionals.
   None of them can construct or return a `HirType`, so none can mint this
   symptom. They are the same stolen-unwrap *class* as PR #291/#295, tracked
   there; they are not this bug.

4. **`substitute_type`'s dict reads were considered and dropped.** The victims
   (a stub with no generics, plus two wrappers) do not sit on the
   monomorphization substitution path, and an unconditionally corrupt
   struct-valued bracket read would fatal on essentially every specialization,
   not exactly twice.

## One fatal, two occurrences

One omission, more than one fatal, is the established ratio: #274's single
omitted `entry_point` produced **six** ZeroKind raises. `ensure_option_handle`
stores the corrupted aggregate via `remember_local_hir_type`, and every later
`lower_type` that retrieves it raises again. Two occurrences from one omitted
field is consistent with that and does not imply two sites. The evidence
supports **one site, hit twice**.

## The experiment, repaired

`function_lowering.spl:247` held the only built discriminating instrument: a
two-sided tag probe that reads the caller-side `HirType` discriminant
immediately before `lower_type(fn_.params[pmi].type_)`, separating "dead copy
minted in flight" (caller non-zero, callee 0) from "already dead upstream"
(caller 0 too).

It was scoped `fn_.name.contains("compile_specialized_template")` — that is,
scoped by the ZeroKind fatal's reported name, which lines 1144-1152 of the same
file declare is a fixed tail label and explicitly "NOT the function being
lowered". The probe could therefore only ever fire if the producer happened to
live inside those three wrappers, which is exactly the reading runs B–F of the
`zerokind_roams` record refuted five times.

The real constraint the name filter was solving is output volume (an unscoped
per-parameter print drove RSS to 10 GB in 3 minutes). This change keeps that
bound and drops the false premise: the probe now reads the discriminant for
every parameter (a cheap SFFI call, no output) and prints **only when the caller
side is already anomalous** — `_sffi_hir_type_discriminant` returns `-1` for a
non-enum argument, which is what a raw-0 or nil `kind` yields. Print count is
bounded by the number of fatals, not by 760 modules. Still default-off behind
`SIMPLE_MIR_TAG_PROBE=1`, and it still reads only the discriminant of the same
field `lower_type` is about to read, so the `:1112` round-2 hazard (reading
further fields off the corrupt object) is not reintroduced.

**The probe also had a second, independent defect: it passed the wrong
argument.** `_sffi_hir_type_discriminant` is `rt_enum_discriminant(value)`
(`function_lowering.spl:46-49`) — it discriminates its OWN ARGUMENT and answers
`-1` for anything that is not an enum. The probe passed
`fn_.params[pmi].type_`, a `HirType` **struct**, which is never an enum: that
call returned `-1` unconditionally and carried no information whatsoever. So the
one remaining instrument was both scoped by a meaningless name AND reading a
constant. It now passes `.kind` — the enum — mirroring the two existing correct
uses at `:1189` (`type_.kind`) and `:735` (`kind`). Without that correction the
new anomaly filter would have matched every parameter of every function and
reproduced the exact 10 GB flood the old name filter existed to prevent.

Run it with `SIMPLE_MIR_TAG_PROBE=1`. If the fix above is correct the probe
prints nothing and Stage 3 proceeds. If ZeroKind persists, the probe now names
the real module, function, parameter index and parameter name in ONE run.

## Verification

**What was verified:** every claim above about tree content, by balanced-paren
parsing of `origin/main` @ `dcb322dc971`, each zero paired with a control count.

**What was NOT verified: the fix was not executed.** No proof was possible on
this host. All five tracked `bootstrap/*/simple` binaries are the same 126 KB
stub (a fixture referencing `NoSuchTypeXYZ` exits 0); `bin/simple` is the
bootstrap CLI and exposes neither `test` nor `lint`; and
`bin/release/aarch64-apple-darwin/simple` cannot parse the current stdlib
(`always_inline`). No bootstrap was run, per instruction. The next Stage-3 run
is the verification, and the repaired probe is the instrument if it fails.

---

## Addendum 2026-09-03: the fix did NOT clear it, and the probe watches the wrong path

### The `assurance_policy: nil` fix is landed and did not resolve the class

Verified present in the build tree that ran (`grep -c 'assurance_policy: nil'` = 1
in `driver_vhdl_artifact_build.spl`). Three subsequent Stage-3 runs on trees
carrying it still raise `E-MIR-TYPE-ZeroKind`:

| run | log bytes | zerokind |
|---|---|---|
| 5e93b8217ee | 8,961,364 | 6 |
| 5e93b8217ee (repeat) | 8,922,206 | 2 |
| 68c4b6cc165 | 8,922,496 | 2 |

The count varies between 2 and 6 across runs on IDENTICAL source. That
instability is itself unexplained and should not be hand-waved: it means the
producer is order- or state-dependent, not a fixed set of source sites.

The omitted-Optional site was a real instance of the shape and the explicit
`nil` is correct on its own merits. It was not the blocker.

### `probe lines=0` is a MEANINGFUL NEGATIVE, not a broken probe

Three runs reported `probe lines=0`. Two distinct causes were found and fixed
before the number could be trusted at all:

1. **The variable never reached the worker.** Stage 3 builds its environment from
   an explicit `env VAR=...` allowlist; `SIMPLE_MIR_TAG_PROBE` was absent, so an
   exported value was silently dropped. Fixed in PR #327. (Second time this
   allowlist swallowed this exact variable in this arc.)
2. **The probe is instrumented on the wrong crossing.** It sits at
   `function_lowering.spl:245`, inside the SIGNATURE-parameter path
   (`param:{pmi}`, `signature_param_type`). The producer identified by this
   record's own analysis is the STRUCT-CONSTRUCT fill path
   (`lower_struct_construct` -> `ensure_option_handle` ->
   `remember_local_hir_type`). The probe cannot see that site.

Truncation was ruled out: the FULL 501,657-byte stderr file also contains zero
probe lines, so the absence is real and not a logging artifact.

**Therefore the correct reading of `probe lines=0` is: the kind-0 HirType does
not arrive via a function signature parameter.** That is a genuine elimination,
and it is consistent with the fill-path hypothesis rather than against it.

### What the next investigation should do

Instrument where the fatal is actually RAISED (inside `lower_type`, at the
`kind == 0` detection) rather than at one suspected crossing — the raise site
sees every producer, a crossing sees only its own. Print the enclosing
construct/site identity there, bounded by fatal count.

Do NOT re-run stage 3 to "see if the probe fires" without first confirming the
probe is on the path under test. Three ~65-minute runs were spent on a probe
that could not observe this defect.
