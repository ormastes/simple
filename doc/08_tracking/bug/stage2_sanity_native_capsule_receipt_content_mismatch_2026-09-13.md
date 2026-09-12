# macOS Stage 2 sanity: the smoke unit fails native-capsule receipt verification (2026-09-13)

Status: ROOT CAUSE FOUND. The receipt path is FIXED (PR #708 restored the
fix PR #702 had clobbered; PR #712 split the gate). The remaining defect is
in CODEGEN, not in this file, and now has a measured reproducer: run 9
printed `field=34363944961:runtime=632` for the same object in the same
process. See "Run 9" below. Original run-8 framing retained for history:

> This is the CURRENT macOS Stage 2 blocker (run 8) and it is a
DIFFERENT defect from the one it replaced. It fires EARLIER than run 7's — in
`native_compile`, before any link — so run 7's `Linking failed: nil` site is no
longer reached.

## Verdict, verbatim (run 8)

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
error: native capsule collection failed -- module, tag and detail follow
scripts.check.cert.redeploy_gate.fixtures.hello_world
native-capsule-receipt-invalid
receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648
error: in-process native-build: build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s) — ERROR: scripts.check.cert.redeploy_gate.fixtures.hello_world
error: Stage 2 bootstrap compiler sanity failed
warning: stage2 native-build failed (exit 2); Stage 3/full CLI unavailable
```

Rejected Stage 2 candidate (preserved, not deployed):
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`

Stage 2 itself built clean again; the failure is entirely in the smoke build the
candidate performs.

## What the numbers say

`driver_native_capsule_result_reason_v1`
(`src/compiler/80.driver/driver_aot_native_output.spl:855-896`) rebuilds the
expected receipt text

```
native-capsule-result-v1\n{capsule_identity}\n{object_path}\n{fp.size}\n{fp.content_hash}\n
```

and compares it byte-for-byte with the receipt the compile step wrote. **Both
sides are 1648 bytes and they differ**, which by that function's own comment
localises the fault to CONTENT, not truncation. The only fields that can differ
at equal length are the fixed-width ones: `fp.size` (unlikely to keep the length)
and `fp.content_hash` (a fixed-width digest — the obvious candidate). That would
mean the object file on disk hashes differently at verification time than when
the receipt was written, or one of the two hash computations is wrong in the
stage-2 NATIVE binary while being right in the interpreter.

## The differing field, measured

The written receipt is on disk; its 4th line — `fp.size` — reads

```
37196932097
```

for an object file that is **632 bytes**. The 5th line, `fp.content_hash`, is
`76e16357e568394bbe191e9c9f3633f4ba8dd5c5bf8b97d725f5474936eb327a`, which is
byte-for-byte what `shasum -a 256` gives for that object. So the hash is right
and **the size is garbage** — a value around 0x8_A8xx_xxxx, the shape of a
pointer or an undecoded box, not a file size. Both sides are 1648 bytes because
both garbage values have the same digit count; they differ because the garbage
is not stable between the write and the verify.

`FileFingerprint.size` is filled by `incremental_file_size` ->
`extern rt_file_size` (`driver_build/incremental.spl:60,639`), and it is read
back through an optional bind:

```
val object_fp = FileFingerprint.from_file(capsule.object_path)
if val fp = object_fp:
    expected = "native-capsule-result-v1\n...\n{fp.size}\n{fp.content_hash}\n"
```

`rt_file_size` itself is NOT the defect: a two-call native probe built by the
seed tier (`extern fn rt_file_size(path: text) -> i64`, printed twice) returns
the true size, twice, on this host. The suspicion is therefore the
**optional-bound scalar FIELD read** (`if val fp = object_fp: ... fp.size`) in
the stage-2 native binary — the same family as the earlier optional-bound scalar
field divergence — with `content_hash`, a `text` field beside it, surviving
intact.

Not yet established, and the next steps:
1. dump both texts (not just the lengths) for this one unit and diff them — the
   differing FIELD is the whole diagnosis and the current message deliberately
   withholds it;
2. if it is `content_hash`, re-hash the object outside the compiler and see which
   of the two sides is wrong;
3. check whether `FileFingerprint.from_file` / the hash helper is another
   native-vs-interpreter divergence, which is the family this lane keeps hitting
   (`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`).

## Relationship to the link-nil blocker

Run 8 carried the link-payload hardening (PR #702: every `"" == ok` status on the
darwin link path is site-named and reported unconditionally, and the orchestrator
refuses to format a nil into `Linking failed: ...`). That hardening is **not
disproven and not proven** by this run: the failure now stops before the linker
is reached, so no `[linker-wrapper]` line and no `Linking failed:` line appears
at all. The link-nil record stays OPEN until a run gets past capsule collection.

## Reproduction

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 --full-bootstrap \
   --mode=dynload --jobs=half
```
from a worktree with a virgin evidence root. ~35 min with a cold Rust seed.

## Related

- `doc/08_tracking/bug/stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`
- `doc/10_metrics/infra/macos_bootstrap_chain_2026-09-12.md`
- PR #702

## ROOT CAUSE (2026-09-13): the fix was already written, and PR #702 reverted it

Run 8 did not disprove anything — **it executed a compiler built without the
fix.** Commit `54660c1a0d4` ("fix(driver): say HOW the AOT diagnostic was lost",
PR #702) is a **stale-snapshot clobber** of
`src/compiler/80.driver/driver_aot_native_output.spl`. It is a net
**+22 / -100** on that one file, and of its 22 added lines only 11 are its own
work (the `diagnostic_note` interpolation); the other 11 are the OLD code it
restored. What it reverted:

- `0e437dec9b1` (PR #677) — the `rt_file_size` extern and all three receipt
  sites composing line 4 from the runtime instead of `fp.size` / `materialized.size`;
- `418399c2d84` (PR #670) — the `first-diff-line=<n>:expected=…:actual=…`
  diagnostic, which is literally what this record's "next step 1" asked for.

Evidence: `git log -S'rt_file_size(capsule.object_path)' -- <file>` names
`54660c1a0d4` as the removing commit; `git log 0e437dec9b1..54660c1a0d4^ -- <file>`
is EMPTY, so #702's parent for this file was #677's commit and nothing else
intervened. `git show 54660c1a0d4 --stat` shows exactly one file touched, so
the clobber is scoped to this file and nothing else was lost.

This is the `.claude/rules/vcs.md` § "Sync must never clobber" failure mode,
disclosed here as that section requires. The receipt-verifier spec
`test/01_unit/compiler/driver/native_capsule_result_receipt_spec.spl` was left
RED on `main` by the clobber (its `first-diff-line=4` assertion had nothing to
assert against) — a standing signal that went unread.

## Fix

1. **Restored** both reverted commits' content, preserving #702's own
   `diagnostic_note` addition. Verified: zero `fp.size` / `materialized.size`
   READS remain (the 3 grep hits are the explanatory comments), and the
   `first-diff-line` verifier is back.
2. **Added a fail-closed plausibility gate**,
   `driver_native_capsule_receipt_size_reason_v1(field_size, runtime_size)`.
   Both receipt sites already take the written size from `rt_file_size`; the
   `fp.size` struct-field read of the same quantity is now passed in purely as a
   **canary**. `FileFingerprint.from_file` sets `size = incremental_file_size(path)
   -> rt_file_size(path)` (`driver_build/incremental.spl:60,640`), so the two are
   the same quantity and equality is a sound invariant, not a vacuous one.
   The gate fails closed on a negative stat sentinel, on any value >= 2^40 (a
   pointer, never a byte count), and on field/runtime divergence — turning the
   codegen miscompile into a named failure at the site that notices it
   (`capsule-receipt-size-implausible:field=…:runtime=…`) instead of an opaque
   `receipt-content-mismatch` far away.

Spec: 4 new examples in
`test/01_unit/compiler/driver/native_capsule_result_receipt_spec.spl`
("native capsule receipt size plausibility"), including the verbatim run-8
value 37196932097 against a 632-byte object. Measured on the Rust seed:
**4 examples, 0 failures**; the restored `first-diff-line=4` example also passes.

**Pre-existing RED, not caused by this change and left RED per
`.claude/rules/testing.md`:** the spec's first example calls
`driver_native_collect_capsule_result_v1` with 5 arguments (a leading
`receipt_ctx()`) while the function takes 4
(`driver_aot_native_output.spl:1033`). Byte-identical at `HEAD` before this
change, so it is spec/impl arity drift predating this lane.

### Which half of the gate is load-bearing

**The `field != runtime` inequality is the check that fires here. The 2^40 bound
is a backstop and would NOT have caught this host's pointers.** The three
measured garbage values — 37196932097 (run 8), and 53657758209 / 53657761281
(PR #677's two same-process reads) — are all ~3.7e10 to 5.4e10, i.e. **below**
2^40 = 1099511627776. Tagged aarch64 heap addresses on this host land two orders
of magnitude under that bound. Nobody may later rely on the magnitude test
alone; it exists only for a value so large it cannot be anything but a pointer,
and this defect's pointers are not that large.

## Run 9 (2026-09-13) — the canary fired, and it is the mode-matched reproducer

`--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin
evidence root, worktree `agent-a87b4c8362f754818`, carrying PR #708. Stage 1
built and admitted; Stage 2 built its 834-unit closure clean; the failure is
again entirely inside the smoke build the candidate performs — **but it is a
different failure, and it names the defect exactly.** Verbatim:

```
error: AOT compile error -- unit, reason and lengths follow on the next lines
error:   unit (bare):
scripts.check.cert.redeploy_gate.fixtures.hello_world
error:   reason (bare):
capsule-receipt-size-implausible:field=34363944961:runtime=632:<...>/object.scripts.check.cert.redeploy_gate.fixtures.hello_world.o
error:   name-len=53 reason-len=403
```

`receipt-content-mismatch` **does not appear.** What this establishes, on the
real Stage-2 artifact in the real build mode — which F45's single-entry T1
probes could not reproduce:

1. **`rt_file_size(path)` is CORRECT under `--mode=dynload --entry-closure`.**
   It returned **632**, the true byte count of the object.
2. **The optional-bound scalar field read is MISCOMPILED in that same binary,
   in the same function, on the same file.** `fp.size` returned
   **34363944961** = `0x8_0010_2001`. The same log's earlier line
   `[DEBUG] Creating codegen adapter for backend=<enum@0x80101efe0>` shows a
   live heap object at `0x8_0101_efe0` — the same `0x8_…` address space. It is
   a tagged heap pointer, not a byte count.
3. Therefore **PR #677's remedy is right and is now proven end to end**: going
   to the runtime for the value produces the correct number where the struct
   field produces a pointer. The receipt itself is sound in run 9; nothing
   garbage was written.
4. The 2^40 backstop did **not** fire (34363944961 is ~3.1% of 2^40). The
   `field != runtime` inequality is what caught it, as recorded above.

**The build stopped only because the canary is fail-closed.** Without it, run 9's
receipt would have been written and verified correctly from `rt_file_size` on
both sides. The defect is no longer in the receipt path; it is in codegen, and
it now has a measured, reproducible witness with both values named.

Stages reached: Stage 1 admitted; Stage 2 built, **not admitted**; Stage 3 not
attempted. Rejected candidate preserved at
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`.

## Run 10 (2026-09-13) — capsule collection PASSES; this record's blocker is cleared

Same command, virgin evidence root, carrying the split gate (PR #712). Stage 1
admitted; Stage 2 built its closure clean; **the smoke build got past native
capsule collection for the first time in this chain.** No
`receipt-content-mismatch`, no `native-capsule-receipt-invalid`, no
`capsule-receipt-size-implausible`. The receipt was written and verified.

The advisory canary fired **three times**, and the three lines are the clearest
statement of the codegen defect this chain has produced:

```
[receipt-size-canary] optional-bound scalar field read miscompiled: field=51251192833:runtime=632 path=<...>.o
[receipt-size-canary] optional-bound scalar field read miscompiled: field=51251189761:runtime=632 path=<...>.o
```

Same file, same process, **different field values 3072 bytes apart**
(0xBEF7A1801 vs 0xBEF7A0C01) — the identical stride PR #677 measured
(0xc7e407601 vs 0xc7e406a01). A fresh box per read. Meanwhile `runtime=632` is
stable and correct on every one of the three reads. The struct-field read is
non-deterministic; the runtime call is not.

Stages reached: Stage 1 admitted; Stage 2 built, **not admitted**; Stage 3 not
attempted. Rejected candidate preserved at
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`.

### The blocker moved to the run-7 link site

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
error: in-process native-build: LLVM native linking failed: Linking failed: no error payload from link_to_native (rendered nil); see the unconditional [linker-wrapper] prints for the failing site
```

This closes the open question in
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`: run 8 could
not reach the link, so PR #702's hardening was neither proven nor disproven.
**It is now reached, and it is RED.** Two facts for that record, not this one:

1. the orchestrator's refusal to format a nil into `Linking failed: ...` WORKS —
   the message names the condition instead of printing a bare nil;
2. but **the `[linker-wrapper]` prints the message points at do not appear in
   the log at all** (`grep 'linker-wrapper'` matches only the error line that
   references them). The hardening's own diagnostic channel is empty, so the
   failing site is still unnamed. That is the next thing to fix, and it belongs
   to that record.

### Status of THIS record

The receipt path is fixed and proven. What remains is a **codegen** defect —
optional-bound scalar (`i64`) field reads under `--mode=dynload --entry-closure`
return a fresh tagged heap pointer per read — with a standalone reproducer that
needs no bootstrap:

- binary: the **run-10** `simple.rejected` Stage 2 candidate, at
  `.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`
  inside worktree `agent-a87b4c8362f754818`, sha256
  `67c9c3a25dc6fdda945c3677e5d8a3fe4629a1cd80ac1d6d898596bb9cd049b4`.
  Use this one: it carries the ADVISORY canary, so it reaches the canary line
  and keeps going instead of aborting. Run 9's binary (sha256
  `a9e61220cb17e438a959083ebb4554138dd2bc3bd333ea8de0ee1ce6c6aeb736`,
  139044728 bytes) reproduces the same defect in blocking form, but the only
  copy was in a session scratchpad and should be assumed gone.
  **Neither is tracked in git.** If the worktree is reclaimed, regenerate with
  the Reproduction command above — the defect has reproduced on every run so
  far, so a fresh Stage 2 is a reliable source of a fresh reproducer;
- input: `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`;
- signal: the `[receipt-size-canary]` line, which names both values.

**Not established, and deliberately not guessed:** the compiler file:line that
lowers this read. A mode-flag bisect (dynload vs static, entry-closure on/off,
jobs) costs roughly one full Stage 2 build per variant and did not fit the time
budget of this lane. F45's single-entry probes do not reproduce it, and a
single-entry probe built against a stale Stage 1 snapshot fails earlier for an
unrelated reason (`unknown extern rt_env_vars`), so it is not a shortcut. The
next session should bisect from the reproducer above rather than re-derive it.

## 2026-09-13 — ROOT CAUSE NAMED: wrong field OFFSET (0 instead of 24), emitted by the RUST SEED

Two premises this record and the task framing carried are **wrong**, and they
matter for who owns the fix.

**1. "Stage 1 is a self-hosted compiler" is false.** `stage2_seed_absolute`
(`scripts/bootstrap/bootstrap-from-scratch.sh:2732`) resolves to
`${stage2_runtime_authority}/simple`, and that binary self-identifies as
`WARNING: this Rust-built Simple binary is a bootstrap seed only`. Stage 2 is
built **by the Rust seed**, with `SIMPLE_NATIVE_BUILD_RUST=1` in its env block
(`:2795`). Per `src/compiler_rust/driver/src/cli/native_build.rs:583-587`, that
env var is exactly what routes `native-build` to the **Rust** pipeline —
"plain `bin/simple native-build` runs the pure-Simple driver instead". So no
line of `src/compiler/**` emitted the Stage-2 machine code, and
`src/compiler/60.codegen` cannot be the fix site.

**2. `interface_digest_of` is ruled out.** It has zero call sites
(`.claude/rules/commands.md`), so there is no interface digest to be stale.

### The defect, in instructions

Producer — `FileFingerprint.from_file` in the biting Stage-2 binary
(`objdump -d --disassemble-symbols=_compiler__driver__driver_build__incremental__FileFingerprint.from_file`):

```
bl   _rt_file_size
mov  x21, x0
mov  w0, #0x20            ; 32-byte struct, 4 slots
bl   _rt_alloc
stp  x19, x20, [x0]       ; path@0, content_hash@8
stp  xzr, x21, [x8,#0x10] ; modified_time@16, size@24   <-- CORRECT
orr  x2, x8, #0x1         ; low-bit tag the struct ptr
b    _rt_enum_new         ; Some(payload)
```

The producer is correct: `size` is at byte offset **24**.

Consumer — `driver_native_capsule_result_reason_v1`, the `if val fp = object_fp:
... fp.size` site (`driver_aot_native_output.spl:983-986`):

```
bl   _rt_unwrap_or_self
and  x24, x0, #0xfffffffffffffff8   ; untag
ldr  x0, [x24]                       ; byte offset 0  <-- WRONG: reads `path`
bl   _compiler__driver__driver_aot_native_output__driver_native_capsule_receipt_size_canary_v1
```

**`fp.size` is compiled as a load at offset 0, which is `path` — a `text` heap
pointer.** That is the whole diagnosis. It explains every observation in this
record: the value has the `0x8_…`/`0xB_…` tagged-heap shape; it is unstable
across calls because `path` is freshly allocated each time; `content_hash`
(offset 8) survived because its own read used a different, correct offset; and
`runtime=632` from `rt_file_size` is stable and right.

**"A fresh box per read" is NOT what happens and should not be repeated.** The
instruction proves the READ is at offset 0; offset 0 is the slot the producer
fills with `path` (`stp x19, x20, [x0]`). Whether the 3072-byte stride between
successive garbage values is string-allocation stride has NOT been measured and
should not be asserted.

### Not the shape — the CLOSURE

Same source, same compiler binary, same `--mode dynload --entry-closure
--source src/compiler --source src/app --source src/lib`, same
`SIMPLE_NATIVE_BUILD_RUST=1`: a 58-unit entry that calls the real
`FileFingerprint.from_file` and reads `fp.size` compiles to

```
and  x26, x0, #0xfffffffffffffff8
ldr  x0, [x26, #0x18]     ; byte offset 24 -- CORRECT
```

and prints `632`. The 834-unit Stage-2 closure compiles the identical construct
to offset 0. The defect is **closure-size / global-scope dependent**, not
shape-dependent.

### Where it goes wrong in the seed — CANDIDATE MECHANISM, NOT YET OBSERVED

Everything above (the offset diff, the closure dependence, the ownership) is
measured. What follows is a READING of the seed's source that has **not** been
confirmed by a trace, and must not be cited as verified.

`src/compiler_rust/compiler/src/hir/lower/expr/access.rs` resolves a field
access to a `field_index`. Line **252** is the precise, receiver-typed path
(silent, and what the 58-unit build takes — `SIMPLE_TRACE_FIELD_GET=1` emits
nothing for it). Lines **339 / 369 / 404 / 435** are **name-keyed fallbacks**
used when the receiver's struct type is not known, ending at
`NKM-LOCALBEST` (:435), which picks *the struct with the most fields that has a
field of this name* — a heuristic that ignores the receiver entirely. In an
834-unit closure many structs declare `size`, so this returns some other
struct's index. The two trace channels that name it:
`SIMPLE_TRACE_FIELD_GET=1` (`[FT2] <BRANCH>/<field> struct=<S> idx=<n> in <file>`)
and `SIMPLE_DEBUG_FIELD_FAIL=1`.

Two facts argue against this exact branch and are recorded so nobody treats it
as settled: (a) `NKM-LOCALBEST` returns the *chosen struct's own* index for
`size`, so it can only yield 0 if some >=5-field struct in the closure declares
`size` first — unchecked; (b) the `S-GLOBAL/... idx=N` trace lines show the
by-name path running **correctly** all over this closure, so it is a normal
path, not a smoking gun. An equally good fit is: receiver type unresolved ->
`TypeId::ANY` -> a generic field-0 load, which is a different fix in the same
file. **To settle it**, run the Stage-2 build under `SIMPLE_TRACE_FIELD_GET=1`
and read the lines around
`func=driver_native_capsule_result_reason_v1`: an
`[FT2] <BRANCH>/size struct=<S> idx=0` line confirms the by-name story; no
`/size` line at all means the typed path itself emitted offset 0, which is a
different defect; a `[FIELD-FAIL]` line names the failed resolution directly.

**Owner: `src/compiler_rust` (the seed). Not `src/compiler/**`.** No
pure-Simple change can fix this; the source it miscompiles is already correct.

### 5-second witness (no bootstrap needed)

```
env SIMPLE_PACKAGE_INDEX_COLD_INIT=1 SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_RUNTIME_PATH=<stage2-runtime-authority> SIMPLE_BINARY=<stage2> \
  <stage2-binary> native-build scripts/check/cert/redeploy_gate/fixtures/hello_world.spl \
    --target aarch64-apple-darwin --runtime-bundle core-c-bootstrap \
    --cache-dir <tmp> --runtime-path <stage2-runtime-authority> -o <tmp>/hello
```

`SIMPLE_PACKAGE_INDEX_COLD_INIT=1` is required or it dies at `load_sources`
with `scv-authority-missing` before reaching the canary. Measured on the run-10
`simple.rejected`: `[receipt-size-canary] ... field=46297340801:runtime=632`
three times, then the link-nil failure. ~5 s.

### Reproducer shape table (all built with the Rust seed, `--mode dynload
`--entry-closure`, `SIMPLE_NATIVE_BUILD_RUST=1`)

| # | shape | units | result |
|---|---|---|---|
| 1 | same-unit `class` + Optional bind, `.size` | 3 | PASS 632 |
| 2 | cross-unit `class`, non-optional return | 3 | PASS 632 |
| 3 | cross-unit `class` via Optional bind | 3 | PASS 632 |
| 4 | cross-unit `Result<(text,i32),text>`, `t[0]` in `match Ok(t)` | 3 | PASS |
| 5 | same-unit `struct` + Optional bind | 3 | PASS 632 |
| 6 | cross-unit `struct` + `static fn ... -> S?` + extern-derived `i64` | 3 | PASS 632 |
| 7 | REAL `FileFingerprint.from_file`, plain `if val fp =` bind | 58 | PASS 632 (`ldr [x,#0x18]`) |
| 8 | REAL `FileFingerprint`, `if not fp.?:` guard then bind (the real code's shape) | 58 | PASS 632 |
| 9 | the real Stage-2 closure | 834 | **FAIL — `ldr [x]`, offset 0** |

Shape alone never bites. Only the full closure does, which is consistent with
the name-keyed fallback above.

## RESOLVED (2026-09-13, runs 13-14): the seed dropped `-> T?`'s struct name

The codegen defect this record has been chasing since run 8 is fixed in the Rust
seed. It was never an offset-model bug and never shape-dependent; it was a NAME
that the seed threw away one step earlier than anyone had looked.

### Measured at instruction level, not inferred

F53 left this branch as a candidate "not yet observed". It is now observed. The
Stage 2 `native-build` was replayed verbatim from its own
`stage2-command.transcript` with `SIMPLE_TRACE_FIELD_GET=1` (the bootstrap script
sanitises the stage environment to a canonical env-name list, so the trace does
NOT survive a plain `SIMPLE_TRACE_FIELD_GET=1 sh bootstrap-from-scratch.sh` —
replaying the transcript directly is what makes it observable). 877 units, 829
trace lines, and the whole diagnosis is two of them:

```
[FIELD-TRACE] ANY/size -> LOCAL-BEST idx=0 count=7 in driver_aot_native_output.spl   (x2)
```

No `[FT2]` line accompanies them, which is the load-bearing detail: `get_field_info`
returned **Ok**, so not one of `expr/access.rs`'s name-keyed fallbacks
(`:339/:369/:404/:435`) ever ran. **F53's hand-off named the wrong suspects.**
`NKM-LOCALBEST` and friends are innocent here — they were never reached.

### The chain

1. `FileFingerprint.from_file` is declared `-> FileFingerprint?`
   (`driver_build/incremental.spl:623`). `static_call_return_type_name`
   (`hir/lower/stmt_lowering.rs:127`) matched only `Type::Simple` and
   `Type::Generic`; `ast::Type::Optional` fell to `_ => None`. So
   `val object_fp = FileFingerprint.from_file(capsule.object_path)`
   (`driver_aot_native_output.spl:970`) recorded **no name at all** — no
   `static_call_type_hints` row, no TypeId upgrade.
2. `if val fp = object_fp:` (`:983`) registers its binding with
   `ctx.add_local(name, ty, ..)` — a TypeId and nothing else. With the subject
   erased to ANY there was no `type_name_hint` (that is set only for parameters)
   and no hint row keyed by `object_fp` to inherit, so `fp` carried no name.
3. `expr/access.rs:231`'s ambiguous-field guard could not have helped either
   way: its `try_resolve_receiver_struct_name_from_expr(fp)` had no hint source
   to draw on, so it could only return None. **Whether the guard fired and
   declined, or was never reached, is NOT measured** — neither branch emits a
   trace line. What IS measured is (a) `size` is index-ambiguous, (b) the
   receiver typed ANY, (c) no `[FT2]` line, (d) the `[FIELD-TRACE]` line below.
   The fix does not depend on which of the two it was.
4. `get_field_info(TypeId::ANY, "size")` (`hir/lower/type_resolver.rs:675`) then
   reached its LOCAL-BEST scan: the SMALLEST index among every `HirType::Struct`
   in `module.types` declaring the name. It returned `Ok((0, _))` from a 7-field
   struct. `size` is index **3** in `FileFingerprint` (byte offset 24); index 0
   is `path`, a `text` pointer.

**Why only the 834-unit closure.** 15 structs in the tree declare `size` as their
FIRST field — `FileStat`, `GcObjectHeader` (x3), `TypeLayout`, `BlockHeader`,
`BrushConfig` (x2), `SftpFileInfo` (x2), `ThreadPool`, `PersistentMap`,
`PersistentTrie`, `PersistentSortedMap`, `FileReadCacheStats`. One of them only
enters this unit's `module.types` once the closure is big enough. At 3 and 58
units LOCAL-BEST finds only `FileFingerprint` and answers 3 — which is exactly
why every one of F53's shapes 1-8 passed and only shape 9 failed. The shape table
was measuring the presence of a decoy, not the shape.

### Fix (`src/compiler_rust`, 3 files)

`declared_type_struct_name` looks through payload-preserving wrappers (`T?`,
`mut T`, `*T`) and reports whether the struct arrived WRAPPED. The flag is
load-bearing in both directions: a wrapped return contributes the NAME only,
because upgrading the local's TypeId to bare `T` addresses the payload's slots
through the wrapper — measured as `field=0:runtime=632` on the way to this fix,
a second wrong answer that briefly replaced the first. Unwrapped `-> T` keeps the
existing TypeId upgrade. The name is additionally propagated onto pattern
bindings whose TypeId erased to ANY, reusing the existing `static_call_type_hints`
consumer rather than adding a second mechanism.

**LOCAL-BEST's smallest-index rule is deliberately NOT changed.** It is
memory-safe by construction and flipping it to most-fields-wins is the
`stage2_struct_field_offset_model_mismatch_oob_read_2026-08-30` out-of-bounds
incident. The defect is that it was reached at all.

### Evidence

5-second witness (`stage2 native-build hello_world.spl`,
`SIMPLE_PACKAGE_INDEX_COLD_INIT=1`), both binaries built by the same release-profile
seed so only the fix differs:

| | canary |
|---|---|
| before | `[receipt-size-canary] ... field=40607765761:runtime=632` **x3** |
| after | **no canary line at all** — `fp.size` == `runtime` == 632 |

Both `ANY/size -> LOCAL-BEST idx=0` lines for `driver_aot_native_output.spl` are
gone from the Stage 2 build trace. The one remaining in `native_noop_admission.spl`
is a different call site and is recorded as follow-up below.

Tests: 2 new lowerer tests. `cargo test -p simple-compiler --lib` goes
3946 passed / 35 failed to 3948 passed / 35 failed, and the 35 failing test NAMES
diff byte-for-byte identical against the unmodified tree — all pre-existing.
Note the first test written for this (`test_optional_static_return_keeps_...`)
PASSES on the unmodified tree: a synthetic module cannot reproduce the defect
because the real decoy population is what triggers it. It is kept as a pin, but
`test_declared_type_struct_name_looks_through_payload_wrappers` is the one that
actually discriminates.

### Follow-up, deliberately NOT in this change

`get_field_info`'s ANY branch consults `is_ambiguous_global_field` only AFTER
LOCAL-BEST has already returned, so a field name the compiler KNOWS is
index-ambiguous is still silently guessed whenever a receiver's name cannot be
recovered. `native_noop_admission.spl` still shows exactly that. Making it
fail closed is a separate change with an unmeasured blast radius across 829
trace lines, and it would NOT have fixed this site on its own (access.rs's
`NKM-LOCALBEST` repeats the identical smallest-index guess). It needs its own
lane.

### Run 13 (2026-09-13) — unchanged reproducer, now with the trace

`--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin
evidence root, worktree `agent-aa45d51377e3a4e99`, at `origin/main` 42347f19a51.
Stage 1 admitted; Stage 2 built its 877-unit closure clean; the canary fired
(`field=31758752897:runtime=632`, x3) and the smoke build then failed at the
run-7 link site. Identical to runs 10 and 12.

Two process notes that each cost a run:
- **A tracked-file edit while a bootstrap is running kills it** —
  `error: Rust inputs changed during full bootstrap; refusing to publish a stale
  seed`. It fires during the SEED build, long before admission.
- **`/opt/homebrew/bin/cmp` shadows `/usr/bin/cmp` and is a SYMLINK**, so
  `bootstrap_stage3_compare_bind` (`scripts/check/lib/bootstrap-stage3/authority.shs:26`)
  fails its `candidate == canonical` check and returns 2 —
  `error: Rust runtime authority private-admission origin comparator unavailable
  or I/O failed ... status=2`. The fix is to put `/usr/bin` FIRST on PATH and
  leave `BOOTSTRAP_STAGE3_COMPARE_TOOL` **unset** so auto-bind derives both the
  path and its sha256. Setting that variable by hand without
  `BOOTSTRAP_STAGE3_COMPARE_TOOL_SHA256` fails a different check in the same
  function.

### Run 14 (2026-09-13) — this record's blocker is CLEARED

Same command, virgin evidence root (`--output=.../bootstrap-run14`), carrying the
fix. Stage 1 admitted; Stage 2 built its closure clean (877 compiled, 0 failed,
492.5s + 10.4s link). **For the first time in this chain the receipt-size canary
did not fire even once** — no `[receipt-size-canary]`, no
`capsule-receipt-size-implausible`, no `receipt-content-mismatch`. This record is
RESOLVED.

Stages reached: Stage 1 admitted; Stage 2 built, **not admitted**; Stage 3 not
attempted. The sole remaining blocker is the sibling record's link-nil, verbatim:

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
error: in-process native-build: LLVM native linking failed: Linking failed: no error payload from link_to_native (rendered nil); see the unconditional [linker-wrapper] prints for the failing site
```
