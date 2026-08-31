# Coverage-wrapper native compile: HIR-lowering residuals (2026-08-31)

Status: OPEN (residual classes). Three sibling root causes were FIXED in the
same change (`fix/cov-wrapper-hir-lowering`); this record covers what is left.

## Context

A full suite run (`/tmp/suite3.log`, 1365 PASS / ~220 FAIL) had 27 `HIR
lowering: ...` failures plus 1 `Trait coherence errors`, all raised while
compiling generated coverage wrappers
(`spipe_wrapped__..._simple_cov_..._spec_native.spl`). Unlike PR #156 these are
NOT one injected-preamble cause: they split into at least eight independent
root causes.

## Harness (reproduction)

Wrappers are regenerated with `preprocess_spipe_native_result_file`
(`src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl:582`) and compiled
with `bin/simple compile <wrapper>`, reading the compiler's own exit status. A
green `bin/simple test --coverage` verdict is NOT evidence (the runner degraded
to the interpreter silently until PR #157).

Both sides were measured on seeds built from this branch's base
(`b0be388ec46`), pristine vs. patched — NOT the ambient `bin/simple`, which on
this host is built from uncommitted `lowerer.rs`/`identifiers.rs` edits and is
therefore not origin/main's compiler.

24 of the 29 rows reproduce their exact suite diagnostic through this harness.

## FIXED in this change (evidence)

1. **Paren-less builtin method call on a builtin receiver.**
   `xs.len`, `s.trim`, `xs.first` reached
   `cannot infer field type while lowering <fn>: struct 'Array' field 'len'`
   because `has_known_method_for_struct_name` consults only
   `method_return_types` (user-declared methods); builtin methods are never
   registered there, so the paren-less-method fallback was never reached.
   `Array`/`String`/`Dict`/… have no user-declarable fields, so `recv.name` on
   one of them is always a method call.
   Proof: `bin/simple compile test/01_unit/std/no_paren_test.spl`
   rc=1 (`struct 'Array' field 'len'`) -> rc=0.

2. **Index into a bare `tuple` annotation.**
   `fn f() -> tuple:` lowers to `HirType::Tuple(vec![])`; indexing it raised
   `Cannot infer element type for index into 'empty tuple'` instead of
   degrading to ANY the way every other unknown receiver does.
   Proof: `bin/simple compile src/os/crypto/ml_dsa_ntt.spl` rc=1 -> rc=0.
   This is the cause behind all 5 crypto spec rows (`power2round_poly`,
   `kpke_keygen_params`).

3. **`.ok` / `.err` on a receiver whose type was erased to ANY.**
   `try_lower_result_projection` needs a typed `Result` receiver; when the
   producing call's return type was not propagated it bailed and the access
   became a hard error. A last-resort dynamic projection (payload ANY,
   discriminant checked at runtime, placed AFTER every field-resolution
   attempt so it cannot hijack a real `ok`/`err` field) removes the
   native-only divergence.
   Proof: `aop_spec`, `di_injection_spec`, `result_type_spec` wrappers no
   longer fail in HIR lowering.

## RESIDUAL — need a decision or deeper work (NOT papered over)

### R1. Interpreter-only constructs in native codegen (5 specs)
`test/01_unit/std/given_working_spec.spl`, `test/feature/usage/structs_spec.spl`
fail with `Unsupported feature: Context statements require interpreter mode.
Native codegen support is planned.` After fix (3),
`browser_engine/net/resource_loader_spec.spl` (18 functions),
`aop_spec` (1), `di_injection_spec` (2) and `exists_check_value_return_spec` (1)
advance to the sibling gate `cannot compile to standalone SMF: N function(s)
contain constructs that require the interpreter`.

This is a declared, planned native-codegen gap, not a bug in these specs. The
DECISION needed is at the runner level: a spec that legitimately requires the
interpreter must be routed to an interpreter-only coverage lane, not compiled.
Silently accepting a degraded run is exactly what PR #157 closed.

### R2. FIXED (2026-08-31, round 2) — the type was never declared
**The original R2 explanation above was WRONG.** It was not a registry gap:
`SimpleAbiDigest256V1` was **used 13 times and declared zero times**.
`abi_digest.spl:15` imports it from
`std.nogc_sync_mut.composition.provider_contract`, which declares
`SimpleProviderQueryV1`, `SimpleProviderQueryResultV1`, `SimpleCliCommandV1`,
`SimpleCliCommandRequestV1`, `SimpleCliCommandResultV1` and nothing else;
`composition/__init__.spl:4-8` re-exports the name from there anyway. The
compiler was behaving correctly — an unresolvable imported name erases to ANY,
so `value.w0` is genuinely unresolvable.

Same defect class as the `RtCoreUInt` C-runtime incident in CLAUDE.md: a symbol
referenced everywhere and defined nowhere, sitting in `main` looking green.

Evidence (own seed built from `79126c25822`, rc read into a variable on the
line after the compile, never through a pipe):
`simple compile src/lib/nogc_sync_mut/composition/abi_digest.spl`
rc=1 `Undefined("undefined identifier: SimpleAbiDigest256V1")` -> rc=0.

Fix: declare `struct SimpleAbiDigest256V1 { w0..w3: u64 }` in
`provider_contract.spl`. The layout is not guessed — it is fixed by the
`abi_digest.spl` module header (four ordered u64 words, `w0` = digest bytes
0..7 big-endian) and by every use site (`var words: [u64]`,
`_u64_to_hex16(value: u64)`).

**Still open, filed here rather than guessed:** `SimpleProviderQueryResultV2` is
also re-exported from `__init__.spl` and declared nowhere. Its shape IS
determinable from its single construction site
(`provider_abi_digest_admission_spec.spl:41` — `base: SimpleProviderQueryResultV1`,
`abi_digest_256: SimpleAbiDigest256V1`), but its codec
`encode_provider_query_result_v2` / `decode_provider_query_result_v2` has **zero
implementations in `src/`**, so declaring the type alone would not make that
spec work. That spec is not in this failure set; the missing codec is a feature
gap needing its own decision.

### R3. RE-TRIAGED — ghost imports over a missing implementation (not R2's family)
Merging R3 into R2 would have been wrong. `BeLayoutBox` and `BeDomNode` ARE
declared (`layout_box.spl:12`, `dom.spl:187`), so this is not a
missing-declaration case in the way R2 was — but it is also not a registry gap.

`anonymous_block_spec.spl:22` and `ifc_linebox_spec.spl` import
`LayoutContext, LayoutBox, LineBox, InlineFragment, layout_context_new` from
`std.gc_async_mut.gpu.browser_engine.layout`. That module exports `BeLayoutBox`
and does not provide any of those names — they are declared `pub` in the
sibling `layout_m14_types.spl`. That is why the diagnostic names `BeLayoutBox`
for a field (`is_anonymous`, `line_boxes`) that belongs to `LayoutBox`.

Correcting the import module would NOT fix these specs, which is why no import
edit was made: `layout_block` — exported at `layout.spl:187` and imported by
both specs — has **no definition anywhere in `src/`**
(`grep -rn "fn layout_block" src/lib/gc_async_mut/gpu/browser_engine/*.spl`
returns nothing). The M14 layout entry point is unimplemented and `layout.spl`
exports a phantom name. Implementing CSS anonymous-block / inline-formatting
layout is a feature, not a residual fix.

`dom_query_spec` (`struct 'BeDomNode' field 'classes'`) was NOT flagged by the
ghost-import scan and is a separate, still-unattributed cause.

### R2/R3 cross-cutting observation (needs a decision, deliberately not acted on)
Both classes share one mechanism: **`use m.{X}` where `m` does not provide `X`
is silently erased to ANY instead of being rejected at the import.** The error
then surfaces far away as `cannot infer field type ... struct 'ANY' field '<f>'`,
naming neither the bad import nor the module. Making a ghost import a hard
error at the `use` site would have caught R2 and R3 at their source, but it
would also reject an unknown amount of existing code, so it is a design
decision, not a residual fix. A scanner that detects the pattern was written
for this investigation and is described under "Ghost-import scan" below.

### R4. Chained paren-less call on an ANY receiver (1 spec)
`exists_check_spec.spl` advances past `Array.first` (fix 1) and now stops at
`struct 'ANY' field 'lower'` — `s.trim.lower`, where `.trim`'s dynamic
MethodCall has type ANY. Deliberately NOT fixed here: making every
unresolvable field on an ANY receiver a dynamic method call would also convert
R2/R3's real compile errors into silent runtime failures. Needs a decision on
whether ANY-receiver field access should be dynamic.

### R5. Class literal with undeclared fields (1 spec)
`classes_spec.spl:290-297` declares `class ValueHolder` inside an `it` block
with methods only, and constructs it as `ValueHolder { _value: 10 }`;
`self._value` then has no declared field. The interpreter accepts this. Design
question: does a class literal implicitly declare fields? Do not "fix" by
editing the spec until that is answered.

### R6. Optional arithmetic (1 spec)
`shared_pointers_spec.spl`: `cannot apply 'Add' to an optional value that has
not been unwrapped`. The diagnostic already names the documented idioms
(`x ?? default`, `x.unwrap()`, `if val v = x:`). Flow-sensitive narrowing is
explicitly NOT the answer —
`doc/05_design/language/type_system/flow_sensitive_narrowing_design.md` is
status PROPOSAL. Needs a source fix in the spec that does not weaken its
assertion.

### R7. llvm_backend arm32 / i686 (2 specs) — OVERLAP
The wrapper generator returns the original path for these, and a direct compile
fails with `Undefined("undefined identifier: panic")` — the class owned by
`fix/cov-wrapper-undefined-identifiers`. The suite's
`` `case KwMod:` is not a variant of the matched enum `` diagnostic did NOT
reproduce through this harness, and `case KwMod` has zero occurrences in
`.spl` source, so that arm is generated rather than written. Re-triage after
the sibling branch lands.

### R8. `Trait coherence errors` (1 spec) — NOT REPRODUCED
`trait_coherence_spec.spl` compiles cleanly (rc=0) through the plain wrapper.
The suite failure is on the wrapper of the **coverage-instrumented**
`simple_cov_...` copy, which this harness does not produce. Needs a repro that
includes coverage instrumentation before it can be triaged.


## Round 2 (2026-08-31) — regrouping of the `/tmp/suite4.log` population

**Containment first (the "30 + 26" framing double-counts).** The 30
`HIR lowering: Unsupported feature: ...` and the 26 `cannot infer field type`
rows OVERLAP: the field-infer diagnostic is emitted wrapped in
`Unsupported feature:` text (`hir/lower/expr/access.rs:479`). Deduplicated
against spec identity the real population is **37 rows**, not ~58.

| group | n | maps to |
|---|---|---|
| `SimpleAbiDigest256V1` / `struct 'ANY' field 'w0'` | 4 | **R2 — FIXED** |
| `LayoutBox`/`line_boxes` ghost imports (anonymous_block, ifc_linebox) | 2 | **R3 — re-triaged, filed** |
| `case KwMod:` not a variant | 4 | R7 — sibling branch (`fix/cov-wrapper-undefined-round2`) |
| `Context statements require interpreter mode` | 2 | R1 — runner-routing decision |
| `ValueHolder._value` (+ check `dsl_spec` `ContextBuilder.__init__`) | 2 | R5 — design question |
| optional `Add` (shared_pointers_spec) | 1 | R6 — do NOT implement narrowing |
| `Trait coherence errors` | 1 | R8 — needs coverage-instrumented repro |
| `exists_check` field `'lower'`, `generics_spec` field `'first'` | 2 | **R4 — deliberately left failing** |
| `main: struct 'ANY' field '<user field>'` + named-struct-missing-field | ~13 | **NEW — unattributed, see below** |
| `dom_query_spec` `BeDomNode.classes` | 1 | NEW — separate from R3 |
| 2 unresolved imports, 1 `Module resolution error: Semantic(`, 1 MIR `'Private'`, `Function.LOG_TRACE` | 5 | NEW — untriaged |

### NEW-A. `main: struct 'ANY' field '<f>'` (~13 specs) — UNATTRIBUTED
`server_worker_policy` (`worker_count`), `rt_hal_buffer_dispatch` (`accepted`),
`audit_log_hash_chain` (`io_runtime`), `debug_service_v1` (`nodes`),
`simd_fixed_scalable_parity` (`fixed_lanes`), `rt_hal_exact_type_id`
(`receipt`), `scenario_evidence_manifest_io` (`showcase_status`), `gui_driver`
(`used_geometry`), `run_spec` (`project`), plus named-struct variants
`Stdin.events`, `Resource.exited`, `LayoutNodeInput.oracle_box`,
`GpuLightingState.light_buf`.

`main` here is the generated wrapper's `main` — `_preprocess_spipe_file`
(`test_result_wrapper.spl:540`) inlines ALL spec top-level code into it, so
every one of these is a field access inside an inlined `describe`/`it` body.

Ruled out: the ghost-import scan flags only `debug_service_v1` of this group,
so this is NOT predominantly R2's cause. Not yet attributed because a direct
`bin/simple compile <spec>` does not reproduce it — the raw spec stops earlier
at a lint gate (`server_worker_policy_spec` exits on
`spipe_false_boolean_wrapper_assertions` before lowering), so the group needs
the actual generated wrapper. `--keep-artifacts` does not retain wrappers;
they must be regenerated via `preprocess_spipe_native_result_file` and copied
out of `/mnt/data/tmp` before cleanup. `SIMPLE_DEBUG_FIELD_FAIL=1` prints
candidate structs and `global_struct_defs` contents at the failure and is the
right instrument once a wrapper is in hand.

### R4 stayed closed
The round-2 change is source-only (one struct declaration); it does not touch
`expr/access.rs`, the ANY-receiver fallback, or any lowering path. Verified
positively rather than assumed: after the fix,
`simple compile test/feature/usage/exists_check_spec.spl` still rc=1, still
`field 'lower'`. Broadening the fallback to ANY remains the wrong trade — a
loud compile error beats a silent runtime wrong answer.

### Ghost-import scan
The `use m.{X}` / "m has no X" detector used above indexes every
`pub? class|struct|enum|trait|fn|val|var` and `export`/`export use` name per
module and checks each spec's brace-imports against it. Over the failing set it
flagged exactly `anonymous_block_spec`, `ifc_linebox_spec` and
`debug_service_v1_spec`. It is a throwaway investigation aid, not landed as a
gate — turning it into one is the design decision recorded above.
