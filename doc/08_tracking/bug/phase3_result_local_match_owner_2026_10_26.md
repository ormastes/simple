# Phase 3 Result local match loses its declared enum owner

Status: OPEN; native behavioral mechanisms qualified for six method-call sites
and four generic codec sites. Combined production-owner qualification pending.
Canonical ID: `phase3_result_local_match_owner_2026_10_26`.
Authoritative DB reconciliation is pending: no qualified full CLI is available.

The immutable Stage 2 producer SHA-256
`acfedbebd1db457efc0f8d1b0b3020dfa20711157bc090334c1b523a6a228779`
rejects ten matches across `backend_helpers`, `backend_api`,
`hir_codec_support`, and `obj_taker`: bare variant `Ok` is ambiguous and
the subject has a known non-enum type. Explicitly typed `Result<T, E>` locals
and the existing `Result.Ok` spelling do not prevent this failure.
The original source was `a0aa04ea5df71665466a5c148cd148b6711da23e`;
the original log is `build/native_probe/phase3_optional_payload_subst/stage2-acfedbebd1db/phase3-main-80.log`
in the preserved `C:/dev/wt-bisect` worktree.

PR #4754 (merged `68142845c39d805c7a3651a6fd62105ff045d71b`) already
adds declared-return recovery for direct call scrutinees. It does not make
these local-variable scrutinees compile with the immutable producer.
The retained method workaround matches the original call directly, once, preserving the
same success/error arms, error text, mutation order, and early returns.
No cast, raw payload extraction, result suppression, or stub is introduced.

Intended-code recovery reference: `9642b8ec4c3a14e8cb7893dce75887b2f4ecdf4b`.
Initial workaround commit: `548831268ca` (retained local experiment, not a published landing).
That initial four-file proposal is superseded: its four generic codec edits
were disproven and restored to their intended code. Only the six method sites
in `backend_helpers`, `backend_api`, and `obj_taker` are retained.
Root-fix owner: compiler MIR declared local/call result provenance lane.
Root-fix entry: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`,
`enum_match_expr_type` and local type binding. Preserve nominal enum identity;
do not resolve collisions by selecting an arbitrary global enum.

Regression evidence must cover generic free calls, concrete method calls,
trait dispatch, both Ok/Err arms, and duplicate variant names. Existing
`test/01_unit/compiler/mir/bare_variant_subject_owner_spec.spl` covers direct
call owner recovery. The native fixture
`test/fixtures/compiler/native_result_method_match_owner.spl` exercises the
method workaround's success and error behavior. Full production-owner verification
requires the ordinary full-context HIR/MIR owner queue and valid dependency
witnesses. Reduced fixtures cannot admit production objects.

Recovery gate: with a rebuilt qualified producer, restore these six locals
narrowly and compile all four affected owners through the normal queue, then run the
behavioral fixture and the MIR ownership regression suite. Keep this bug open
and the tags intact until that gate passes; fetching a root fix is insufficient.

## Bounded native evidence, 2026-10-26

Three repair cycles used the immutable producer above, LLVM backend,
`core-c-bootstrap`, no stub fallback, one requested fixture worker, and the
preserved Stage 2 runtime authority. All logs and failed sources remain under
`C:/dev/wt-p3wa/build/native_probe/result-direct-match-owner`.

- Cycle 1: direct generic free-call matches failed MIR ownership (4 errors).
  Concrete method matches in that module had no ownership errors.
- Cycle 2: adding a generic Result-parameter helper failed monomorphization
  with E-MONO-033 (2 unresolved calls); it did not qualify any workaround.
- Cycle 3, independent entries: identical-Result casts still failed ownership
  (4 errors). The real imported `enum_wire_nil_slot` and
  `enum_wire_restore_nil` cast fixture failed ownership (6 errors), despite
  successful HIR and monomorphization. Neither fixture produced an executable.
- Cycle 3 method-only fixture: native build exit 0, executable exit 0,
  `result-method-match-owner: PASS`. It checks success payload 29 and exact
  `method-error` text with another enum declaring Ok/Err. Logs:
  `cycle3-normal-native_result_method_match_owner.log` and
  `run-native_result_method_match_owner.log`.
  Executable SHA-256:
  `e3ce24419f9a84c71a5779aff182f99e6c356d9b6642b271554d6aea1e78cb53`.

An initial cycle-3 invocation incorrectly requested exact Stage 3 mode for
fixture entries. Its entry guard refused all three before compilation. The
corrected ordinary native invocations above retain separate logs.
HIR persistence stayed enabled and rejected malformed self-check records
(`nil_in_non_optional_scalar`); these were cache refusals, not admitted hits.
No fixture object is a production dependency witness or a donation to Stage 3.
No broad SPipe/core/MCP qualification or underlying compiler fix is claimed.
The working/staged direct-env guards passed; executable specs under
`doc/06_spec` counted zero. Diff whitespace checks passed.

## Renewed codec repair batch, 2026-10-26

Codec workaround commit:
[`0a9837a6082`](https://github.com/ormastes/simple/commit/0a9837a60828721abed7cab7a0fb6b2e64878e3f) (same patch as tested local `14a38034b41`).
Its parent `626fea7f91a` preserves the separately checked six method sites.

After the first three-cycle escalation, the user renewed the binary-first
request and authorized a new bounded repair batch. This batch also stopped
after three source/verification cycles. The producer and runtime lineage stayed
unchanged. Both final fixtures requested 80 threads; actual HIR pools were
bounded to six or seven workers for their two-module closures.

The retained form decodes `Result<bool, text>` on a non-generic, explicitly
typed parameter into `HcEnumWireSlotState`. The generic encoder keeps an
explicitly typed local state and its original write/reject operations. Each
wire call still runs exactly once; an error rejects and returns before append.
This introduces one small state record per scalar wire check. The existing
conservative writer precharge is unchanged.

Restore uses an explicitly specialized `Result<T, text>` parameter helper.
Both `hc_restore_enum_nil_result<T>` and `enum_wire_restore_nil<T>` receive
explicit type arguments. The success value and the original
`reject_malformed(detail); return nil` sequence are retained. Native checks
verified error mutation through this helper boundary, including the returned
nil and exact error detail; no ABI reinterpretation or unchecked cast is used.

The first forms compiled but their diagnostics had unrelated inference errors:
a generic wrapper returned a state record into an inferred local, and a
restored nominal enum was passed to an inferred `enum_wire_nil_slot$i64`.
The final fixtures keep typed state inside the generic caller and use explicit
nominal locals and type arguments for downstream enum-wire calls.

The generator's 33 `hc_restore_enum_nil` call sites were audited. All directly
return from a decoder with an explicit nominal return type, and all prototypes
are qualified constructors of that same type. There are zero owner mismatches
across AsmLocation, DimExprKind, EffectKind, HirExprKind, HirPatternKind,
HirTypeKind, and TypeKind. They do not introduce the inferred result local that
broke the diagnostic. The generator and generated codec therefore stay intact.
Audit: `build/native_probe/result-parameter-owner/generated-restore-call-audit.json`.

Final native behavioral evidence:

- `native_wire_bool_result_parameter.spl`: known true nil flag, real false
  scalar as non-nil, and malformed slot with its exact error all passed.
  Executable SHA-256:
  `a85ddf3daa1507aaf97d439549749032adad18f0c46e6fc096b72817eecaa6e6`.
- `native_wire_restore_result_parameter.spl`: both explicit generic and
  concrete Result parameter extraction restored real wire nil; malformed
  slots returned nil and propagated the exact reader error. Passed.
  Executable SHA-256:
  `7634955261791abb87bc9c1e001521dd262d6879ccdd3397b6a1d889e38a789c`.

Logs, source snapshots, original capsule receipts, and relink manifests remain
under `C:/dev/wt-p3wa/build/native_probe/result-parameter-owner`. Cycle 2 built
and linked native objects but failed subsequent SMF packaging. Cycle 3 used
`--mode one-binary`; it built and linked both entries but still returned 1
after linking. The executables above were strict diagnostic relinks of those
actual emitted objects, hash-checked canonical 41 C runtime owners from the
frozen a0 source, and canonical entry shims derived from actual object symbols.
Both relinks and executions returned 0. The native-build command itself is
still FAIL; this is not a full pipeline PASS, cache admission, or production
object donation. No fourth cycle was run.
