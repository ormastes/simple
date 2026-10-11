# Bare enum unit patterns become duplicate MIR defaults

Source review links the Windows Phase 4 lifecycle closure's B5b duplicate-default
diagnostic to `MemoryOrdering` alternatives in `std.nogc_sync_mut.atomic`.
The imported module is present. Flat AST conversion deliberately represents bare
identifiers as bindings; HIR previously accepted every binding as irrefutable.
MIR already repairs a name owned by exactly one known enum, but leaves a name
shared by multiple enums as a binding. Its global uniqueness test does not use
the scrutinee's declared owner. This missing distinction, rather than all bare
patterns unconditionally failing, is the source defect.

The repair indexes nullary variants by consumer-local enum symbol identity before
function bodies lower. Match lowering uses the scrutinee's expression type or its
declared symbol type to distinguish an owned variant from an actual binding.
Imported aliases receive their own identity. Registry lifetime is one HirLowering
module and is cleared by the existing context reset; no frontend/global root is
introduced. Non-unit variants, unknown names, mutable bindings and unrelated enum
names retain binding semantics. MIR duplicate-default validation is unchanged.

Regression artifacts:
- `test/unit/compiler/hir/bare_enum_unit_pattern_spec.spl`: owner discrimination,
  unit/payload distinction, mutable/catch-all/wildcard cases, consumer alias.
- `test/fixtures/compiler/bare_enum_unit_pattern_native.spl`: executable exit-zero
  contract selecting both variants, qualified alternatives and a real catch-all.
- `test/fixtures/compiler/bare_enum_duplicate_defaults_invalid.spl`: compilation
  must still reject two genuine default arms.

Pre-fix Linux producer 184d1be492926713d19bfb95ba2705cb31a2fb6affe8ebea9e1874185d6ef921
reproduces exact B5b multiple wildcard/binding defaults when two enums both own
Relaxed/Acquire. Evidence: classfix-source-623b7943f1/build/atomic-receiver-discriminator-20261002/bare-enum-collision.log
and its process-tree receipt. The unique-owner control compiled but panicked on
an enum discriminant at runtime; the full catch-all fixture failed on unresolved
`remaining`. These are additional pre-fix failures, not a successful execution.
Three bounded baseline attempts exhausted this session's enum iteration cap.
Post-fix executable tests and required compiler/MCP checks remain pending.

## Follow-up: typed MIR owner recovery (2026-10-08)

The HTTP closure exposed a second path through the same owner problem: bare
`Ok`/`Err` enum arms reached MIR with an absent pattern type even when the
scrutinee was a typed `Result`, and the global variant-owner search rejected
`Ok` as ambiguous. A source-only follow-up now seeds enum identity from
`enum_match_expr_type(scrutinee)` before resolving enum arms. Bare unit
`Binding` patterns are promoted only when the known subject owner declares that
variant as unit; unknown-subject fallback requires one total owner and unit
metadata. Unit-vs-payload registrations remain distinct, and explicit pattern
owners must match the subject owner.

Regression sources are in
`test/fixtures/compiler/bare_enum_unit_pattern_owners/`: two imported enums
with the same bare type and variant names but different payload shape, a
payload-name binding check, a catch-all that uses its binding, Result `Ok`/`Err`
matching while another enum declares those names, and a wrong-owner negative
fixture. They are **uncompiled and unrun**. The existing HTTP failure logs
remain the only execution evidence; this patch has no compiler qualification.
Qualified-name fallback for pre-existing owner-resolution paths outside this
change remains a separate audit item.

The separate global AtomicI64 `load` / `compare_exchange` source defect is fixed
by commit 2bbeac34c3; see bootstrap_global_receiver_canonical_identity_2026-10-02.md.
Its post-fix native verification also remains pending.
