# Builtin Array calls lack collection-planner identity

Status: open. Owner: Codex items3_7, item 3 prerequisite lane.
Requirements: collection planner REQ-002, REQ-003, REQ-007.

The real Array map/filter MIR dispatch deliberately accepts
`MethodResolution.Unresolved` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`.
The typed collection extractor requires a resolved operation symbol and
therefore cannot consume these builtin calls. There is no production
collection registry producer or `config/compiler/collection_operations.sdn`.

Acceptance: parse a real typed Array map source, lower and resolve its HIR,
and retain an admitted builtin operation identity. A named user receiver
with the same method spelling must not receive that identity. Existing
untyped bootstrap lowering must remain unchanged. Registry admission must
bind canonical builtin identity, not infer it from method spelling.

The initial integration regression exercises real frontend/HIR/resolver
owners. A failing unresolved assertion is prerequisite evidence, not a
replacement for emitted MIR or cross-engine production qualification.

`MethodResolution` currently has only user instance/trait/free/static symbol
variants and Unresolved. Adding builtin identity requires a deliberate
representation change, generated HIR codec updates, resolver transport
updates, MIR dispatch, and cache identity validation. Inventing a user symbol
ID or admitting unresolved method names is not a safe workaround.

No optimization or fusion is authorized by this prerequisite: effect,
alias, order, memory, callback, and cross-engine P0 gates remain mandatory.
Provider token usage and comparable cohort: unavailable.

## Candidate and bounded diagnostic result

The candidate appends `MethodResolution.BuiltinCollection` with bounded
`CollectionBuiltinOperation.ArrayMap`/`ArrayFilter` identity. It preserves
instance/trait/UFCS precedence, requires a typed builtin Array and a supported
unary inline callback shape, and leaves untyped bootstrap calls unchanged.
This establishes dispatch shape only, not a verified callback signature or
rewrite proof. MIR revalidates the identity and uses the existing loop path.

The authoritative pure-Simple codec generator produced the codec update;
ordinary and canonical codec version headers were advanced so existing HIR
and portable-body caches cannot retain the previous schema identity.

Three authorized Windows Phase 1 diagnostic cycles were used:

1. Original owner: one integration example failed its resolved-identity check.
2. Candidate: two examples passed (typed identity/codec round trip and
   same-named user receiver exclusion).
3. Extended executable coverage: three examples, one passed, two failed.
   The MIR scenario reached zero lowering errors but then called an unimported
   `serialize_mir_module`. The function lives in
   `compiler.mir.mir_serialization`; the test needs that explicit import in a
   later authorized cycle. The interpreter map result was 5 as expected;
   the filter result did not match the expected `Value.Int(2)` shape.

No fourth cycle ran. Filter root cause is unproven, the candidate is not
production verified, and the full registry/extraction/fusion path remains open.
See the item 3 evidence report for commands and logs.

Independent review found additional filter admission gaps: the classifier
accepts any Array element type and does not prove a boolean predicate result.
The existing MIR filter loop uses i64 element decoding and raw nonzero
predicate truth, whereas the new HIR interpreter branch requires Value.Bool.
The candidate must remain draft until admission is constrained or typed
backend parity is implemented and verified. These findings do not establish
the root cause of the observed filter result mismatch.
