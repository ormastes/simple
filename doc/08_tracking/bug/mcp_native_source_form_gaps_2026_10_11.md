# MCP native source-form lowering gaps

Status: OPEN. Canonical ID: `mcp_native_source_form_gaps_2026_10_11`.
GitHub: https://github.com/ormastes/simple/issues/3080 (registered before source edits).

The actual failed MCP build uses frozen source
`a51194b96b5f5ce3fa57670bc62a15c2414388bf` and producer SHA-256
`e6447d0d10f2c8ae552b67da8420a7e581a22bb55f79e4d4e4d30b981f095811`.
Evidence is retained under C06
`build/native_probe/phase3-whole-20261011-c06/release-phase3-canonical-preparation/attempt3-mcp-failure/`.
`failure.json` identifies the producer/source; `mcp_build.log` SHA-256 is
`b03b5cfd6fbb89fd1f17f31044973b4702c1acc7bdfb7712e4000c187d430bbe`.

Four exact source sites have scoped temporary workarounds:

- `main_static_tools.spl:228`: native HIR StructLit dispatch explicitly rejects
  the brace-form constructor. The named-field constructor retains name, desc,
  and req with the same inputs and field order.
- `main_lazy_caret_tools.spl:94`: native array extend is unresolved. Ordered
  push iteration appends every argument after the unchanged environment and
  executable prefix; process invocation, timeout, cleanup, and output handling
  stay untouched. No command is executed by the source-only verification lane.
- `storage_roots/resolver.spl:177`: native Result.map explicitly only accepts
  primitive payloads. An explicit match evaluates inspect_storage_roots once,
  projects the success roots, and forwards the original StorageRootError.
- `main_lazy_ctx_tools.spl:597`: f64.to_int dispatch is unavailable. A small
  pure score-conversion helper guards the native cast while preserving the
  existing formatter's arithmetic and text assembly.

## Float conversion contract

The interpreter method owner at
`src/compiler_rust/compiler/src/interpreter_method/primitives.rs:278` defines
float to_int as `f.trunc() as i64`. This truncates toward zero, saturates overflow
and infinities to the signed endpoints, and maps NaN to zero. It is read-only
semantic evidence; the Rust seed was not run as a test/tooling fallback.

Native `select_cast_instruction` in
`src/compiler/70.backend/backend/mir_to_llvm_helpers.spl:68` emits fptosi for a
float-to-signed-integer cast. Therefore an unguarded source cast is not equivalent
for NaN or unrepresentable values. The helper multiplies by 1000 once, checks
NaN using `not (scaled == scaled)`, clamps at exact ±2^63, and casts only the
remaining representable finite interval. Maximum/minimum i64 values are exact
integer constants. The existing formatter's handling of negative fractional
scores is retained, not redesigned.

Using ordered equality with negation is deliberate: current backend float-Ne
uses ordered `one`, so `scaled != scaled` would not be a sound native NaN guard.
This workaround does not repair general float-Ne semantics.

The standalone `test/fixtures/compiler/mcp_score_conversion/main.spl` calls the
production helper with twelve independently expected cases: zero, positive and
negative fractional values, sub-milli values, exact finite multiplication,
large finite positive/negative saturation, both infinities, NaN, and negative
zero. The fixture is authored but unexecuted. Existing storage-root resolver,
MCP static-tool and caret scenarios remain separate behavior checks.

## Qualification and removal

Source review, actual affected-source HIR/MIR/object generation, and native
fixture execution are pending. No object/runtime/performance/stage PASS is
claimed. The isolated sparse lane launches no compiler below the resource gate.

Keep this bug OPEN while any workaround remains. Retire each source adaptation
only after its original brace StructLit, array.extend, aggregate Result.map,
and f64.to_int form passes HIR/MIR/native object and behavior controls on a
repaired producer. Float controls must include NaN, infinity, signed endpoints
and truncation; Result controls must cover exact error forwarding and success
fields; argument and descriptor controls must preserve order and all values.
Remove the score helper only when its original method call is qualified.

Declared-array/SdnRow transport belongs to #3079. Optional JSON flatten and the
unlocated trim diagnostic belong to another owner. They are not edited here.

Source workaround commit: `cf5adec6dfdd192ca2150291401451ad1ba16243`; recovery parent `a51194b96b5f5ce3fa57670bc62a15c2414388bf`. Canonical OPEN row is registered in `doc/08_tracking/bug/bug_db.sdn`. This isolated candidate has not been integrated/pushed to `release_phase3`; remote push requires actual Phase3PASS.
