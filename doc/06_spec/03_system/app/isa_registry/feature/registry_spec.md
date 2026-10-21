# Pinned ISA registry declarations

**Status:** Authored manual; execution and docgen UNRUN. This is not generated evidence.
**Requirement:** REQ-MC-009; D0; research §7.1–7.2.
**Executable source:** `test/03_system/app/isa_registry/feature/registry_spec.spl`.

## Inspect a pinned declaration

1. Load the pinned fixture authority. The synthetic authority names its revision, snapshot identity and exact operation set; it represents no official ISA.
2. Parse the registry. Every operation retains its semantic name, element, shape, required features, lowering, encoder/decoder declarations, fallback policy, verification obligations and reason.
3. Inspect declared coverage. All six lowering states remain visible. Unsupported and unverified declarations explain their status. Empty encoder declarations never become proof of an implementation.
4. Inspect required verification obligations. Each declared evidence kind produces one typed obligation for its operation. An obligation does not report a passing test.

Expected: a strict parser result, exact preserved fields, a stable coverage table and exact obligation pairs. These expectations are executable assertions in the source; none has yet been observed on a qualified runtime.

## Compare reordered inputs

1. Parse the same synthetic rows in opposite orders, with reversed authority IDs and verification lists.
2. Inspect declared coverage. Both must equal the independently authored golden below, including the final LF.

| operation_id | lowering | reason | verification |
|---|---|---|---|
| fixture.a | native | | byte-golden,decode-roundtrip |
| fixture.b | unsupported | not-implemented | |

3. Inspect required verification obligations. Exactly two sorted pairs belong to fixture.a. fixture.b stays in coverage with its explicit unsupported declaration.

## Refuse invalid input

1. Change one envelope field, operation field, pin, membership, lowering or capacity property.
2. Reject invalid registry input with its specified error code. Equal row counts with different IDs must fail; source-provided metadata cannot authorize itself.
3. Mutate a successfully decoded typed registry's snapshot identity and invoke validation and both generators. All must refuse authority_mismatch.

<details>
<summary>Edge and capacity matrix</summary>

Cases include unknown schema/fields, duplicate/missing keys, wrong field type, invalid digest, revision mismatch, duplicate evidence/features/rows, missing/extra/duplicate authority membership, empty IDs, trailing input, forbidden fallback, missing unsupported/unverified reason, exact byte limit and depth/row/list/text limits. See executable source and the test plan for individual scenario names.

</details>

Official ISA selection, complete pinned extraction, integration coverage, instruction execution, latency and RSS evidence remain pending. No percentage, complete ISA support or certification claim follows from these fixtures.

Source review amendment adds malformed escape/control/separator refusal, exact structural-capacity acceptance and typed invalid-lowering/duplicate-row/oversize-ID refusal. Total authored scenarios: 32. Runtime and generated-manual status remain UNRUN.
