# Clang Contract Specification

> Tests covering Supported Clang majors (architecture 12.6), ClangFeatureSet — the CapabilitySet wire slot, ClangNodeFlags and the rewrite-policy gate (architecture 12.3), ClangRejectReason wire discriminants, ClangEntityIdentity — exact bytes, ClangEntityIdentity — round trip, ClangEntityIdentity — rejection, ClangAdapterCapability — exact bytes, ClangAdapterCapability — round trip and rejection, Adapter acceptance carries a reason receipt (shared rule 4), ClangAstExport — exact bytes, ClangAstExport — empty input, ClangAstExport — round trip, ClangAstExport — durable identity resolution, ClangAstExport — rejection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 64 | 64 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Clang Contract Specification

## Scenarios

### Supported Clang majors (architecture 12.6)

#### accepts only the majors this repo builds and tests an adapter for

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts only the majors this repo builds and tests an adapter for


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts only the majors this repo builds and tests an adapter for")
assert_true(clang_major_supported(CLANG_SUPPORTED_MAJOR_MIN))
assert_true(clang_major_supported(CLANG_SUPPORTED_MAJOR_PRIMARY))
assert_true(clang_major_supported(CLANG_SUPPORTED_MAJOR_MAX))
```

</details>

#### rejects an unknown major rather than assuming ABI compatibility

- rejects an unknown major rather than assuming ABI compatibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown major rather than assuming ABI compatibility")
assert_false(clang_major_supported(CLANG_SUPPORTED_MAJOR_MIN - 1))
assert_false(clang_major_supported(CLANG_SUPPORTED_MAJOR_MAX + 1))
assert_false(clang_major_supported(0))
assert_false(clang_major_supported(99))
```

</details>

### ClangFeatureSet — the CapabilitySet wire slot

#### accepts the frozen five-bit vocabulary

- accepts the frozen five-bit vocabulary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the frozen five-bit vocabulary")
assert_true(clang_feature_set_valid(CLANG_FEATURE_NONE))
assert_true(clang_feature_set_valid(CLANG_FEATURE_SET_ALL))
assert_true(clang_feature_set_valid(CLANG_FEATURE_AST_EXPORT))
```

</details>

#### rejects a reserved bit instead of ignoring it

- rejects a reserved bit instead of ignoring it


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a reserved bit instead of ignoring it")
assert_false(clang_feature_set_valid(CLANG_FEATURE_SET_ALL + 1))
assert_false(clang_feature_set_valid(-1))
```

</details>

#### reports membership only when every requested bit is present

- reports membership only when every requested bit is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports membership only when every requested bit is present")
val s = clang_feature_set_add(CLANG_FEATURE_AST_EXPORT,
                              CLANG_FEATURE_LLVM_PASS)
assert_true(clang_feature_set_contains(s, CLANG_FEATURE_AST_EXPORT))
assert_true(clang_feature_set_contains(s, CLANG_FEATURE_LLVM_PASS))
assert_false(clang_feature_set_contains(s, CLANG_FEATURE_MATCHER_QUERY))
assert_false(clang_feature_set_contains(s, CLANG_FEATURE_PROFILE_REMARKS))
```

</details>

#### treats the empty request as unsatisfiable rather than trivially true

- treats the empty request as unsatisfiable rather than trivially true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats the empty request as unsatisfiable rather than trivially true")
assert_false(clang_feature_set_contains(CLANG_FEATURE_SET_ALL,
                                        CLANG_FEATURE_NONE))
```

</details>

### ClangNodeFlags and the rewrite-policy gate (architecture 12.3)

#### rejects a flags word with a reserved bit set

- rejects a flags word with a reserved bit set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a flags word with a reserved bit set")
assert_true(clang_node_flags_valid(CLANG_NODE_FLAGS_ALL))
assert_false(clang_node_flags_valid(CLANG_NODE_FLAGS_ALL + 1))
assert_false(clang_node_flags_valid(-1))
```

</details>

#### requires explicit policy for macro, system-header, generated and template nodes

- requires explicit policy for macro, system-header, generated and template nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires explicit policy for macro, system-header, generated and template nodes")
assert_true(clang_rewrite_policy_required(CLANG_NODE_FLAG_MACRO_EXPANSION))
assert_true(clang_rewrite_policy_required(CLANG_NODE_FLAG_SYSTEM_HEADER))
assert_true(clang_rewrite_policy_required(CLANG_NODE_FLAG_GENERATED_FILE))
assert_true(clang_rewrite_policy_required(
    CLANG_NODE_FLAG_TEMPLATE_INSTANTIATION))
assert_equal(CLANG_NODE_FLAGS_REWRITE_GUARDED, 29)
```

</details>

#### does not gate a plain node, nor one that is merely implicit or synthetic

- does not gate a plain node, nor one that is merely implicit or synthetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not gate a plain node, nor one that is merely implicit or synthetic")
assert_false(clang_rewrite_policy_required(CLANG_NODE_FLAG_NONE))
assert_false(clang_rewrite_policy_required(CLANG_NODE_FLAG_IMPLICIT))
assert_false(clang_rewrite_policy_required(CLANG_NODE_FLAG_SYNTHETIC_ORIGIN))
```

</details>

### ClangRejectReason wire discriminants

#### assigns the eight reasons to 0..7 in declaration order

- assigns the eight reasons to 0..7 in declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the eight reasons to 0..7 in declaration order")
assert_equal(clang_reject_reason_to_u8(ClangRejectReason.Accepted), 0)
assert_equal(clang_reject_reason_to_u8(ClangRejectReason.UnsupportedMajor), 1)
assert_equal(clang_reject_reason_to_u8(
    ClangRejectReason.AstExportSchemaMismatch), 2)
assert_equal(clang_reject_reason_to_u8(
    ClangRejectReason.MatcherAdapterMissing), 3)
assert_equal(clang_reject_reason_to_u8(
    ClangRejectReason.TransformerAdapterMissing), 4)
assert_equal(clang_reject_reason_to_u8(
    ClangRejectReason.LlvmIrSchemaMismatch), 5)
assert_equal(clang_reject_reason_to_u8(
    ClangRejectReason.MissingRequiredFeature), 6)
assert_equal(clang_reject_reason_to_u8(
    ClangRejectReason.UnknownFeatureBits), 7)
assert_equal(CLANG_REJECT_REASON_COUNT, 8)
```

</details>

#### round-trips every discriminant through from_u8

- round-trips every discriminant through from_u8


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every discriminant through from_u8")
var i = 0
var mismatches = 0
while i <= CLANG_REJECT_REASON_MAX:
    if clang_reject_reason_to_u8(clang_reject_reason_from_u8(i)) != i:
        mismatches = mismatches + 1
    i = i + 1
assert_equal(mismatches, 0)
```

</details>

#### rejects a discriminant past the end of the frozen enum

- rejects a discriminant past the end of the frozen enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a discriminant past the end of the frozen enum")
assert_true(clang_reject_reason_valid(CLANG_REJECT_REASON_MAX))
assert_false(clang_reject_reason_valid(CLANG_REJECT_REASON_MAX + 1))
assert_false(clang_reject_reason_valid(-1))
```

</details>

### ClangEntityIdentity — exact bytes

#### encodes the zero identity to the frozen 68-byte body

- encodes the zero identity to the frozen 68-byte body


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the zero identity to the frozen 68-byte body")
expect(wire_to_hex(encode_clang_entity_identity(clang_zero_identity())))
    .to_equal(GOLDEN_IDENTITY_ZERO)
```

</details>

#### encodes the saturated identity without sign-extension filler

- encodes the saturated identity without sign-extension filler


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the saturated identity without sign-extension filler")
expect(wire_to_hex(encode_clang_entity_identity(identity_max())))
    .to_equal(GOLDEN_IDENTITY_MAX)
```

</details>

#### encodes every field asymmetrically so field order is pinned

- encodes every field asymmetrically so field order is pinned


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes every field asymmetrically so field order is pinned")
expect(wire_to_hex(encode_clang_entity_identity(identity_decl())))
    .to_equal(GOLDEN_IDENTITY_DECL)
```

</details>

### ClangEntityIdentity — round trip

#### reconstructs the asymmetric declaration identity

- reconstructs the asymmetric declaration identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs the asymmetric declaration identity")
val r = decode_clang_entity_identity(
    encode_clang_entity_identity(identity_decl()))
assert_true(r.ok)
assert_true(clang_entity_identity_equal(r.value, identity_decl()))
```

</details>

#### reconstructs the zero identity

- reconstructs the zero identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs the zero identity")
val r = decode_clang_entity_identity(
    encode_clang_entity_identity(clang_zero_identity()))
assert_true(r.ok)
assert_true(clang_entity_identity_equal(r.value, clang_zero_identity()))
```

</details>

#### distinguishes an absent USR from StringId zero

- distinguishes an absent USR from StringId zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes an absent USR from StringId zero")
assert_true(clang_entity_identity_has_usr(identity_decl()))
assert_true(clang_entity_identity_has_usr(clang_zero_identity()))
assert_false(clang_entity_identity_has_usr(identity_max()))
```

</details>

### ClangEntityIdentity — rejection

#### rejects an empty buffer

- rejects an empty buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty buffer")
assert_false(decode_clang_entity_identity(empty_bytes()).ok)
```

</details>

#### rejects a truncated record

- rejects a truncated record


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated record")
val enc = encode_clang_entity_identity(identity_decl())
assert_false(decode_clang_entity_identity(truncated(enc, 40)).ok)
assert_false(decode_clang_entity_identity(
    truncated(enc, enc.len() - 1)).ok)
```

</details>

#### rejects trailing bytes after a complete record

- rejects trailing bytes after a complete record


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trailing bytes after a complete record")
assert_false(decode_clang_entity_identity(
    with_trailing_byte(encode_clang_entity_identity(identity_decl()))).ok)
```

</details>

#### rejects a cross-typed buffer carrying another record's magic

- rejects a cross-typed buffer carrying another record's magic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a cross-typed buffer carrying another record's magic")
assert_false(decode_clang_entity_identity(
    encode_clang_adapter_capability(clang_this_build_capability())).ok)
```

</details>

#### rejects a wrong schema version rather than negotiating

- rejects a wrong schema version rather than negotiating


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong schema version rather than negotiating")
val bad = corrupt_byte(encode_clang_entity_identity(identity_decl()), 4, 2)
assert_false(decode_clang_entity_identity(bad).ok)
```

</details>

#### rejects a non-zero envelope reserved field

- rejects a non-zero envelope reserved field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a non-zero envelope reserved field")
val bad = corrupt_byte(encode_clang_entity_identity(identity_decl()), 6, 1)
assert_false(decode_clang_entity_identity(bad).ok)
```

</details>

### ClangAdapterCapability — exact bytes

#### encodes the zero capability to the frozen 14-byte body

- encodes the zero capability to the frozen 14-byte body


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the zero capability to the frozen 14-byte body")
expect(wire_to_hex(encode_clang_adapter_capability(
    clang_adapter_capability(0, 0, 0, 0, 0, 0)))).to_equal(GOLDEN_CAP_ZERO)
```

</details>

#### encodes what this wave-1 build actually advertises

- encodes what this wave-1 build actually advertises


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes what this wave-1 build actually advertises")
expect(wire_to_hex(encode_clang_adapter_capability(
    clang_this_build_capability()))).to_equal(GOLDEN_CAP_THIS_BUILD)
```

</details>

#### encodes the five adapter versions in declaration order

- encodes the five adapter versions in declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the five adapter versions in declaration order")
expect(wire_to_hex(encode_clang_adapter_capability(
    clang_adapter_capability(18, 1, 2, 3, 4, CLANG_FEATURE_SET_ALL))))
    .to_equal(GOLDEN_CAP_FULL)
```

</details>

#### encodes the maximum legal capability

- encodes the maximum legal capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the maximum legal capability")
expect(wire_to_hex(encode_clang_adapter_capability(
    clang_adapter_capability(0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
                             CLANG_FEATURE_SET_ALL))))
    .to_equal(GOLDEN_CAP_MAX)
```

</details>

### ClangAdapterCapability — round trip and rejection

#### reconstructs a fully-featured advertisement

- reconstructs a fully-featured advertisement


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs a fully-featured advertisement")
val cap = clang_adapter_capability(18, 1, 2, 3, 4, CLANG_FEATURE_SET_ALL)
val r = decode_clang_adapter_capability(
    encode_clang_adapter_capability(cap))
assert_true(r.ok)
assert_true(clang_adapter_capability_equal(r.value, cap))
```

</details>

#### still decodes an advertisement from an unsupported major, so it can be refused with a reason

- still decodes an advertisement from an unsupported major, so it can be refused with a reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still decodes an advertisement from an unsupported major, so it can be refused with a reason")
val cap = clang_adapter_capability(99, 1, 1, 1, 1, CLANG_FEATURE_SET_ALL)
val r = decode_clang_adapter_capability(
    encode_clang_adapter_capability(cap))
assert_true(r.ok)
assert_equal(r.value.clang_major, 99)
```

</details>

#### rejects an empty buffer

- rejects an empty buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty buffer")
assert_false(decode_clang_adapter_capability(empty_bytes()).ok)
```

</details>

#### rejects a truncated, over-long or cross-typed buffer

- rejects a truncated, over-long or cross-typed buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated, over-long or cross-typed buffer")
val enc = encode_clang_adapter_capability(clang_this_build_capability())
assert_false(decode_clang_adapter_capability(
    truncated(enc, enc.len() - 1)).ok)
assert_false(decode_clang_adapter_capability(with_trailing_byte(enc)).ok)
assert_false(decode_clang_adapter_capability(
    encode_clang_entity_identity(identity_decl())).ok)
```

</details>

### Adapter acceptance carries a reason receipt (shared rule 4)

#### accepts this build when only AST export is required

- accepts this build when only AST export is required


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts this build when only AST export is required")
val d = clang_capability_decide(clang_this_build_capability(),
                                CLANG_FEATURE_AST_EXPORT)
assert_true(d.accepted)
assert_equal(clang_reject_reason_to_u8(d.reason), 0)
```

</details>

#### refuses an unsupported major and says so

- refuses an unsupported major and says so


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an unsupported major and says so")
val cap = clang_adapter_capability(99, CLANG_AST_EXPORT_SCHEMA, 1, 1, 1,
                                   CLANG_FEATURE_SET_ALL)
val d = clang_capability_decide(cap, CLANG_FEATURE_AST_EXPORT)
assert_false(d.accepted)
assert_equal(clang_reject_reason_to_u8(d.reason), 1)
```

</details>

#### refuses unknown feature bits before blaming a missing feature

- refuses unknown feature bits before blaming a missing feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses unknown feature bits before blaming a missing feature")
val cap = clang_adapter_capability(18, CLANG_AST_EXPORT_SCHEMA, 1, 1, 1,
                                   CLANG_FEATURE_SET_ALL + 1)
val d = clang_capability_decide(cap, CLANG_FEATURE_AST_EXPORT)
assert_false(d.accepted)
assert_equal(clang_reject_reason_to_u8(d.reason), 7)
```

</details>

#### refuses an export schema mismatch

- refuses an export schema mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an export schema mismatch")
val cap = clang_adapter_capability(18, CLANG_AST_EXPORT_SCHEMA + 1, 1, 1,
                                   1, CLANG_FEATURE_SET_ALL)
val d = clang_capability_decide(cap, CLANG_FEATURE_AST_EXPORT)
assert_false(d.accepted)
assert_equal(clang_reject_reason_to_u8(d.reason), 2)
```

</details>

#### refuses a capability that does not advertise the required feature

- refuses a capability that does not advertise the required feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a capability that does not advertise the required feature")
val d = clang_capability_decide(clang_this_build_capability(),
                                CLANG_FEATURE_MATCHER_QUERY)
assert_false(d.accepted)
assert_equal(clang_reject_reason_to_u8(d.reason), 6)
```

</details>

#### refuses a matcher requirement when the adapter version is unset

- refuses a matcher requirement when the adapter version is unset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a matcher requirement when the adapter version is unset")
val cap = clang_adapter_capability(18, CLANG_AST_EXPORT_SCHEMA, 0, 1, 1,
                                   CLANG_FEATURE_SET_ALL)
val d = clang_capability_decide(cap, CLANG_FEATURE_MATCHER_QUERY)
assert_false(d.accepted)
assert_equal(clang_reject_reason_to_u8(d.reason), 3)
```

</details>

#### refuses a transform requirement when the transformer version is unset

- refuses a transform requirement when the transformer version is unset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a transform requirement when the transformer version is unset")
val cap = clang_adapter_capability(18, CLANG_AST_EXPORT_SCHEMA, 1, 0, 1,
                                   CLANG_FEATURE_SET_ALL)
val d = clang_capability_decide(cap, CLANG_FEATURE_SOURCE_TRANSFORM)
assert_false(d.accepted)
assert_equal(clang_reject_reason_to_u8(d.reason), 4)
```

</details>

#### refuses an LLVM pass requirement when the IR schema is unset

- refuses an LLVM pass requirement when the IR schema is unset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an LLVM pass requirement when the IR schema is unset")
val cap = clang_adapter_capability(18, CLANG_AST_EXPORT_SCHEMA, 1, 1, 0,
                                   CLANG_FEATURE_SET_ALL)
val d = clang_capability_decide(cap, CLANG_FEATURE_LLVM_PASS)
assert_false(d.accepted)
assert_equal(clang_reject_reason_to_u8(d.reason), 5)
```

</details>

### ClangAstExport — exact bytes

#### encodes an export with no nodes at all

- encodes an export with no nodes at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes an export with no nodes at all")
expect(wire_to_hex(encode_clang_ast_export(
    clang_empty_export(clang_zero_artifact(),
                       CLANG_SUPPORTED_MAJOR_PRIMARY))))
    .to_equal(GOLDEN_EXPORT_EMPTY)
```

</details>

#### encodes a two-node arena column-major with the columns in frozen order

- encodes a two-node arena column-major with the columns in frozen order


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a two-node arena column-major with the columns in frozen order")
expect(wire_to_hex(encode_clang_ast_export(export_two())))
    .to_equal(GOLDEN_EXPORT_TWO)
```

</details>

### ClangAstExport — empty input

#### treats a zero-node export as valid rather than as an error

- treats a zero-node export as valid rather than as an error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a zero-node export as valid rather than as an error")
val e = clang_empty_export(tu_artifact(), CLANG_SUPPORTED_MAJOR_PRIMARY)
assert_true(clang_export_valid(e))
assert_equal(clang_export_node_count(e), 0)
```

</details>

#### round-trips a zero-node export

- round-trips a zero-node export


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a zero-node export")
val e = clang_empty_export(tu_artifact(), CLANG_SUPPORTED_MAJOR_PRIMARY)
val r = decode_clang_ast_export(encode_clang_ast_export(e))
assert_true(r.ok)
assert_equal(clang_export_node_count(r.value), 0)
assert_true(clang_export_equal(r.value, e))
```

</details>

#### finds no node for any identity in an empty export

- finds no node for any identity in an empty export


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds no node for any identity in an empty export")
val e = clang_empty_export(tu_artifact(), CLANG_SUPPORTED_MAJOR_PRIMARY)
assert_equal(clang_export_index_of(e, identity_decl()), -1)
```

</details>

#### rejects a completely empty buffer

- rejects a completely empty buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a completely empty buffer")
assert_false(decode_clang_ast_export(empty_bytes()).ok)
```

</details>

### ClangAstExport — round trip

#### reconstructs a two-node arena including its absent ids

- reconstructs a two-node arena including its absent ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs a two-node arena including its absent ids")
val r = decode_clang_ast_export(encode_clang_ast_export(export_two()))
assert_true(r.ok)
assert_true(clang_export_equal(r.value, export_two()))
assert_equal(clang_export_node_count(r.value), 2)
```

</details>

#### preserves which node is a root

- preserves which node is a root


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves which node is a root")
val r = decode_clang_ast_export(encode_clang_ast_export(export_two()))
assert_true(clang_export_is_root(r.value, 0))
assert_false(clang_export_is_root(r.value, 1))
```

</details>

### ClangAstExport — durable identity resolution

#### reconstructs a node's identity from the arena

- reconstructs a node's identity from the arena


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs a node's identity from the arena")
assert_true(clang_entity_identity_equal(
    clang_identity_of(export_two(), 0), identity_node0()))
```

</details>

#### resolves an identity back to its node index

- resolves an identity back to its node index


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves an identity back to its node index")
assert_equal(clang_export_index_of(export_two(), identity_node0()), 0)
```

</details>

#### resolves the second node, distinguishing it by ordinal and anchor

- resolves the second node, distinguishing it by ordinal and anchor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the second node, distinguishing it by ordinal and anchor")
assert_equal(clang_export_index_of(export_two(),
                                   clang_identity_of(export_two(), 1)), 1)
```

</details>

#### refuses an identity that differs only in local ordinal

- refuses an identity that differs only in local ordinal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an identity that differs only in local ordinal")
assert_equal(clang_export_index_of(export_two(), identity_decl()), -1)
```

</details>

#### refuses an identity belonging to a different translation unit

- refuses an identity belonging to a different translation unit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an identity belonging to a different translation unit")
val foreign = clang_entity_identity(src_artifact(), 0x2a, anchor_zero(),
                                    0x00abcdef, 9)
assert_equal(clang_export_index_of(export_two(), foreign), -1)
```

</details>

#### refuses an identity whose ordinal does not match any node

- refuses an identity whose ordinal does not match any node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an identity whose ordinal does not match any node")
val wrong = clang_entity_identity(tu_artifact(), 0x2a, anchor_zero(),
                                  0x00abcdef, 77)
assert_equal(clang_export_index_of(export_two(), wrong), -1)
```

</details>

### ClangAstExport — rejection

#### rejects a producer Clang major outside the supported set

- rejects a producer Clang major outside the supported set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a producer Clang major outside the supported set")
val bad = corrupt_byte(encode_clang_ast_export(export_two()),
                       OFF_MAJOR, 99)
assert_false(decode_clang_ast_export(bad).ok)
```

</details>

#### rejects a node count that does not consume the buffer exactly

- rejects a node count that does not consume the buffer exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a node count that does not consume the buffer exactly")
val bad = corrupt_byte(encode_clang_ast_export(export_two()),
                       OFF_NODE_COUNT, 3)
assert_false(decode_clang_ast_export(bad).ok)
```

</details>

#### rejects trailing bytes after a complete record

- rejects trailing bytes after a complete record


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trailing bytes after a complete record")
assert_false(decode_clang_ast_export(
    with_trailing_byte(encode_clang_ast_export(export_two()))).ok)
```

</details>

#### rejects a truncated record

- rejects a truncated record


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated record")
val enc = encode_clang_ast_export(export_two())
assert_false(decode_clang_ast_export(truncated(enc, 20)).ok)
assert_false(decode_clang_ast_export(truncated(enc, enc.len() - 1)).ok)
```

</details>

#### rejects a reserved node-flag bit instead of ignoring it

- rejects a reserved node-flag bit instead of ignoring it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a reserved node-flag bit instead of ignoring it")
val bad = corrupt_byte(encode_clang_ast_export(export_two()),
                       OFF_FLAGS_0_HIGH, 0x80)
assert_false(decode_clang_ast_export(bad).ok)
```

</details>

#### rejects a parent that is not emitted before its child

- rejects a parent that is not emitted before its child


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a parent that is not emitted before its child")
val bad = corrupt_byte(encode_clang_ast_export(export_two()),
                       OFF_PARENT_1, 1)
assert_false(decode_clang_ast_export(bad).ok)
```

</details>

#### rejects a wrong schema version and a non-zero reserved field

- rejects a wrong schema version and a non-zero reserved field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong schema version and a non-zero reserved field")
val enc = encode_clang_ast_export(export_two())
assert_false(decode_clang_ast_export(corrupt_byte(enc, 4, 2)).ok)
assert_false(decode_clang_ast_export(corrupt_byte(enc, 6, 1)).ok)
```

</details>

#### rejects a cross-typed buffer carrying another record's magic

- rejects a cross-typed buffer carrying another record's magic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a cross-typed buffer carrying another record's magic")
assert_false(decode_clang_ast_export(
    encode_clang_entity_identity(identity_decl())).ok)
```

</details>

#### refuses to encode an arena whose columns disagree in length

- refuses to encode an arena whose columns disagree in length


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to encode an arena whose columns disagree in length")
var kind: [u32] = []
kind.push(1)
kind.push(2)
var short: [u32] = []
short.push(0)
var anchor: [SourceAnchor] = []
anchor.push(clang_zero_source_anchor())
val e = clang_ast_export(tu_artifact(), CLANG_SUPPORTED_MAJOR_PRIMARY,
                         kind, short, short, short, short, anchor)
assert_false(clang_export_valid(e))
assert_equal(encode_clang_ast_export(e).len(), 0)
```

</details>

#### refuses to encode an arena produced by an unsupported Clang major

- refuses to encode an arena produced by an unsupported Clang major


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to encode an arena produced by an unsupported Clang major")
val e = clang_empty_export(tu_artifact(), 99)
assert_false(clang_export_valid(e))
assert_equal(encode_clang_ast_export(e).len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/clang_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Supported Clang majors (architecture 12.6), ClangFeatureSet — the CapabilitySet wire slot, ClangNodeFlags and the rewrite-policy gate (architecture 12.3), ClangRejectReason wire discriminants, ClangEntityIdentity — exact bytes, ClangEntityIdentity — round trip, ClangEntityIdentity — rejection, ClangAdapterCapability — exact bytes, ClangAdapterCapability — round trip and rejection, Adapter acceptance carries a reason receipt (shared rule 4), ClangAstExport — exact bytes, ClangAstExport — empty input, ClangAstExport — round trip, ClangAstExport — durable identity resolution, ClangAstExport — rejection.
- Supported Clang majors (architecture 12.6)
- ClangFeatureSet — the CapabilitySet wire slot
- ClangNodeFlags and the rewrite-policy gate (architecture 12.3)
- ClangRejectReason wire discriminants
- ClangEntityIdentity — exact bytes
- ClangEntityIdentity — round trip
- ClangEntityIdentity — rejection
- ClangAdapterCapability — exact bytes
- ClangAdapterCapability — round trip and rejection
- Adapter acceptance carries a reason receipt (shared rule 4)
- ClangAstExport — exact bytes
- ClangAstExport — empty input
- ClangAstExport — round trip
- ClangAstExport — durable identity resolution
- ClangAstExport — rejection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 64 |
| Active scenarios | 64 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `905835f0e7017436f9bb4a88fa5a1de52ae22655c09c169f839c6a051a53027c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `905835f0e7017436f9bb4a88fa5a1de52ae22655c09c169f839c6a051a53027c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `905835f0e7017436f9bb4a88fa5a1de52ae22655c09c169f839c6a051a53027c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/clang_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/clang_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/clang_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/clang_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/clang_contract_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only the majors this repo builds and tests an adapter for' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/clang_contract_spec.spl:225:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown major rather than assuming ABI compatibility' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/clang_contract_spec.spl:234:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the frozen five-bit vocabulary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
