# Type Domain Resolver Normalization Specification

> <details>

<!-- sdn-diagram:id=type_domain_resolver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_domain_resolver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_domain_resolver_spec -> std
type_domain_resolver_spec -> parser
type_domain_resolver_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_domain_resolver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Domain Resolver Normalization Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/module_resolver/type_domain_resolver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### type domain resolver normalization

#### maps bare single-segment imports into the default type domain

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolver = ModuleResolver.new("/workspace", "/workspace/src")
val segments = normalize_type_segments(resolver, ["I64"])
expect(segments.len()).to_equal(3)
expect(segments[0]).to_equal("type")
expect(segments[1]).to_equal("simple_lang")
expect(segments[2]).to_equal("I64")
```

</details>

#### maps explicit owned-domain imports onto underscore-backed disk paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolver = ModuleResolver.new("/workspace", "/workspace/src")
val segments = normalize_type_segments(resolver, ["simple-lang/I64"])
expect(segments.len()).to_equal(3)
expect(segments[0]).to_equal("type")
expect(segments[1]).to_equal("simple_lang")
expect(segments[2]).to_equal("I64")
```

</details>

#### leaves crate imports untouched

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolver = ModuleResolver.new("/workspace", "/workspace/src")
val segments = normalize_type_segments(resolver, ["crate", "compiler", "core"])
expect(segments.len()).to_equal(3)
expect(segments[0]).to_equal("crate")
expect(segments[1]).to_equal("compiler")
expect(segments[2]).to_equal("core")
```

</details>

#### exposes public child modules through domain facade glob exports

1. Ok
2. ModulePath
3. Ok
   - Expected: exports contains `I64`
   - Expected: exports contains `Text`
   - Expected: exports does not contain `internal`
4. Err
5. fail
6. Err
7. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolver = ModuleResolver.new("/workspace", "/workspace/src")
val manifest_source = "mod simple_lang\npub mod I64\npub mod Text\nmod internal\nexport use type.simple_lang.*\n"
val manifest_result = resolver.parse_manifest(manifest_source, "/workspace/src/type/simple_lang")
match manifest_result:
    Ok(manifest):
        val resolved = ResolvedModule.directory(
            "/workspace/src/type/simple_lang/__init__.spl",
            ModulePath(segments: ["type", "simple_lang"]),
            manifest
        )
        val exports_result = resolver.get_exports(resolved)
        match exports_result:
            Ok(exports):
                expect(exports.contains("I64")).to_equal(true)
                expect(exports.contains("Text")).to_equal(true)
                expect(exports.contains("internal")).to_equal(false)
            Err(_):
                fail("type-domain resolver failed to read exports")
    Err(_):
        fail("type-domain resolver failed to load manifest")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
