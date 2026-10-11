# Collection Algorithm Attribute Specification

> Tests covering collection algorithm declaration attribute.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Algorithm Attribute Specification

## Scenarios

### collection algorithm declaration attribute

#### rewrites only the attributed initializer

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"hash\")\nvar chosen = AdaptiveTextSet.new()")
val declaration = parse_statement()
expect(parser_has_errors()).to_be(false)
expect(stmt_get_tag(declaration)).to_equal(STMT_VAR_DECL)
val init = stmt_get_expr(declaration)
expect(expr_get_tag(init)).to_equal(EXPR_METHOD_CALL)
expect(expr_get_str(init)).to_equal("attributed_at_site")
val args = expr_get_args(init)
expect(args.len()).to_equal(3)
expect(expr_get_tag(args[0])).to_equal(EXPR_METHOD_CALL)
expect(expr_get_str(args[0])).to_equal("new")
expect(expr_get_tag(args[1])).to_equal(EXPR_STRING_LIT)
expect(expr_get_str(args[1])).to_equal("hash")
expect(expr_get_str(args[2])).to_start_with("ast://")
expect(expr_get_str(args[2])).to_contain("/local/chosen#")
```

</details>

#### accepts an immutable declaration and retains its original initializer

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"ordered\")\nval chosen = AdaptiveTextSet.with_site_and_target(policy, \"ast://module/chosen#stable\", target)")
val declaration = parse_statement()
expect(parser_has_errors()).to_be(false)
expect(stmt_get_tag(declaration)).to_equal(STMT_VAL_DECL)
val attributed = stmt_get_expr(declaration)
val args = expr_get_args(attributed)
expect(expr_get_str(attributed)).to_equal("attributed_at_site")
expect(expr_get_str(args[0])).to_equal("with_site_and_target")
expect(expr_get_str(args[1])).to_equal("ordered")
```

</details>

#### uses an explicit literal site for exact profile lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manual_site = "ast://module/manual#stable"
val prior = AdaptiveSetWorkloadProfile(
    site_id: manual_site, target_profile_id: "x86_64-v3", sample_count: 1,
    size_p95: 12, lookup_count_p95: 100,
    hit_count_p95: 80, miss_count_p95: 20
)
expect(parser_collection_feedback_install("x86_64-v3", [prior])).to_be(true)
parser_init("@collection_algorithm(\"auto\")\nval chosen = AdaptiveTextSet.with_site_and_target(policy, \"ast://module/manual#stable\", \"x86_64-v3\")")
val rewritten = stmt_get_expr(parse_statement())
expect(parser_has_errors()).to_be(false)
expect(expr_get_str(rewritten)).to_equal("attributed_with_prior_at_site")
expect(expr_get_str(expr_get_args(rewritten)[2])).to_equal(manual_site)
parser_collection_feedback_clear()
```

</details>

#### rejects an unprovable explicit site or target during profile replay

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prior = AdaptiveSetWorkloadProfile(
    site_id: "ast://module/manual#stable", target_profile_id: "x86_64-v3",
    sample_count: 1, size_p95: 12, lookup_count_p95: 100,
    hit_count_p95: 80, miss_count_p95: 20
)
expect(parser_collection_feedback_install("x86_64-v3", [prior])).to_be(true)
parser_init("@collection_algorithm(\"auto\")\nval chosen = AdaptiveTextSet.with_site_and_target(policy, site, \"x86_64-v3\")")
parse_statement()
expect(parser_has_errors()).to_be(true)
parser_init("@collection_algorithm(\"auto\")\nval chosen = AdaptiveTextSet.with_site_and_target(policy, \"ast://module/manual#stable\", \"other-target\")")
parse_statement()
expect(parser_has_errors()).to_be(true)
parser_collection_feedback_clear()
```

</details>

#### requires a literal explicit site even without profile replay

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"auto\")\nval chosen = AdaptiveTextSet.with_site_and_target(policy, site, target)")
parse_statement()
expect(parser_has_errors()).to_be(true)
```

</details>

#### routes a directly constructed text map to the map attribute API

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"ordered\")\nvar mapping = AdaptiveTextMap.new()")
val declaration = parse_statement()
expect(parser_has_errors()).to_be(false)
val attributed = stmt_get_expr(declaration)
expect(expr_get_str(attributed)).to_equal("attributed_at_site")
expect(expr_get_str(expr_get_left(attributed))).to_equal("AdaptiveTextMap")
```

</details>

#### routes a directly constructed generic map without changing its family

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"ordered\")\nvar mapping = AdaptiveMap.new()")
val declaration = parse_statement()
expect(parser_has_errors()).to_be(false)
val attributed = stmt_get_expr(declaration)
expect(expr_get_str(attributed)).to_equal("attributed_at_site")
expect(expr_get_str(expr_get_left(attributed))).to_equal("AdaptiveMap")
```

</details>

#### uses a written text-set type for a factory initializer

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"hash\")\nval chosen: AdaptiveTextSet = make_set()")
val attributed = stmt_get_expr(parse_statement())
expect(parser_has_errors()).to_be(false)
expect(expr_get_str(attributed)).to_equal("attributed_at_site")
expect(expr_get_str(expr_get_left(attributed))).to_equal("AdaptiveTextSet")
expect(expr_get_str(expr_get_args(attributed)[1])).to_equal("hash")
```

</details>

#### retains a written generic-map family when the flat type tag erases its arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"ordered\")\nvar chosen: AdaptiveMap<i64, text> = make_map()")
val attributed = stmt_get_expr(parse_statement())
expect(parser_has_errors()).to_be(false)
expect(expr_get_str(attributed)).to_equal("attributed_at_site")
expect(expr_get_str(expr_get_left(attributed))).to_equal("AdaptiveMap")
```

</details>

#### rejects a direct constructor that disagrees with the written family

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"hash\")\nval chosen: AdaptiveTextSet = AdaptiveTextMap.new()")
parse_statement()
expect(parser_has_errors()).to_be(true)
```

</details>

#### derives the same site identity from identical source

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "@collection_algorithm(\"auto\")\nval chosen = AdaptiveTextSet.new()"
parser_init(source)
val first = expr_get_str(expr_get_args(stmt_get_expr(parse_statement()))[2])
parser_init(source)
val second = expr_get_str(expr_get_args(stmt_get_expr(parse_statement()))[2])
expect(first).to_equal(second)
```

</details>

#### matches the Rust parser's exact declaration site identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main():\n    @collection_algorithm(\"auto\")\n    var hot = AdaptiveTextSet.new()\n"
parser_init_with_path(source, "app/collection_probe.spl")
parse_module_body()
expect(parser_has_errors()).to_be(false)
val body = decl_get_body(module_get_decls()[0])
val site = expr_get_str(expr_get_args(stmt_get_expr(body[0]))[2])
expect(site).to_equal("ast://app/collection_probe.spl/main/local/hot#-7095170762293803234")
```

</details>

#### uses the same declaration site for an absolute source below the process directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main():\n    @collection_algorithm(\"auto\")\n    var hot = AdaptiveTextSet.new()\n"
val path = "{cwd_process()}/app/collection_probe.spl"
parser_init_with_path(source, path)
parse_module_body()
expect(parser_has_errors()).to_be(false)
val body = decl_get_body(module_get_decls()[0])
val site = expr_get_str(expr_get_args(stmt_get_expr(body[0]))[2])
expect(site).to_equal("ast://app/collection_probe.spl/main/local/hot#-7095170762293803234")
expect(parser_collection_module_key(path)).to_equal("app/collection_probe.spl")
```

</details>

#### matches the Rust parser's exact field site identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Store:\n    @collection_algorithm(\"ordered\")\n    values: AdaptiveTextSet = AdaptiveTextSet.new()\n"
parser_init_with_path(source, "app/collection_probe.spl")
parse_module_body()
expect(parser_has_errors()).to_be(false)
val defaults = decl_get_field_defaults(module_get_decls()[0])
val site = expr_get_str(expr_get_args(defaults[0])[2])
expect(site).to_equal("ast://app/collection_probe.spl/Store/values#-555445139409988573")
```

</details>

#### keeps nested field owners distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_collection_site_reset()
val prior_outer = parser_collection_site_owner_push("Outer")
val prior_inner = parser_collection_site_owner_push("Inner")
val nested_site = parser_collection_field_site_id("module.spl", "values", 123)
parser_collection_site_owner_restore(prior_inner)
parser_collection_site_owner_restore(prior_outer)
expect(nested_site).to_equal("ast://module.spl/Outer/Inner/values#123")
```

</details>

#### keeps a local site and its feedback when the algorithm changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val declaration = "val chosen = AdaptiveTextSet.new()"
parser_init_with_path("@collection_algorithm(\"auto\")\n" + declaration, "collection_switch.spl")
val first = expr_get_str(expr_get_args(stmt_get_expr(parse_statement()))[2])
val prior = AdaptiveSetWorkloadProfile(
    site_id: first, target_profile_id: "x86_64-v3", sample_count: 1,
    size_p95: 12, lookup_count_p95: 100,
    hit_count_p95: 80, miss_count_p95: 20
)
expect(parser_collection_feedback_install("x86_64-v3", [prior])).to_be(true)
parser_init_with_path("@collection_algorithm(\"ordered\")\n" + declaration, "collection_switch.spl")
val rewritten = stmt_get_expr(parse_statement())
expect(expr_get_str(rewritten)).to_equal("attributed_with_prior_at_site")
expect(expr_get_str(expr_get_args(rewritten)[2])).to_equal(first)
expect(expr_get_str(expr_get_args(rewritten)[1])).to_equal("ordered")
parser_collection_feedback_clear()
```

</details>

#### keeps local feedback attached after unrelated text is inserted before its declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val declaration = "@collection_algorithm(\"auto\")\nval chosen = AdaptiveTextSet.new()"
parser_init_with_path(declaration, "collection_identity.spl")
val site = expr_get_str(expr_get_args(stmt_get_expr(parse_statement()))[2])
val prior = AdaptiveSetWorkloadProfile(
    site_id: site, target_profile_id: "x86_64-v3", sample_count: 1,
    size_p95: 12, lookup_count_p95: 100,
    hit_count_p95: 80, miss_count_p95: 20
)
expect(parser_collection_feedback_install("x86_64-v3", [prior])).to_be(true)
parser_init_with_path("# unrelated comment\n\n" + declaration, "collection_identity.spl")
val rewritten = stmt_get_expr(parse_statement())
expect(expr_get_str(rewritten)).to_equal("attributed_with_prior_at_site")
expect(expr_get_str(expr_get_args(rewritten)[2])).to_equal(site)
parser_collection_feedback_clear()
```

</details>

#### assigns distinct identities to identical local declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val declaration = "@collection_algorithm(\"auto\")\nval chosen = AdaptiveTextSet.new()\n"
parser_init(declaration + declaration)
val first = expr_get_str(expr_get_args(stmt_get_expr(parse_statement()))[2])
parser_skip_newlines()
val second = expr_get_str(expr_get_args(stmt_get_expr(parse_statement()))[2])
expect(first == second).to_be(false)
expect(second).to_start_with(first + ":")
```

</details>

#### includes the enclosing function in an attributed local identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn left():\n" +
    "    @collection_algorithm(\"auto\")\n" +
    "    val chosen = AdaptiveTextSet.new()\n" +
    "fn right():\n" +
    "    @collection_algorithm(\"auto\")\n" +
    "    val chosen = AdaptiveTextSet.new()\n"
parser_init_with_path(source, "collection_owner_identity.spl")
parse_module_body()
expect(parser_has_errors()).to_be(false)
val decls = module_get_decls()
val left_site = expr_get_str(expr_get_args(stmt_get_expr(decl_get_body(decls[0])[0]))[2])
val right_site = expr_get_str(expr_get_args(stmt_get_expr(decl_get_body(decls[1])[0]))[2])
expect(left_site).to_contain("/left/local/chosen#")
expect(right_site).to_contain("/right/local/chosen#")
expect(left_site == right_site).to_be(false)
```

</details>

#### embeds admitted site feedback in the initializer before interpretation

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "@collection_algorithm(\"auto\")\nval chosen = AdaptiveTextSet.new()"
parser_init(source)
val site = expr_get_str(expr_get_args(stmt_get_expr(parse_statement()))[2])
val prior = AdaptiveSetWorkloadProfile(
    site_id: site, target_profile_id: "x86_64-v3", sample_count: 2,
    size_p95: 12, lookup_count_p95: 100,
    hit_count_p95: 80, miss_count_p95: 20,
    hash_probe_count_p95: 100, hash_collision_count_p95: 40
)
expect(parser_collection_feedback_install("x86_64-v3", [prior])).to_be(true)
parser_init(source)
val rewritten = stmt_get_expr(parse_statement())
expect(expr_get_str(rewritten)).to_equal("attributed_with_prior_at_site")
val rewritten_args = expr_get_args(rewritten)
expect(rewritten_args.len()).to_equal(11)
expect(expr_get_str(rewritten_args[0])).to_equal("new")
parser_collection_feedback_clear()
```

</details>

#### rejects unknown algorithms before lowering

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"unknown\")\nval chosen = AdaptiveTextSet.new()")
parse_statement()
expect(parser_has_errors()).to_be(true)
```

</details>

#### rejects an unrelated constructor without rewriting the initializer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"hash\")\nval chosen = HashMap.new()")
val declaration = parse_statement()
expect(parser_has_errors()).to_be(true)
expect(expr_get_str(stmt_get_expr(declaration))).to_equal("new")
```

</details>

#### rejects non-constructor methods on an adaptive family

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"hash\")\nval chosen = AdaptiveTextSet.clear()")
parse_statement()
expect(parser_has_errors()).to_be(true)
parser_init("@collection_algorithm(\"ordered\")\nval chosen = AdaptiveMap.with_attribute()")
parse_statement()
expect(parser_has_errors()).to_be(true)
```

</details>

#### rejects an unrelated class field default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Holder:\n    @collection_algorithm(\"ordered\")\n    items: HashMap = HashMap.new()\n"
parser_init_with_path(source, "collection_field_wrong_family.spl")
parse_module_body()
expect(parser_has_errors()).to_be(true)
```

</details>

#### requires an initialized declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"linear\")\nvar chosen: AdaptiveTextSet")
parse_statement()
expect(parser_has_errors()).to_be(true)
```

</details>

#### rejects use on a non-declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("@collection_algorithm(\"ordered\")\nprint(42)")
parse_statement()
expect(parser_has_errors()).to_be(true)
```

</details>

#### rewrites one initialized class field default with a stable site

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Holder:\n    @collection_algorithm(\"ordered\")\n    items: AdaptiveTextSet = AdaptiveTextSet.new()\n"
parser_init_with_path(source, "collection_field.spl")
parse_module_body()
expect(parser_has_errors()).to_be(false)
val declarations = module_get_decls()
val defaults = decl_get_field_defaults(declarations[0])
expect(defaults.len()).to_equal(1)
expect(expr_get_str(defaults[0])).to_equal("attributed_at_site")
val args = expr_get_args(defaults[0])
expect(expr_get_str(args[1])).to_equal("ordered")
expect(expr_get_str(args[2])).to_contain("/Holder/items#")
```

</details>

#### rewrites a typed class field initialized by a factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Holder:\n    @collection_algorithm(\"ordered\")\n    items: AdaptiveTextSet = make_set()\n"
parser_init_with_path(source, "collection_field_factory.spl")
parse_module_body()
expect(parser_has_errors()).to_be(false)
val default_value = decl_get_field_defaults(module_get_decls()[0])[0]
expect(expr_get_str(default_value)).to_equal("attributed_at_site")
expect(expr_get_str(expr_get_left(default_value))).to_equal("AdaptiveTextSet")
```

</details>

#### keeps field identity after unrelated text before its class

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val declaration = "class Holder:\n    @collection_algorithm(\"ordered\")\n    items: AdaptiveTextSet = AdaptiveTextSet.new()\n"
parser_init_with_path(declaration, "collection_field_identity.spl")
parse_module_body()
val first_decl = module_get_decls()[0]
val first_default = decl_get_field_defaults(first_decl)[0]
val first_site = expr_get_str(expr_get_args(first_default)[2])
parser_init_with_path("# unrelated comment\n\n" + declaration, "collection_field_identity.spl")
parse_module_body()
val second_decl = module_get_decls()[0]
val second_default = decl_get_field_defaults(second_decl)[0]
expect(expr_get_str(expr_get_args(second_default)[2])).to_equal(first_site)
```

</details>

#### keeps a field site when its algorithm changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first_source = "class Holder:\n    @collection_algorithm(\"auto\")\n    items: AdaptiveTextSet = AdaptiveTextSet.new()\n"
val second_source = "class Holder:\n    @collection_algorithm(\"ordered\")\n    items: AdaptiveTextSet = AdaptiveTextSet.new()\n"
parser_init_with_path(first_source, "collection_field_switch.spl")
parse_module_body()
expect(parser_has_errors()).to_be(false)
val first_default = decl_get_field_defaults(module_get_decls()[0])[0]
val first_site = expr_get_str(expr_get_args(first_default)[2])
parser_init_with_path(second_source, "collection_field_switch.spl")
parse_module_body()
expect(parser_has_errors()).to_be(false)
val second_default = decl_get_field_defaults(module_get_decls()[0])[0]
expect(expr_get_str(expr_get_args(second_default)[2])).to_equal(first_site)
expect(expr_get_str(expr_get_args(second_default)[1])).to_equal("ordered")
```

</details>

#### rejects an attributed field without a default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "struct Holder:\n    @collection_algorithm(\"hash\")\n    items: AdaptiveTextSet\n"
parser_init_with_path(source, "collection_field_missing_default.spl")
parse_module_body()
expect(parser_has_errors()).to_be(true)
```

</details>

#### rejects a field attribute followed by a method

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Holder:\n    @collection_algorithm(\"ordered\")\n    fn size(self) -> i64:\n        0\n"
parser_init_with_path(source, "collection_attribute_method.spl")
parse_module_body()
expect(parser_has_errors()).to_be(true)
```

</details>

#### rejects a field attribute followed by pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Holder:\n    @collection_algorithm(\"ordered\")\n    pass\n"
parser_init_with_path(source, "collection_attribute_pass.spl")
parse_module_body()
expect(parser_has_errors()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `C:\dev\simple\build\native_probe\phase1-collection-init-repair-20261010\test\01_unit\compiler\parser\collection_algorithm_attribute_spec.spl` |
| Updated | 2026-10-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering collection algorithm declaration attribute.
- collection algorithm declaration attribute

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
