# Access Policy Specification

> 1. expect policy is open

<!-- sdn-diagram:id=access_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=access_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

access_policy_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=access_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Access Policy Specification

## Scenarios

### AccessPolicy

#### enum values

#### Open is open

1. expect policy is open
2. expect not policy is boundary
3. expect not policy is bypass


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = AccessPolicy.Open
expect policy.is_open()
expect not policy.is_boundary()
expect not policy.is_bypass()
```

</details>

#### Boundary is boundary

1. expect not policy is open
2. expect policy is boundary
3. expect not policy is bypass


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = AccessPolicy.Boundary
expect not policy.is_open()
expect policy.is_boundary()
expect not policy.is_bypass()
```

</details>

#### Bypass is bypass

1. expect not policy is open
2. expect not policy is boundary
3. expect policy is bypass


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = AccessPolicy.Bypass
expect not policy.is_open()
expect not policy.is_boundary()
expect policy.is_bypass()
```

</details>

#### to_string

#### Open converts to string

1. expect AccessPolicy Open to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect AccessPolicy.Open.to_string() == "Open"
```

</details>

#### Boundary converts to string

1. expect AccessPolicy Boundary to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect AccessPolicy.Boundary.to_string() == "Boundary"
```

</details>

#### Bypass converts to string

1. expect AccessPolicy Bypass to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect AccessPolicy.Bypass.to_string() == "Bypass"
```

</details>

### effective_access_policy

#### Rule 2: No __init__.spl = freely accessible

#### returns Open when no __init__.spl

1. expect policy is open


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = effective_access_policy(false, false)
expect policy.is_open()
```

</details>

#### returns Open regardless of bypass flag when no __init__.spl

1. expect policy is open


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = effective_access_policy(false, true)
expect policy.is_open()
```

</details>

#### Rule 1: __init__.spl is the boundary wall

#### returns Boundary when __init__.spl exists without bypass

1. expect policy is boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = effective_access_policy(true, false)
expect policy.is_boundary()
```

</details>

#### Rule 4: #[bypass] attribute

#### returns Bypass when __init__.spl has bypass

1. expect policy is bypass


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = effective_access_policy(true, true)
expect policy.is_bypass()
```

</details>

### check_access

#### Open policy

#### allows any symbol access

1. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("test")
val sym = SymbolId.new("anything")
expect check_access(manifest, AccessPolicy.Open, sym)
```

</details>

#### Bypass policy

#### allows any symbol access (transparent)

1. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("test")
val sym = SymbolId.new("anything")
expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

#### Boundary policy

#### allows access to exported symbols

1. var manifest = DirManifest new
2. manifest add export
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("test")
val sym = SymbolId.new("PublicApi")
manifest.add_export(sym)

expect check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

#### denies access to non-exported symbols

1. expect not check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("test")
val sym = SymbolId.new("InternalHelper")

expect not check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

### Rule 1: __init__.spl boundary enforcement

#### exported symbol through boundary is accessible

1. var manifest = DirManifest new
2. manifest add child
3. manifest add export
4. var mc = ModuleContents new
5. mc add symbol
6. expect vis is public
7. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("router"))
val sym = SymbolId.new("Router")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(Symbol.pub_symbol("Router"))

# Symbol is public, module is public, and it's exported
val vis = effective_visibility(manifest, "router", mc, sym)
expect vis.is_public()

# Access through boundary is allowed
val policy = effective_access_policy(true, false)
expect check_access(manifest, policy, sym)
```

</details>

#### non-exported symbol through boundary is blocked

1. var manifest = DirManifest new
2. manifest add child
3. expect not check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("internal"))
# NOT exporting InternalHelper

val sym = SymbolId.new("InternalHelper")
val policy = effective_access_policy(true, false)
expect not check_access(manifest, policy, sym)
```

</details>

### Rule 4: bypass directory validation

#### bypass directory allows pass-through access

1. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("lib")
val sym = SymbolId.new("anything")
val policy = effective_access_policy(true, true)
expect check_access(manifest, policy, sym)
```

</details>

#### bypass directory ignores export list

1. var manifest = DirManifest new
2. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("lib")
# Even without exports, bypass allows access
val sym = SymbolId.new("SomeType")
val policy = effective_access_policy(true, true)
expect check_access(manifest, policy, sym)
```

</details>

### Rule 6: bloodline restriction (model level)

#### public symbol in public module without export is private

1. var manifest = DirManifest new
2. manifest add child
3. var mc = ModuleContents new
4. mc add symbol
5. expect vis is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("mymod"))
# NOT adding export

var mc = ModuleContents.new()
mc.add_symbol(Symbol.pub_symbol("Helper"))
val sym = SymbolId.new("Helper")

val vis = effective_visibility(manifest, "mymod", mc, sym)
expect vis.is_private()
```

</details>

#### public symbol in private module with export is private

1. var manifest = DirManifest new
2. manifest add child
3. manifest add export
4. var mc = ModuleContents new
5. mc add symbol
6. expect vis is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.priv_decl("mymod"))
val sym = SymbolId.new("Helper")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(Symbol.pub_symbol("Helper"))

val vis = effective_visibility(manifest, "mymod", mc, sym)
expect vis.is_private()
```

</details>

#### private symbol in public module with export is private

1. var manifest = DirManifest new
2. manifest add child
3. manifest add export
4. var mc = ModuleContents new
5. mc add symbol
6. expect vis is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("mymod"))
val sym = SymbolId.new("Secret")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(Symbol.priv_symbol("Secret"))

val vis = effective_visibility(manifest, "mymod", mc, sym)
expect vis.is_private()
```

</details>

#### private symbol in private module with export is private

1. var manifest = DirManifest new
2. manifest add child
3. manifest add export
4. var mc = ModuleContents new
5. mc add symbol
6. expect vis is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.priv_decl("mymod"))
val sym = SymbolId.new("Secret")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(Symbol.priv_symbol("Secret"))

val vis = effective_visibility(manifest, "mymod", mc, sym)
expect vis.is_private()
```

</details>

### Boundary with multiple exports

#### allows access to first of multiple exports

1. var manifest = DirManifest new
2. manifest add child
3. manifest add export
4. manifest add export
5. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("api")
manifest.add_child(ModDecl.pub_decl("handlers"))
val sym_a = SymbolId.new("GetHandler")
val sym_b = SymbolId.new("PostHandler")
manifest.add_export(sym_a)
manifest.add_export(sym_b)

val policy = effective_access_policy(true, false)
expect check_access(manifest, policy, sym_a)
```

</details>

#### allows access to second of multiple exports

1. var manifest = DirManifest new
2. manifest add child
3. manifest add export
4. manifest add export
5. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("api")
manifest.add_child(ModDecl.pub_decl("handlers"))
val sym_a = SymbolId.new("GetHandler")
val sym_b = SymbolId.new("PostHandler")
manifest.add_export(sym_a)
manifest.add_export(sym_b)

val policy = effective_access_policy(true, false)
expect check_access(manifest, policy, sym_b)
```

</details>

#### denies access to symbol not in multi-export list

1. var manifest = DirManifest new
2. manifest add child
3. manifest add export
4. manifest add export
5. expect not check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("api")
manifest.add_child(ModDecl.pub_decl("handlers"))
val sym_a = SymbolId.new("GetHandler")
val sym_b = SymbolId.new("PostHandler")
manifest.add_export(sym_a)
manifest.add_export(sym_b)

val sym_internal = SymbolId.new("InternalMiddleware")
val policy = effective_access_policy(true, false)
expect not check_access(manifest, policy, sym_internal)
```

</details>

### Boundary with multiple child modules

#### public symbol in first public module is visible

1. var manifest = DirManifest new
2. manifest add child
3. manifest add child
4. manifest add export
5. var mc = ModuleContents new
6. mc add symbol
7. expect vis is public


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("public_mod"))
manifest.add_child(ModDecl.priv_decl("private_mod"))
val sym = SymbolId.new("PubType")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(Symbol.pub_symbol("PubType"))

val vis = effective_visibility(manifest, "public_mod", mc, sym)
expect vis.is_public()
```

</details>

#### public symbol in private child module is hidden

1. var manifest = DirManifest new
2. manifest add child
3. manifest add child
4. manifest add export
5. var mc = ModuleContents new
6. mc add symbol
7. expect vis is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("public_mod"))
manifest.add_child(ModDecl.priv_decl("private_mod"))
val sym = SymbolId.new("PrivType")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(Symbol.pub_symbol("PrivType"))

val vis = effective_visibility(manifest, "private_mod", mc, sym)
expect vis.is_private()
```

</details>

#### symbol in non-existent module is private

1. var manifest = DirManifest new
2. manifest add child
3. manifest add export
4. var mc = ModuleContents new
5. mc add symbol
6. expect vis is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("existing"))
val sym = SymbolId.new("Ghost")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(Symbol.pub_symbol("Ghost"))

val vis = effective_visibility(manifest, "nonexistent", mc, sym)
expect vis.is_private()
```

</details>

### Open policy edge cases

#### Open allows access even with empty manifest

1. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("utils")
val sym = SymbolId.new("Helper")
expect check_access(manifest, AccessPolicy.Open, sym)
```

</details>

#### Open allows access to any symbol name

1. expect check access
2. expect check access
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("utils")
val sym1 = SymbolId.new("")
val sym2 = SymbolId.new("a")
val sym3 = SymbolId.new("very_long_symbol_name_here")
expect check_access(manifest, AccessPolicy.Open, sym1)
expect check_access(manifest, AccessPolicy.Open, sym2)
expect check_access(manifest, AccessPolicy.Open, sym3)
```

</details>

#### Open ignores export list even if populated

1. var manifest = DirManifest new
2. manifest add export
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("utils")
manifest.add_export(SymbolId.new("Exported"))

# Non-exported symbol still accessible under Open policy
val sym = SymbolId.new("NotExported")
expect check_access(manifest, AccessPolicy.Open, sym)
```

</details>

### Bypass policy edge cases

#### Bypass allows access with empty manifest

1. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("lib")
val sym = SymbolId.new("Anything")
expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

#### Bypass allows access even if exports are defined

1. var manifest = DirManifest new
2. manifest add export
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("lib")
manifest.add_export(SymbolId.new("Something"))

val sym = SymbolId.new("SomethingElse")
expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

#### Bypass allows access to exports too

1. var manifest = DirManifest new
2. manifest add export
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("lib")
val sym = SymbolId.new("ExportedToo")
manifest.add_export(sym)

expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

### Boundary policy edge cases

#### Boundary with empty exports denies all

1. expect not check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("sealed")
val sym = SymbolId.new("Anything")
expect not check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

#### Boundary with matching export name allows

1. var manifest = DirManifest new
2. manifest add export
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
val sym = SymbolId.new("Api")
manifest.add_export(sym)

expect check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

#### Boundary distinguishes different symbol names

1. var manifest = DirManifest new
2. manifest add export
3. expect check access
4. expect not check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_export(SymbolId.new("Router"))

val sym_ok = SymbolId.new("Router")
val sym_bad = SymbolId.new("router")
expect check_access(manifest, AccessPolicy.Boundary, sym_ok)
expect not check_access(manifest, AccessPolicy.Boundary, sym_bad)
```

</details>

### Nested boundary simulation

#### inner boundary blocks even if outer allows

1. var outer = DirManifest new
2. outer add export
3. var inner = DirManifest new
4. inner add child
5. expect check access
6. expect not check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Outer: boundary that exports InnerPkg
var outer = DirManifest.new("outer")
val inner_sym = SymbolId.new("InnerPkg")
outer.add_export(inner_sym)

# Inner: boundary that does NOT export DeepSecret
var inner = DirManifest.new("inner")
inner.add_child(ModDecl.pub_decl("deep"))
# NOT exporting DeepSecret

val deep_sym = SymbolId.new("DeepSecret")
val outer_policy = effective_access_policy(true, false)
val inner_policy = effective_access_policy(true, false)

# Outer allows InnerPkg
expect check_access(outer, outer_policy, inner_sym)
# Inner blocks DeepSecret
expect not check_access(inner, inner_policy, deep_sym)
```

</details>

#### inner open allows even if outer is boundary

1. var outer = DirManifest new
2. outer add export
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var outer = DirManifest.new("outer")
val utils_sym = SymbolId.new("Utils")
outer.add_export(utils_sym)

# Inner has no __init__.spl (Open policy)
val inner_policy = effective_access_policy(false, false)
val any_sym = SymbolId.new("AnyHelper")

# Inner is open, so access is allowed
expect check_access(DirManifest.new("inner"), inner_policy, any_sym)
```

</details>

#### bypass within boundary passes through

1. var outer = DirManifest new
2. outer add export
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var outer = DirManifest.new("outer")
val lib_sym = SymbolId.new("Lib")
outer.add_export(lib_sym)

# Inner has bypass
val inner_policy = effective_access_policy(true, true)
val deep_sym = SymbolId.new("DeepModule")

# Bypass is transparent
expect check_access(DirManifest.new("lib"), inner_policy, deep_sym)
```

</details>

### effective_visibility with ancestor_visibility combination

#### fully public path with all conditions met

1. var manifest = DirManifest new
2. manifest add child
3. manifest add export
4. var mc = ModuleContents new
5. mc add symbol
6. expect final vis is public


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("mymod"))
val sym = SymbolId.new("Widget")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(Symbol.pub_symbol("Widget"))

val eff_vis = effective_visibility(manifest, "mymod", mc, sym)
val ancestor_path = [Visibility.Public, Visibility.Public, eff_vis]
val final_vis = ancestor_visibility(ancestor_path)
expect final_vis.is_public()
```

</details>

#### private ancestor overrides public effective visibility

1. var manifest = DirManifest new
2. manifest add child
3. manifest add export
4. var mc = ModuleContents new
5. mc add symbol
6. expect final vis is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("mymod"))
val sym = SymbolId.new("Widget")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(Symbol.pub_symbol("Widget"))

val eff_vis = effective_visibility(manifest, "mymod", mc, sym)
# Even though effective visibility is public, a private ancestor overrides
val ancestor_path = [Visibility.Private, eff_vis]
val final_vis = ancestor_visibility(ancestor_path)
expect final_vis.is_private()
```

</details>

### AccessPolicy all input combinations

#### false, false -> Open

1. expect effective access policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect effective_access_policy(false, false).is_open()
```

</details>

#### false, true -> Open

1. expect effective access policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect effective_access_policy(false, true).is_open()
```

</details>

#### true, false -> Boundary

1. expect effective access policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect effective_access_policy(true, false).is_boundary()
```

</details>

#### true, true -> Bypass

1. expect effective access policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect effective_access_policy(true, true).is_bypass()
```

</details>

### check_access all policy-export combinations

#### Open + exported -> allowed

1. var manifest = DirManifest new
2. manifest add export
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("d")
val sym = SymbolId.new("X")
manifest.add_export(sym)
expect check_access(manifest, AccessPolicy.Open, sym)
```

</details>

#### Open + non-exported -> allowed

1. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("d")
val sym = SymbolId.new("X")
expect check_access(manifest, AccessPolicy.Open, sym)
```

</details>

#### Bypass + exported -> allowed

1. var manifest = DirManifest new
2. manifest add export
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("d")
val sym = SymbolId.new("X")
manifest.add_export(sym)
expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

#### Bypass + non-exported -> allowed

1. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("d")
val sym = SymbolId.new("X")
expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

#### Boundary + exported -> allowed

1. var manifest = DirManifest new
2. manifest add export
3. expect check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = DirManifest.new("d")
val sym = SymbolId.new("X")
manifest.add_export(sym)
expect check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

#### Boundary + non-exported -> denied

1. expect not check access


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DirManifest.new("d")
val sym = SymbolId.new("X")
expect not check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/dependency/access_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AccessPolicy
- effective_access_policy
- check_access
- Rule 1: __init__.spl boundary enforcement
- Rule 4: bypass directory validation
- Rule 6: bloodline restriction (model level)
- Boundary with multiple exports
- Boundary with multiple child modules
- Open policy edge cases
- Bypass policy edge cases
- Boundary policy edge cases
- Nested boundary simulation
- effective_visibility with ancestor_visibility combination
- AccessPolicy all input combinations
- check_access all policy-export combinations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
