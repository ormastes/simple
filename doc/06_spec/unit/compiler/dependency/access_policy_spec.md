# Access Policy Specification

> Tests covering AccessPolicy, effective_access_policy, check_access, Rule 1: __init__.spl boundary enforcement, Rule 4: bypass directory validation, Rule 6: bloodline restriction (model level), Boundary with multiple exports, Boundary with multiple child modules, Open policy edge cases, Bypass policy edge cases, Boundary policy edge cases, Nested boundary simulation, effective_visibility with ancestor_visibility combination, AccessPolicy all input combinations, check_access all policy-export combinations.

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

- Open is open


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Open is open")
val policy = AccessPolicy.Open
expect policy.is_open()
expect not policy.is_boundary()
expect not policy.is_bypass()
```

</details>

#### Boundary is boundary

- Boundary is boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Boundary is boundary")
val policy = AccessPolicy.Boundary
expect not policy.is_open()
expect policy.is_boundary()
expect not policy.is_bypass()
```

</details>

#### Bypass is bypass

- Bypass is bypass


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bypass is bypass")
val policy = AccessPolicy.Bypass
expect not policy.is_open()
expect not policy.is_boundary()
expect policy.is_bypass()
```

</details>

#### to_string

#### Open converts to string

- Open converts to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Open converts to string")
expect AccessPolicy.Open.to_string() == "Open"
```

</details>

#### Boundary converts to string

- Boundary converts to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Boundary converts to string")
expect AccessPolicy.Boundary.to_string() == "Boundary"
```

</details>

#### Bypass converts to string

- Bypass converts to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bypass converts to string")
expect AccessPolicy.Bypass.to_string() == "Bypass"
```

</details>

### effective_access_policy

#### Rule 2: No __init__.spl = freely accessible

#### returns Open when no __init__.spl

- returns Open when no __init__.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Open when no __init__.spl")
val policy = effective_access_policy(false, false)
expect policy.is_open()
```

</details>

#### returns Open regardless of bypass flag when no __init__.spl

- returns Open regardless of bypass flag when no __init__.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Open regardless of bypass flag when no __init__.spl")
val policy = effective_access_policy(false, true)
expect policy.is_open()
```

</details>

#### Rule 1: __init__.spl is the boundary wall

#### returns Boundary when __init__.spl exists without bypass

- returns Boundary when __init__.spl exists without bypass


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Boundary when __init__.spl exists without bypass")
val policy = effective_access_policy(true, false)
expect policy.is_boundary()
```

</details>

#### Rule 4: #[bypass] attribute

#### returns Bypass when __init__.spl has bypass

- returns Bypass when __init__.spl has bypass


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Bypass when __init__.spl has bypass")
val policy = effective_access_policy(true, true)
expect policy.is_bypass()
```

</details>

### check_access

#### Open policy

#### allows any symbol access

- allows any symbol access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows any symbol access")
val manifest = DirManifest.new("test")
val sym = SymbolName.new("anything")
expect check_access(manifest, AccessPolicy.Open, sym)
```

</details>

#### Bypass policy

#### allows any symbol access (transparent)

- allows any symbol access (transparent)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows any symbol access (transparent)")
val manifest = DirManifest.new("test")
val sym = SymbolName.new("anything")
expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

#### Boundary policy

#### allows access to exported symbols

- allows access to exported symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows access to exported symbols")
var manifest = DirManifest.new("test")
val sym = SymbolName.new("PublicApi")
manifest.add_export(sym)

expect check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

#### denies access to non-exported symbols

- denies access to non-exported symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies access to non-exported symbols")
val manifest = DirManifest.new("test")
val sym = SymbolName.new("InternalHelper")

expect not check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

### Rule 1: __init__.spl boundary enforcement

#### exported symbol through boundary is accessible

- exported symbol through boundary is accessible


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exported symbol through boundary is accessible")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("router"))
val sym = SymbolName.new("Router")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(DepSymbol.pub_symbol("Router"))

# Symbol is public, module is public, and it's exported
val vis = dir_effective_visibility(manifest, "router", mc, sym)
expect vis.is_public()

# Access through boundary is allowed
val policy = effective_access_policy(true, false)
expect check_access(manifest, policy, sym)
```

</details>

#### non-exported symbol through boundary is blocked

- non-exported symbol through boundary is blocked


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-exported symbol through boundary is blocked")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("internal"))
# NOT exporting InternalHelper

val sym = SymbolName.new("InternalHelper")
val policy = effective_access_policy(true, false)
expect not check_access(manifest, policy, sym)
```

</details>

### Rule 4: bypass directory validation

#### bypass directory allows pass-through access

- bypass directory allows pass-through access


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bypass directory allows pass-through access")
val manifest = DirManifest.new("lib")
val sym = SymbolName.new("anything")
val policy = effective_access_policy(true, true)
expect check_access(manifest, policy, sym)
```

</details>

#### bypass directory ignores export list

- bypass directory ignores export list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bypass directory ignores export list")
var manifest = DirManifest.new("lib")
# Even without exports, bypass allows access
val sym = SymbolName.new("SomeType")
val policy = effective_access_policy(true, true)
expect check_access(manifest, policy, sym)
```

</details>

### Rule 6: bloodline restriction (model level)

#### public symbol in public module without export is private

- public symbol in public module without export is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public symbol in public module without export is private")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("mymod"))
# NOT adding export

var mc = ModuleContents.new()
mc.add_symbol(DepSymbol.pub_symbol("Helper"))
val sym = SymbolName.new("Helper")

val vis = dir_effective_visibility(manifest, "mymod", mc, sym)
expect vis.is_private()
```

</details>

#### public symbol in private module with export is private

- public symbol in private module with export is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public symbol in private module with export is private")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.priv_decl("mymod"))
val sym = SymbolName.new("Helper")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(DepSymbol.pub_symbol("Helper"))

val vis = dir_effective_visibility(manifest, "mymod", mc, sym)
expect vis.is_private()
```

</details>

#### private symbol in public module with export is private

- private symbol in public module with export is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("private symbol in public module with export is private")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("mymod"))
val sym = SymbolName.new("Secret")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(DepSymbol.priv_symbol("Secret"))

val vis = dir_effective_visibility(manifest, "mymod", mc, sym)
expect vis.is_private()
```

</details>

#### private symbol in private module with export is private

- private symbol in private module with export is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("private symbol in private module with export is private")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.priv_decl("mymod"))
val sym = SymbolName.new("Secret")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(DepSymbol.priv_symbol("Secret"))

val vis = dir_effective_visibility(manifest, "mymod", mc, sym)
expect vis.is_private()
```

</details>

### Boundary with multiple exports

#### allows access to first of multiple exports

- allows access to first of multiple exports


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows access to first of multiple exports")
var manifest = DirManifest.new("api")
manifest.add_child(ModDecl.pub_decl("handlers"))
val sym_a = SymbolName.new("GetHandler")
val sym_b = SymbolName.new("PostHandler")
manifest.add_export(sym_a)
manifest.add_export(sym_b)

val policy = effective_access_policy(true, false)
expect check_access(manifest, policy, sym_a)
```

</details>

#### allows access to second of multiple exports

- allows access to second of multiple exports


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows access to second of multiple exports")
var manifest = DirManifest.new("api")
manifest.add_child(ModDecl.pub_decl("handlers"))
val sym_a = SymbolName.new("GetHandler")
val sym_b = SymbolName.new("PostHandler")
manifest.add_export(sym_a)
manifest.add_export(sym_b)

val policy = effective_access_policy(true, false)
expect check_access(manifest, policy, sym_b)
```

</details>

#### denies access to symbol not in multi-export list

- denies access to symbol not in multi-export list


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies access to symbol not in multi-export list")
var manifest = DirManifest.new("api")
manifest.add_child(ModDecl.pub_decl("handlers"))
val sym_a = SymbolName.new("GetHandler")
val sym_b = SymbolName.new("PostHandler")
manifest.add_export(sym_a)
manifest.add_export(sym_b)

val sym_internal = SymbolName.new("InternalMiddleware")
val policy = effective_access_policy(true, false)
expect not check_access(manifest, policy, sym_internal)
```

</details>

### Boundary with multiple child modules

#### public symbol in first public module is visible

- public symbol in first public module is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public symbol in first public module is visible")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("public_mod"))
manifest.add_child(ModDecl.priv_decl("private_mod"))
val sym = SymbolName.new("PubType")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(DepSymbol.pub_symbol("PubType"))

val vis = dir_effective_visibility(manifest, "public_mod", mc, sym)
expect vis.is_public()
```

</details>

#### public symbol in private child module is hidden

- public symbol in private child module is hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public symbol in private child module is hidden")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("public_mod"))
manifest.add_child(ModDecl.priv_decl("private_mod"))
val sym = SymbolName.new("PrivType")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(DepSymbol.pub_symbol("PrivType"))

val vis = dir_effective_visibility(manifest, "private_mod", mc, sym)
expect vis.is_private()
```

</details>

#### symbol in non-existent module is private

- symbol in non-existent module is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("symbol in non-existent module is private")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("existing"))
val sym = SymbolName.new("Ghost")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(DepSymbol.pub_symbol("Ghost"))

val vis = dir_effective_visibility(manifest, "nonexistent", mc, sym)
expect vis.is_private()
```

</details>

### Open policy edge cases

#### Open allows access even with empty manifest

- Open allows access even with empty manifest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Open allows access even with empty manifest")
val manifest = DirManifest.new("utils")
val sym = SymbolName.new("Helper")
expect check_access(manifest, AccessPolicy.Open, sym)
```

</details>

#### Open allows access to any symbol name

- Open allows access to any symbol name


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Open allows access to any symbol name")
val manifest = DirManifest.new("utils")
val sym1 = SymbolName.new("")
val sym2 = SymbolName.new("a")
val sym3 = SymbolName.new("very_long_symbol_name_here")
expect check_access(manifest, AccessPolicy.Open, sym1)
expect check_access(manifest, AccessPolicy.Open, sym2)
expect check_access(manifest, AccessPolicy.Open, sym3)
```

</details>

#### Open ignores export list even if populated

- Open ignores export list even if populated


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Open ignores export list even if populated")
var manifest = DirManifest.new("utils")
manifest.add_export(SymbolName.new("Exported"))

# Non-exported symbol still accessible under Open policy
val sym = SymbolName.new("NotExported")
expect check_access(manifest, AccessPolicy.Open, sym)
```

</details>

### Bypass policy edge cases

#### Bypass allows access with empty manifest

- Bypass allows access with empty manifest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bypass allows access with empty manifest")
val manifest = DirManifest.new("lib")
val sym = SymbolName.new("Anything")
expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

#### Bypass allows access even if exports are defined

- Bypass allows access even if exports are defined


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bypass allows access even if exports are defined")
var manifest = DirManifest.new("lib")
manifest.add_export(SymbolName.new("Something"))

val sym = SymbolName.new("SomethingElse")
expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

#### Bypass allows access to exports too

- Bypass allows access to exports too


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bypass allows access to exports too")
var manifest = DirManifest.new("lib")
val sym = SymbolName.new("ExportedToo")
manifest.add_export(sym)

expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

### Boundary policy edge cases

#### Boundary with empty exports denies all

- Boundary with empty exports denies all


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Boundary with empty exports denies all")
val manifest = DirManifest.new("sealed")
val sym = SymbolName.new("Anything")
expect not check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

#### Boundary with matching export name allows

- Boundary with matching export name allows


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Boundary with matching export name allows")
var manifest = DirManifest.new("pkg")
val sym = SymbolName.new("Api")
manifest.add_export(sym)

expect check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

#### Boundary distinguishes different symbol names

- Boundary distinguishes different symbol names


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Boundary distinguishes different symbol names")
var manifest = DirManifest.new("pkg")
manifest.add_export(SymbolName.new("Router"))

val sym_ok = SymbolName.new("Router")
val sym_bad = SymbolName.new("router")
expect check_access(manifest, AccessPolicy.Boundary, sym_ok)
expect not check_access(manifest, AccessPolicy.Boundary, sym_bad)
```

</details>

### Nested boundary simulation

#### inner boundary blocks even if outer allows

- inner boundary blocks even if outer allows


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inner boundary blocks even if outer allows")
# Outer: boundary that exports InnerPkg
var outer = DirManifest.new("outer")
val inner_sym = SymbolName.new("InnerPkg")
outer.add_export(inner_sym)

# Inner: boundary that does NOT export DeepSecret
var inner = DirManifest.new("inner")
inner.add_child(ModDecl.pub_decl("deep"))
# NOT exporting DeepSecret

val deep_sym = SymbolName.new("DeepSecret")
val outer_policy = effective_access_policy(true, false)
val inner_policy = effective_access_policy(true, false)

# Outer allows InnerPkg
expect check_access(outer, outer_policy, inner_sym)
# Inner blocks DeepSecret
expect not check_access(inner, inner_policy, deep_sym)
```

</details>

#### inner open allows even if outer is boundary

- inner open allows even if outer is boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inner open allows even if outer is boundary")
var outer = DirManifest.new("outer")
val utils_sym = SymbolName.new("Utils")
outer.add_export(utils_sym)

# Inner has no __init__.spl (Open policy)
val inner_policy = effective_access_policy(false, false)
val any_sym = SymbolName.new("AnyHelper")

# Inner is open, so access is allowed
expect check_access(DirManifest.new("inner"), inner_policy, any_sym)
```

</details>

#### bypass within boundary passes through

- bypass within boundary passes through


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bypass within boundary passes through")
var outer = DirManifest.new("outer")
val lib_sym = SymbolName.new("Lib")
outer.add_export(lib_sym)

# Inner has bypass
val inner_policy = effective_access_policy(true, true)
val deep_sym = SymbolName.new("DeepModule")

# Bypass is transparent
expect check_access(DirManifest.new("lib"), inner_policy, deep_sym)
```

</details>

### effective_visibility with ancestor_visibility combination

#### fully public path with all conditions met

- fully public path with all conditions met


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fully public path with all conditions met")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("mymod"))
val sym = SymbolName.new("Widget")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(DepSymbol.pub_symbol("Widget"))

val eff_vis = dir_effective_visibility(manifest, "mymod", mc, sym)
val ancestor_path = [Visibility.Public, Visibility.Public, eff_vis]
val final_vis = ancestor_visibility(ancestor_path)
expect final_vis.is_public()
```

</details>

#### private ancestor overrides public effective visibility

- private ancestor overrides public effective visibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("private ancestor overrides public effective visibility")
var manifest = DirManifest.new("pkg")
manifest.add_child(ModDecl.pub_decl("mymod"))
val sym = SymbolName.new("Widget")
manifest.add_export(sym)

var mc = ModuleContents.new()
mc.add_symbol(DepSymbol.pub_symbol("Widget"))

val eff_vis = dir_effective_visibility(manifest, "mymod", mc, sym)
# Even though effective visibility is public, a private ancestor overrides
val ancestor_path = [Visibility.Private, eff_vis]
val final_vis = ancestor_visibility(ancestor_path)
expect final_vis.is_private()
```

</details>

### AccessPolicy all input combinations

#### false, false -> Open

- false, false -> Open


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false, false -> Open")
expect effective_access_policy(false, false).is_open()
```

</details>

#### false, true -> Open

- false, true -> Open


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false, true -> Open")
expect effective_access_policy(false, true).is_open()
```

</details>

#### true, false -> Boundary

- true, false -> Boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("true, false -> Boundary")
expect effective_access_policy(true, false).is_boundary()
```

</details>

#### true, true -> Bypass

- true, true -> Bypass


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("true, true -> Bypass")
expect effective_access_policy(true, true).is_bypass()
```

</details>

### check_access all policy-export combinations

#### Open + exported -> allowed

- Open + exported -> allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Open + exported -> allowed")
var manifest = DirManifest.new("d")
val sym = SymbolName.new("X")
manifest.add_export(sym)
expect check_access(manifest, AccessPolicy.Open, sym)
```

</details>

#### Open + non-exported -> allowed

- Open + non-exported -> allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Open + non-exported -> allowed")
val manifest = DirManifest.new("d")
val sym = SymbolName.new("X")
expect check_access(manifest, AccessPolicy.Open, sym)
```

</details>

#### Bypass + exported -> allowed

- Bypass + exported -> allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bypass + exported -> allowed")
var manifest = DirManifest.new("d")
val sym = SymbolName.new("X")
manifest.add_export(sym)
expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

#### Bypass + non-exported -> allowed

- Bypass + non-exported -> allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bypass + non-exported -> allowed")
val manifest = DirManifest.new("d")
val sym = SymbolName.new("X")
expect check_access(manifest, AccessPolicy.Bypass, sym)
```

</details>

#### Boundary + exported -> allowed

- Boundary + exported -> allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Boundary + exported -> allowed")
var manifest = DirManifest.new("d")
val sym = SymbolName.new("X")
manifest.add_export(sym)
expect check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

#### Boundary + non-exported -> denied

- Boundary + non-exported -> denied


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Boundary + non-exported -> denied")
val manifest = DirManifest.new("d")
val sym = SymbolName.new("X")
expect not check_access(manifest, AccessPolicy.Boundary, sym)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/dependency/access_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AccessPolicy, effective_access_policy, check_access, Rule 1: __init__.spl boundary enforcement, Rule 4: bypass directory validation, Rule 6: bloodline restriction (model level), Boundary with multiple exports, Boundary with multiple child modules, Open policy edge cases, Bypass policy edge cases, Boundary policy edge cases, Nested boundary simulation, effective_visibility with ancestor_visibility combination, AccessPolicy all input combinations, check_access all policy-export combinations.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dba469e42b858df05bc54c8c6a727b2701e26ab5f5342f7ffdf9c98e75539ba8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dba469e42b858df05bc54c8c6a727b2701e26ab5f5342f7ffdf9c98e75539ba8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dba469e42b858df05bc54c8c6a727b2701e26ab5f5342f7ffdf9c98e75539ba8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/dependency/access_policy_spec.spl
mirror: doc/06_spec/unit/compiler/dependency/access_policy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/dependency/access_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/dependency/access_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/dependency/access_policy_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Open is open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/dependency/access_policy_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Boundary is boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/dependency/access_policy_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Bypass is bypass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
