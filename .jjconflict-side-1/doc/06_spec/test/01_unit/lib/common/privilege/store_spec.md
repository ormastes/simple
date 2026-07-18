# PrivilegeStore Specification

> Covers lookup/mint/revoke round-trip, group expansion, and SDN save/load

<!-- sdn-diagram:id=store_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=store_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

store_spec -> std
store_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=store_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PrivilegeStore Specification

Covers lookup/mint/revoke round-trip, group expansion, and SDN save/load

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/common/privilege/store_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Covers lookup/mint/revoke round-trip, group expansion, and SDN save/load
round-trip via `store_fs` (see Phase 3 interfaces).

## Scenarios

### PrivilegeStore

### lookup / mint / revoke

#### AC-1: mint returns a token that lookup then finds

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = PrivilegeStore.new()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val parent = AuthorityToken.root_for(principal)
val child_path = id_path_intern("id.user.banking.view")
val minted = store.mint(parent, child_path, AuthorityLevel.Sensitive)
expect minted.ok to_equal true
val found = store.lookup(principal, child_path)
expect found.present to_equal true
```

</details>

#### AC-1: revoke removes the token from subsequent lookup

- store revoke


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = PrivilegeStore.new()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val parent = AuthorityToken.root_for(principal)
val path = id_path_intern("id.user.banking.view")
val minted = store.mint(parent, path, AuthorityLevel.Sensitive)
store.revoke(minted.value.issuer_sig)
val found = store.lookup(principal, path)
expect found.present to_equal false
```

</details>

### expand_groups

#### AC-1: id.group.dev expands to member id_paths

- store add group


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = PrivilegeStore.new()
val claude = id_path_intern("id.user.claude")
val codex = id_path_intern("id.user.codex")
val dev = id_path_intern("id.group.dev")
store.add_group(GroupDecl(id_path: dev, members: [claude, codex]))
val expanded = store.expand_groups(dev)
expect expanded to_contain claude
expect expanded to_contain codex
```

</details>

### SDN round-trip

#### AC-1: encode then decode yields equal store

- store mint
- expect decoded value tokens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = PrivilegeStore.new()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val parent = AuthorityToken.root_for(principal)
store.mint(parent, id_path_intern("id.user.banking.view"), AuthorityLevel.Sensitive)
val text = privilege_store_encode(store)
val decoded = privilege_store_decode(text)
expect decoded.ok to_equal true
expect decoded.value.tokens.len() to_equal store.tokens.len()
```

</details>

#### AC-1: store_fs.save_sdn / load_sdn round-trip via filesystem

- store mint
- expect loaded value tokens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = PrivilegeStore.new()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val parent = AuthorityToken.root_for(principal)
store.mint(parent, id_path_intern("id.user.mail.read"), AuthorityLevel.Internal)
val tmp = "/tmp/spm_winfs_privstore_spec.sdn"
val save_result = save_sdn(store, tmp)
expect save_result.ok to_equal true
val loaded = load_sdn(tmp)
expect loaded.ok to_equal true
expect loaded.value.tokens.len() to_equal 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
