# Vault Specification

> <details>

<!-- sdn-diagram:id=vault_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vault_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vault_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vault_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vault Specification

## Scenarios

### Vault — tokenized card storage

### store_token

#### stores card and returns opaque token

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vault = new_memory_vault()
val req = StoreRequest { card_number: "4111111111111111", expiry_month: 12, expiry_year: 2028, cardholder_name: "Test User" }
val result = vault_store(vault, req)
expect result.success == true
expect result.token.token_id != ""
expect result.token.card_last4 == "1111"
expect result.token.card_brand == "Visa"
```

</details>

#### never exposes raw PAN in stored token

1. expect result token token id contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vault = new_memory_vault()
val req = StoreRequest { card_number: "5500000000000004", expiry_month: 6, expiry_year: 2027, cardholder_name: "MC User" }
val result = vault_store(vault, req)
expect result.success == true
expect result.token.token_id.contains("5500000000000004") == false
```

</details>

#### rejects invalid card number

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vault = new_memory_vault()
val req = StoreRequest { card_number: "0000000000000000", expiry_month: 12, expiry_year: 2028, cardholder_name: "Bad Card" }
val result = vault_store(vault, req)
expect result.success == false
```

</details>

### retrieve

#### retrieves stored token metadata by ID

1. var vault = new memory vault


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vault = new_memory_vault()
val req = StoreRequest { card_number: "4111111111111111", expiry_month: 3, expiry_year: 2029, cardholder_name: "Retrieve Test" }
val stored = vault_store(vault, req)
vault = MemoryVault { tokens: [stored.token], next_id: 2 }
val retrieved = vault_retrieve(vault, stored.token.token_id)
expect retrieved.success == true
expect retrieved.token.card_last4 == "1111"
```

</details>

#### returns failure for unknown token ID

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vault = new_memory_vault()
val result = vault_retrieve(vault, "tok_nonexistent")
expect result.success == false
```

</details>

### delete

#### deletes a stored token

1. var vault = new memory vault


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = StoreRequest { card_number: "4111111111111111", expiry_month: 12, expiry_year: 2028, cardholder_name: "Delete Test" }
var vault = new_memory_vault()
val stored = vault_store(vault, req)
vault = MemoryVault { tokens: [stored.token], next_id: 2 }
val del = vault_delete(vault, stored.token.token_id)
expect del.success == true
```

</details>

#### returns failure when deleting unknown token

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vault = new_memory_vault()
val result = vault_delete(vault, "tok_nonexistent")
expect result.success == false
```

</details>

### list_tokens

#### lists all stored tokens

1. var vault = new memory vault

2. expect tokens length


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req1 = StoreRequest { card_number: "4111111111111111", expiry_month: 12, expiry_year: 2028, cardholder_name: "User A" }
val req2 = StoreRequest { card_number: "5500000000000004", expiry_month: 6, expiry_year: 2027, cardholder_name: "User B" }
var vault = new_memory_vault()
val s1 = vault_store(vault, req1)
val s2 = vault_store(vault, req2)
vault = MemoryVault { tokens: [s1.token, s2.token], next_id: 3 }
val tokens = vault.tokens
expect tokens.length() == 2
```

</details>

#### returns empty list when no tokens stored

1. expect vault tokens length


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vault = new_memory_vault()
expect vault.tokens.length() == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `/tmp/simple-payment/test/vault_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vault — tokenized card storage
- store_token
- retrieve
- delete
- list_tokens

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
