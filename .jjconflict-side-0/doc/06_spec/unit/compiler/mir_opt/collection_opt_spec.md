# collection_opt_spec

> Purpose: Prove that MIR Collection Optimization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# collection_opt_spec

Purpose: Prove that MIR Collection Optimization.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/mir_opt/collection_opt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that MIR Collection Optimization.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### MIR Collection Optimization

#### treats set membership tests as pure hoistable collection queries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- treats set membership tests as pure hoistable collection queries
- Verify: treats set membership tests as pure hoistable collection queries
   - Expected: opt.is_pure_method("contains") is true
   - Expected: opt.is_pure_method("has") is true
   - Expected: opt.is_pure_method("size") is true
   - Expected: opt.is_pure_method("contains_key") is true
   - Expected: opt.is_pure_method("is_subset") is true
   - Expected: opt.is_pure_method("is_superset") is true
   - Expected: opt.is_pure_method("is_disjoint") is true
   - Expected: opt.is_pure_method("insert") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats set membership tests as pure hoistable collection queries")
step("Verify: treats set membership tests as pure hoistable collection queries")
# @req: REQ-COMPILER-MIR-OPT-001
var opt = create_collection_opt_pass()

expect(opt.is_pure_method("contains")).to_equal(true)
expect(opt.is_pure_method("has")).to_equal(true)
expect(opt.is_pure_method("size")).to_equal(true)
expect(opt.is_pure_method("contains_key")).to_equal(true)
expect(opt.is_pure_method("is_subset")).to_equal(true)
expect(opt.is_pure_method("is_superset")).to_equal(true)
expect(opt.is_pure_method("is_disjoint")).to_equal(true)
expect(opt.is_pure_method("insert")).to_equal(false)
```

</details>

#### reuses repeated pure set relationship query results in a block

- reuses repeated pure set relationship query results in a block
- Verify: reuses repeated pure set relationship query results in a block
   - Expected: _co_count_named_call(block, "is_subset") equals `1`
   - Expected: _co_count_named_call(block, "is_disjoint") equals `1`
   - Expected: opt.pure_queries_reused equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated pure set relationship query results in a block")
step("Verify: reuses repeated pure set relationship query results in a block")
val subset1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("is_subset"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val subset2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("is_subset"), [_co_copy(1), _co_copy(2)]), span: nil)
val disjoint1 = MirInst(kind: MirInstKind.Call(_co_lid(12), _co_func("is_disjoint"), [_co_copy(1), _co_copy(4)]), span: nil)
val disjoint2 = MirInst(kind: MirInstKind.Call(_co_lid(13), _co_func("is_disjoint"), [_co_copy(1), _co_copy(4)]), span: nil)
val func = _co_function([_co_block([subset1, cmp, subset2, disjoint1, disjoint2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "is_subset")).to_equal(1)
expect(_co_count_named_call(block, "is_disjoint")).to_equal(1)
expect(opt.pure_queries_reused).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### reuses repeated pure has membership query results in a block

- reuses repeated pure has membership query results in a block
- Verify: reuses repeated pure has membership query results in a block
   - Expected: _co_count_named_call(block, "has") equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated pure has membership query results in a block")
step("Verify: reuses repeated pure has membership query results in a block")
val has1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("has"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val has2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("has"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([has1, cmp, has2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "has")).to_equal(1)
expect(opt.pure_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reuses repeated pure set membership query results in a block

- reuses repeated pure set membership query results in a block
- Verify: reuses repeated pure set membership query results in a block
   - Expected: _co_count_named_call(block, "contains") equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated pure set membership query results in a block")
step("Verify: reuses repeated pure set membership query results in a block")
val contains1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val contains2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([contains1, cmp, contains2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "contains")).to_equal(1)
expect(opt.pure_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### does not reuse pure set membership across mutating collection calls

- does not reuse pure set membership across mutating collection calls
- Verify: does not reuse pure set membership across mutating collection calls
   - Expected: _co_count_named_call(block, "contains") equals `2`
   - Expected: opt.pure_queries_reused equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not reuse pure set membership across mutating collection calls")
step("Verify: does not reuse pure set membership across mutating collection calls")
val contains1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val insert = MirInst(kind: MirInstKind.Call(nil, _co_func("insert"), [_co_copy(1), _co_copy(3)]), span: nil)
val contains2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([contains1, insert, contains2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "contains")).to_equal(2)
expect(opt.pure_queries_reused).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### reuses repeated runtime collection reads in a block

- reuses repeated runtime collection reads in a block
- Verify: reuses repeated runtime collection reads in a block
   - Expected: _co_count_named_call(block, "rt_array_get") equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated runtime collection reads in a block")
step("Verify: reuses repeated runtime collection reads in a block")
val get1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val get2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([get1, cmp, get2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_get")).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(opt.pure_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### keeps runtime length reads from fencing repeated runtime collection reads

- keeps runtime length reads from fencing repeated runtime collection reads
- Verify: keeps runtime length reads from fencing repeated runtime collection reads
   - Expected: _co_count_named_call(block, "rt_array_get") equals `1`
   - Expected: _co_count_rt_array_len(block) equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps runtime length reads from fencing repeated runtime collection reads")
step("Verify: keeps runtime length reads from fencing repeated runtime collection reads")
val get1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val len = MirInst(kind: MirInstKind.Call(_co_lid(20), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val get2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([get1, len, get2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_get")).to_equal(1)
expect(_co_count_rt_array_len(block)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(_co_count_copy_from(block, 10)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(opt.pure_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reuses repeated typed byte reads in a block

- reuses repeated typed byte reads in a block
- Verify: reuses repeated typed byte reads in a block
   - Expected: _co_count_named_call(block, "rt_typed_bytes_u8_data_at") equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated typed byte reads in a block")
step("Verify: reuses repeated typed byte reads in a block")
val get1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_typed_bytes_u8_data_at"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val get2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_typed_bytes_u8_data_at"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([get1, cmp, get2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_typed_bytes_u8_data_at")).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(opt.pure_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### does not reuse runtime collection reads across append calls

- does not reuse runtime collection reads across append calls
- Verify: does not reuse runtime collection reads across append calls
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_at") equals `2`
   - Expected: opt.pure_queries_reused equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not reuse runtime collection reads across append calls")
step("Verify: does not reuse runtime collection reads across append calls")
val get1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_typed_words_u64_at"), [_co_copy(1), _co_copy(2)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(nil, _co_func("rt_typed_words_u64_push"), [_co_copy(1), _co_copy(3)]), span: nil)
val get2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_typed_words_u64_at"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([get1, push, get2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_typed_words_u64_at")).to_equal(2)
expect(opt.pure_queries_reused).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### reuses repeated runtime array data pointer reads in a block

- reuses repeated runtime array data pointer reads in a block
- Verify: reuses repeated runtime array data pointer reads in a block
   - Expected: _co_count_named_call(block, "rt_array_data_ptr") equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated runtime array data pointer reads in a block")
step("Verify: reuses repeated runtime array data pointer reads in a block")
val ptr1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_data_ptr"), [_co_copy(1)]), span: nil)
val use_ptr = MirInst(kind: MirInstKind.GetElementPtr(_co_lid(20), _co_copy(10), [_co_copy(2)]), span: nil)
val ptr2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_data_ptr"), [_co_copy(1)]), span: nil)
val func = _co_function([_co_block([ptr1, use_ptr, ptr2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_data_ptr")).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(opt.pure_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reuses repeated runtime dict lookups in a block

- reuses repeated runtime dict lookups in a block
- Verify: reuses repeated runtime dict lookups in a block
   - Expected: _co_count_named_call(block, "rt_dict_get") equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated runtime dict lookups in a block")
step("Verify: reuses repeated runtime dict lookups in a block")
val get1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_dict_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val get2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_dict_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([get1, cmp, get2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_dict_get")).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(opt.pure_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reuses repeated runtime contains queries in a block

- reuses repeated runtime contains queries in a block
- Verify: reuses repeated runtime contains queries in a block
   - Expected: _co_count_named_call(block, "rt_array_contains") equals `1`
   - Expected: _co_count_named_call(block, "rt_dict_contains_key") equals `1`
   - Expected: opt.pure_queries_reused equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated runtime contains queries in a block")
step("Verify: reuses repeated runtime contains queries in a block")
val contains1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val contains2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val dict_contains1 = MirInst(kind: MirInstKind.Call(_co_lid(12), _co_func("rt_dict_contains_key"), [_co_copy(4), _co_copy(5)]), span: nil)
val dict_contains2 = MirInst(kind: MirInstKind.Call(_co_lid(13), _co_func("rt_dict_contains_key"), [_co_copy(4), _co_copy(5)]), span: nil)
val func = _co_function([_co_block([contains1, cmp, contains2, dict_contains1, dict_contains2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_contains")).to_equal(1)
expect(_co_count_named_call(block, "rt_dict_contains_key")).to_equal(1)
expect(opt.pure_queries_reused).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### reuses repeated runtime array first reads in a block

- reuses repeated runtime array first reads in a block
- Verify: reuses repeated runtime array first reads in a block
   - Expected: _co_count_named_call(block, "rt_array_first") equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated runtime array first reads in a block")
step("Verify: reuses repeated runtime array first reads in a block")
val first1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_first"), [_co_copy(1)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val first2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_first"), [_co_copy(1)]), span: nil)
val func = _co_function([_co_block([first1, cmp, first2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_first")).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(opt.pure_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reuses repeated typed array length queries for adjacent bounds checks

- reuses repeated typed array length queries for adjacent bounds checks
- Verify: reuses repeated typed array length queries for adjacent bounds checks
   - Expected: _co_count_rt_array_len(block) equals `1`
   - Expected: _co_count_bounds_checks(block) equals `2`
   - Expected: opt.len_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated typed array length queries for adjacent bounds checks")
step("Verify: reuses repeated typed array length queries for adjacent bounds checks")
val len1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val check1 = MirInst(kind: MirInstKind.Intrinsic(nil, "bounds_check", [_co_copy(2), _co_copy(10)]), span: nil)
val len2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val check2 = MirInst(kind: MirInstKind.Intrinsic(nil, "bounds_check", [_co_copy(3), _co_copy(11)]), span: nil)
val func = _co_function([_co_block([len1, check1, len2, check2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_rt_array_len(block)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(_co_count_bounds_checks(block)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(opt.len_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reuses repeated typed array length queries for traversal compares

- reuses repeated typed array length queries for traversal compares
- Verify: reuses repeated typed array length queries for traversal compares
   - Expected: _co_count_rt_array_len(block) equals `1`
   - Expected: opt.len_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses repeated typed array length queries for traversal compares")
step("Verify: reuses repeated typed array length queries for traversal compares")
val len1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val cmp1 = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Lt, _co_copy(2), _co_copy(10)), span: nil)
val len2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val cmp2 = MirInst(kind: MirInstKind.BinOp(_co_lid(21), MirBinOp.Lt, _co_copy(3), _co_copy(11)), span: nil)
val func = _co_function([_co_block([len1, cmp1, len2, cmp2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_rt_array_len(block)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(opt.len_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### replaces duplicate typed array length calls even when the duplicate has multiple consumers

- replaces duplicate typed array length calls even when the duplicate has multiple consumers
- Verify: replaces duplicate typed array length calls even when the duplicate has multiple consumers
   - Expected: _co_count_rt_array_len(block) equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.len_queries_reused equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces duplicate typed array length calls even when the duplicate has multiple consumers")
step("Verify: replaces duplicate typed array length calls even when the duplicate has multiple consumers")
val len1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val len2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Lt, _co_copy(2), _co_copy(11)), span: nil)
val check = MirInst(kind: MirInstKind.Intrinsic(nil, "bounds_check", [_co_copy(2), _co_copy(11)]), span: nil)
val func = _co_function([_co_block([len1, len2, cmp, check])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_rt_array_len(block)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(_co_count_copy_from(block, 10)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(opt.len_queries_reused).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### does not reuse typed array length queries across mutating collection calls

- does not reuse typed array length queries across mutating collection calls
- Verify: does not reuse typed array length queries across mutating collection calls
   - Expected: _co_count_rt_array_len(block) equals `2`
   - Expected: opt.len_queries_reused equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not reuse typed array length queries across mutating collection calls")
step("Verify: does not reuse typed array length queries across mutating collection calls")
val len1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(nil, _co_func("push"), [_co_copy(1), _co_copy(2)]), span: nil)
val len2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val func = _co_function([_co_block([len1, push, len2])])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_rt_array_len(block)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(opt.len_queries_reused).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

<details>
<summary>Advanced: hoists invariant runtime collection metadata reads out of read-only loops</summary>

#### hoists invariant runtime collection metadata reads out of read-only loops

- hoists invariant runtime collection metadata reads out of read-only loops
- Verify: hoists invariant runtime collection metadata reads out of read-only loops
   - Expected: _co_count_rt_array_len(optimized[0]) equals `1`
   - Expected: _co_count_rt_array_len(optimized[1]) equals `0`
   - Expected: opt.calls_hoisted equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hoists invariant runtime collection metadata reads out of read-only loops")
step("Verify: hoists invariant runtime collection metadata reads out of read-only loops")
val header = _co_block_with(0, [], MirTerminator.Goto(BlockId(id: 1)))
val len = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val body = _co_block_with(1, [len], MirTerminator.Goto(BlockId(id: 0)))

var opt = create_collection_opt_pass()
val optimized = colopt_hoist_pure_calls(opt, [header, body], _co_loop(0, [1]))

expect(_co_count_rt_array_len(optimized[0])).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(_co_count_rt_array_len(optimized[1])).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(opt.calls_hoisted).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: keeps runtime collection metadata reads inside mutating loops</summary>

#### keeps runtime collection metadata reads inside mutating loops

- keeps runtime collection metadata reads inside mutating loops
- Verify: keeps runtime collection metadata reads inside mutating loops
   - Expected: _co_count_rt_array_len(optimized[0]) equals `0`
   - Expected: _co_count_rt_array_len(optimized[1]) equals `1`
   - Expected: opt.calls_hoisted equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps runtime collection metadata reads inside mutating loops")
step("Verify: keeps runtime collection metadata reads inside mutating loops")
val header = _co_block_with(0, [], MirTerminator.Goto(BlockId(id: 1)))
val len = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(nil, _co_func("rt_typed_words_u64_push"), [_co_copy(1), _co_copy(2)]), span: nil)
val body = _co_block_with(1, [len, push], MirTerminator.Goto(BlockId(id: 0)))

var opt = create_collection_opt_pass()
val optimized = colopt_hoist_pure_calls(opt, [header, body], _co_loop(0, [1]))

expect(_co_count_rt_array_len(optimized[0])).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(_co_count_rt_array_len(optimized[1])).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(opt.calls_hoisted).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: hoists invariant scalar tag operations used by collection loops</summary>

#### hoists invariant scalar tag operations used by collection loops

- hoists invariant scalar tag operations used by collection loops
- Verify: hoists invariant scalar tag operations used by collection loops
   - Expected: _co_count_binop(optimized[0], MirBinOp.Shl) equals `1`
   - Expected: _co_count_binop(optimized[0], MirBinOp.BitOr) equals `1`
   - Expected: _co_count_binop(optimized[1], MirBinOp.Shl) equals `0`
   - Expected: _co_count_binop(optimized[1], MirBinOp.BitOr) equals `0`
   - Expected: opt.scalar_ops_hoisted equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hoists invariant scalar tag operations used by collection loops")
step("Verify: hoists invariant scalar tag operations used by collection loops")
val header = _co_block_with(0, [], MirTerminator.Goto(BlockId(id: 1)))
val tag = MirInst(kind: MirInstKind.BinOp(_co_lid(10), MirBinOp.Shl, _co_copy(2), _co_int(3)), span: nil)
val mask = MirInst(kind: MirInstKind.BinOp(_co_lid(11), MirBinOp.BitOr, _co_copy(10), _co_int(1)), span: nil)
val body = _co_block_with(1, [tag, mask], MirTerminator.Goto(BlockId(id: 0)))

var opt = create_collection_opt_pass()
val optimized = colopt_hoist_pure_calls(opt, [header, body], _co_loop(0, [1]))

expect(_co_count_binop(optimized[0], MirBinOp.Shl)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(_co_count_binop(optimized[0], MirBinOp.BitOr)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(_co_count_binop(optimized[1], MirBinOp.Shl)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(_co_count_binop(optimized[1], MirBinOp.BitOr)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(opt.scalar_ops_hoisted).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>


</details>

#### hoists invariant scalar chains through bitcasts

- hoists invariant scalar chains through bitcasts
- Verify: hoists invariant scalar chains through bitcasts
   - Expected: _co_count_bitcast(optimized[0]) equals `1`
   - Expected: _co_count_binop(optimized[0], MirBinOp.BitAnd) equals `1`
   - Expected: _co_count_bitcast(optimized[1]) equals `0`
   - Expected: _co_count_binop(optimized[1], MirBinOp.BitAnd) equals `0`
   - Expected: opt.scalar_ops_hoisted equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hoists invariant scalar chains through bitcasts")
step("Verify: hoists invariant scalar chains through bitcasts")
val header = _co_block_with(0, [], MirTerminator.Goto(BlockId(id: 1)))
val casted = MirInst(kind: MirInstKind.Bitcast(_co_lid(10), _co_copy(2), MirType.i64()), span: nil)
val mask = MirInst(kind: MirInstKind.BinOp(_co_lid(11), MirBinOp.BitAnd, _co_copy(10), _co_int(255)), span: nil)
val body = _co_block_with(1, [casted, mask], MirTerminator.Goto(BlockId(id: 0)))

var opt = create_collection_opt_pass()
val optimized = colopt_hoist_pure_calls(opt, [header, body], _co_loop(0, [1]))

expect(_co_count_bitcast(optimized[0])).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(_co_count_binop(optimized[0], MirBinOp.BitAnd)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(_co_count_bitcast(optimized[1])).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(_co_count_binop(optimized[1], MirBinOp.BitAnd)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(opt.scalar_ops_hoisted).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

<details>
<summary>Advanced: keeps scalar operations inside loops when they use loop-defined values</summary>

#### keeps scalar operations inside loops when they use loop-defined values

- keeps scalar operations inside loops when they use loop-defined values
- Verify: keeps scalar operations inside loops when they use loop-defined values
   - Expected: _co_count_binop(optimized[0], MirBinOp.Shl) equals `0`
   - Expected: _co_count_binop(optimized[1], MirBinOp.Shl) equals `1`
   - Expected: opt.scalar_ops_hoisted equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps scalar operations inside loops when they use loop-defined values")
step("Verify: keeps scalar operations inside loops when they use loop-defined values")
val header = _co_block_with(0, [], MirTerminator.Goto(BlockId(id: 1)))
val next_slot = MirInst(kind: MirInstKind.BinOp(_co_lid(2), MirBinOp.BitXor, _co_copy(2), _co_int(1)), span: nil)
val tag = MirInst(kind: MirInstKind.BinOp(_co_lid(10), MirBinOp.Shl, _co_copy(2), _co_int(3)), span: nil)
val body = _co_block_with(1, [next_slot, tag], MirTerminator.Goto(BlockId(id: 0)))

var opt = create_collection_opt_pass()
val optimized = colopt_hoist_pure_calls(opt, [header, body], _co_loop(0, [1]))

expect(_co_count_binop(optimized[0], MirBinOp.Shl)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(_co_count_binop(optimized[1], MirBinOp.Shl)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(opt.scalar_ops_hoisted).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>


</details>

#### specializes proven array index dispatch to direct array get

- specializes proven array index dispatch to direct array get
- Verify: specializes proven array index dispatch to direct array get
   - Expected: _co_count_named_call(block, "rt_index_get") equals `0`
   - Expected: _co_count_named_call(block, "rt_array_get") equals `1`
   - Expected: opt.array_index_gets_specialized equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("specializes proven array index dispatch to direct array get")
step("Verify: specializes proven array index dispatch to direct array get")
val index_get = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_index_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals([_co_block([index_get])], [_co_local(1, array_type)])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_index_get")).to_equal(0)
expect(_co_count_named_call(block, "rt_array_get")).to_equal(1)
expect(opt.array_index_gets_specialized).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### keeps generic index dispatch when receiver type is not array

- keeps generic index dispatch when receiver type is not array
- Verify: keeps generic index dispatch when receiver type is not array
   - Expected: _co_count_named_call(block, "rt_index_get") equals `1`
   - Expected: _co_count_named_call(block, "rt_array_get") equals `0`
   - Expected: opt.array_index_gets_specialized equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps generic index dispatch when receiver type is not array")
step("Verify: keeps generic index dispatch when receiver type is not array")
val index_get = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_index_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function_with_locals([_co_block([index_get])], [_co_local(1, MirType.i64())])

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_index_get")).to_equal(1)
expect(_co_count_named_call(block, "rt_array_get")).to_equal(0)
expect(opt.array_index_gets_specialized).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### elides dead append-only capacity arrays

- elides dead append-only capacity arrays
- Verify: elides dead append-only capacity arrays
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap") equals `0`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_push") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("elides dead append-only capacity arrays")
step("Verify: elides dead append-only capacity arrays")
val alloc = MirInst(kind: MirInstKind.Call(_co_lid(1), _co_func("rt_array_new_with_cap"), [_co_copy(2)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(nil, _co_func("rt_typed_words_u64_push"), [_co_copy(1), _co_copy(3)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals(
    [_co_block([alloc, push])],
    [_co_local(1, array_type), _co_local(2, MirType(kind: MirTypeKind.U64)), _co_local(3, MirType(kind: MirTypeKind.U64))]
)

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap")).to_equal(0)
expect(_co_count_named_call(block, "rt_typed_words_u64_push")).to_equal(0)
```

</details>

#### elides dead append-only u64 capacity arrays

- elides dead append-only u64 capacity arrays
- Verify: elides dead append-only u64 capacity arrays
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap_u64") equals `0`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_push") equals `0`
   - Expected: opt.dead_append_arrays_elided equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("elides dead append-only u64 capacity arrays")
step("Verify: elides dead append-only u64 capacity arrays")
val alloc = MirInst(kind: MirInstKind.Call(_co_lid(1), _co_func("rt_array_new_with_cap_u64"), [_co_copy(2)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(nil, _co_func("rt_typed_words_u64_push"), [_co_copy(1), _co_copy(3)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals(
    [_co_block([alloc, push])],
    [_co_local(1, array_type), _co_local(2, MirType(kind: MirTypeKind.U64)), _co_local(3, MirType(kind: MirTypeKind.U64))]
)

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap_u64")).to_equal(0)
expect(_co_count_named_call(block, "rt_typed_words_u64_push")).to_equal(0)
expect(opt.dead_append_arrays_elided).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### keeps capacity arrays when append result is observed

- keeps capacity arrays when append result is observed
- Verify: keeps capacity arrays when append result is observed
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap") equals `1`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_push") equals `1`
   - Expected: opt.dead_append_arrays_elided equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps capacity arrays when append result is observed")
step("Verify: keeps capacity arrays when append result is observed")
val alloc = MirInst(kind: MirInstKind.Call(_co_lid(1), _co_func("rt_array_new_with_cap"), [_co_copy(2)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(_co_lid(4), _co_func("rt_typed_words_u64_push"), [_co_copy(1), _co_copy(3)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals(
    [_co_block([alloc, push])],
    [_co_local(1, array_type), _co_local(2, MirType(kind: MirTypeKind.U64)), _co_local(3, MirType(kind: MirTypeKind.U64)), _co_local(4, MirType.bool())]
)

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap")).to_equal(1)
expect(_co_count_named_call(block, "rt_typed_words_u64_push")).to_equal(1)
expect(opt.dead_append_arrays_elided).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### elides dead write-only capacity arrays

- elides dead write-only capacity arrays
- Verify: elides dead write-only capacity arrays
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap") equals `0`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_set") equals `0`
   - Expected: opt.dead_append_arrays_elided equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("elides dead write-only capacity arrays")
step("Verify: elides dead write-only capacity arrays")
val alloc = MirInst(kind: MirInstKind.Call(_co_lid(1), _co_func("rt_array_new_with_cap"), [_co_copy(2)]), span: nil)
val set = MirInst(kind: MirInstKind.Call(nil, _co_func("rt_typed_words_u64_set"), [_co_copy(1), _co_copy(4), _co_copy(3)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals(
    [_co_block([alloc, set])],
    [
        _co_local(1, array_type),
        _co_local(2, MirType(kind: MirTypeKind.U64)),
        _co_local(3, MirType(kind: MirTypeKind.U64)),
        _co_local(4, MirType(kind: MirTypeKind.U64))
    ]
)

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap")).to_equal(0)
expect(_co_count_named_call(block, "rt_typed_words_u64_set")).to_equal(0)
expect(opt.dead_append_arrays_elided).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### keeps write-only capacity arrays when write result is observed

- keeps write-only capacity arrays when write result is observed
- Verify: keeps write-only capacity arrays when write result is observed
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap") equals `1`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_set") equals `1`
   - Expected: opt.dead_append_arrays_elided equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps write-only capacity arrays when write result is observed")
step("Verify: keeps write-only capacity arrays when write result is observed")
val alloc = MirInst(kind: MirInstKind.Call(_co_lid(1), _co_func("rt_array_new_with_cap"), [_co_copy(2)]), span: nil)
val set = MirInst(kind: MirInstKind.Call(_co_lid(5), _co_func("rt_typed_words_u64_set"), [_co_copy(1), _co_copy(4), _co_copy(3)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals(
    [_co_block([alloc, set])],
    [
        _co_local(1, array_type),
        _co_local(2, MirType(kind: MirTypeKind.U64)),
        _co_local(3, MirType(kind: MirTypeKind.U64)),
        _co_local(4, MirType(kind: MirTypeKind.U64)),
        _co_local(5, MirType.bool())
    ]
)

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap")).to_equal(1)
expect(_co_count_named_call(block, "rt_typed_words_u64_set")).to_equal(1)
expect(opt.dead_append_arrays_elided).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### elides dead append-only arrays after known data pointer lowering

- elides dead append-only arrays after known data pointer lowering
- Verify: elides dead append-only arrays after known data pointer lowering
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap") equals `0`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_store_known_data_at") equals `0`
   - Expected: opt.dead_append_arrays_elided equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("elides dead append-only arrays after known data pointer lowering")
step("Verify: elides dead append-only arrays after known data pointer lowering")
val alloc = MirInst(kind: MirInstKind.Call(_co_lid(1), _co_func("rt_array_new_with_cap"), [_co_copy(2)]), span: nil)
val data_ptr_store = MirInst(kind: MirInstKind.Call(nil, _co_func("rt_typed_words_u64_store_known_data_at"), [_co_copy(1), _co_copy(5), _co_copy(6), _co_copy(3)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals(
    [_co_block([alloc, data_ptr_store])],
    [
        _co_local(1, array_type),
        _co_local(2, MirType(kind: MirTypeKind.U64)),
        _co_local(3, MirType(kind: MirTypeKind.U64)),
        _co_local(5, MirType.i64()),
        _co_local(6, MirType(kind: MirTypeKind.U64))
    ]
)

var opt = create_collection_opt_pass()
val optimized = collection_opt_optimize_function(opt, func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap")).to_equal(0)
expect(_co_count_named_call(block, "rt_typed_words_u64_store_known_data_at")).to_equal(0)
expect(opt.dead_append_arrays_elided).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-MIR-OPT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `507c8d3a5b68d21d19269f56f7b5c6b4f19acaa3d8d25ec6291695e54da525d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `507c8d3a5b68d21d19269f56f7b5c6b4f19acaa3d8d25ec6291695e54da525d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `507c8d3a5b68d21d19269f56f7b5c6b4f19acaa3d8d25ec6291695e54da525d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/mir_opt/collection_opt_spec.spl
mirror: doc/06_spec/unit/compiler/mir_opt/collection_opt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mir_opt/collection_opt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mir_opt/collection_opt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mir_opt/collection_opt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 30 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/mir_opt/collection_opt_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats set membership tests as pure hoistable collection queries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/collection_opt_spec.spl:181:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses repeated pure set relationship query results in a block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/collection_opt_spec.spl:200:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses repeated pure has membership query results in a block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
