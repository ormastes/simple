# Collection Opt Specification

> 1. var opt = create collection opt pass

<!-- sdn-diagram:id=collection_opt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=collection_opt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

collection_opt_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=collection_opt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Opt Specification

## Scenarios

### MIR Collection Optimization

#### treats set membership tests as pure hoistable collection queries

1. var opt = create collection opt pass
   - Expected: opt.is_pure_method("contains") is true
   - Expected: opt.is_pure_method("has") is true
   - Expected: opt.is_pure_method("size") is true
   - Expected: opt.is_pure_method("contains_key") is true
   - Expected: opt.is_pure_method("is_subset") is true
   - Expected: opt.is_pure_method("is_superset") is true
   - Expected: opt.is_pure_method("is_disjoint") is true
   - Expected: opt.is_pure_method("insert") is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "is_subset") equals `1`
   - Expected: _co_count_named_call(block, "is_disjoint") equals `1`
   - Expected: opt.pure_queries_reused equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("is_subset"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val subset2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("is_subset"), [_co_copy(1), _co_copy(2)]), span: nil)
val disjoint1 = MirInst(kind: MirInstKind.Call(_co_lid(12), _co_func("is_disjoint"), [_co_copy(1), _co_copy(4)]), span: nil)
val disjoint2 = MirInst(kind: MirInstKind.Call(_co_lid(13), _co_func("is_disjoint"), [_co_copy(1), _co_copy(4)]), span: nil)
val func = _co_function([_co_block([subset1, cmp, subset2, disjoint1, disjoint2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "is_subset")).to_equal(1)
expect(_co_count_named_call(block, "is_disjoint")).to_equal(1)
expect(opt.pure_queries_reused).to_equal(2)
```

</details>

#### reuses repeated pure has membership query results in a block

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "has") equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("has"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val has2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("has"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([has1, cmp, has2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "has")).to_equal(1)
expect(opt.pure_queries_reused).to_equal(1)
```

</details>

#### reuses repeated pure set membership query results in a block

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "contains") equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contains1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val contains2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([contains1, cmp, contains2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "contains")).to_equal(1)
expect(opt.pure_queries_reused).to_equal(1)
```

</details>

#### does not reuse pure set membership across mutating collection calls

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "contains") equals `2`
   - Expected: opt.pure_queries_reused equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contains1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val insert = MirInst(kind: MirInstKind.Call(nil, _co_func("insert"), [_co_copy(1), _co_copy(3)]), span: nil)
val contains2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([contains1, insert, contains2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "contains")).to_equal(2)
expect(opt.pure_queries_reused).to_equal(0)
```

</details>

#### reuses repeated runtime collection reads in a block

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_get") equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val get1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val get2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([get1, cmp, get2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_get")).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)
expect(opt.pure_queries_reused).to_equal(1)
```

</details>

#### keeps runtime length reads from fencing repeated runtime collection reads

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_get") equals `1`
   - Expected: _co_count_rt_array_len(block) equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val get1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val len = MirInst(kind: MirInstKind.Call(_co_lid(20), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val get2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([get1, len, get2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_get")).to_equal(1)
expect(_co_count_rt_array_len(block)).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)
expect(opt.pure_queries_reused).to_equal(1)
```

</details>

#### reuses repeated typed byte reads in a block

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_typed_bytes_u8_data_at") equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val get1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_typed_bytes_u8_data_at"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val get2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_typed_bytes_u8_data_at"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([get1, cmp, get2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_typed_bytes_u8_data_at")).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)
expect(opt.pure_queries_reused).to_equal(1)
```

</details>

#### does not reuse runtime collection reads across append calls

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_at") equals `2`
   - Expected: opt.pure_queries_reused equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val get1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_typed_words_u64_at"), [_co_copy(1), _co_copy(2)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(nil, _co_func("rt_typed_words_u64_push"), [_co_copy(1), _co_copy(3)]), span: nil)
val get2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_typed_words_u64_at"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([get1, push, get2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_typed_words_u64_at")).to_equal(2)
expect(opt.pure_queries_reused).to_equal(0)
```

</details>

#### reuses repeated runtime array data pointer reads in a block

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_data_ptr") equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_data_ptr"), [_co_copy(1)]), span: nil)
val use_ptr = MirInst(kind: MirInstKind.GetElementPtr(_co_lid(20), _co_copy(10), [_co_copy(2)]), span: nil)
val ptr2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_data_ptr"), [_co_copy(1)]), span: nil)
val func = _co_function([_co_block([ptr1, use_ptr, ptr2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_data_ptr")).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)
expect(opt.pure_queries_reused).to_equal(1)
```

</details>

#### reuses repeated runtime dict lookups in a block

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_dict_get") equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val get1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_dict_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val get2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_dict_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function([_co_block([get1, cmp, get2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_dict_get")).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)
expect(opt.pure_queries_reused).to_equal(1)
```

</details>

#### reuses repeated runtime contains queries in a block

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_contains") equals `1`
   - Expected: _co_count_named_call(block, "rt_dict_contains_key") equals `1`
   - Expected: opt.pure_queries_reused equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contains1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val contains2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_contains"), [_co_copy(1), _co_copy(2)]), span: nil)
val dict_contains1 = MirInst(kind: MirInstKind.Call(_co_lid(12), _co_func("rt_dict_contains_key"), [_co_copy(4), _co_copy(5)]), span: nil)
val dict_contains2 = MirInst(kind: MirInstKind.Call(_co_lid(13), _co_func("rt_dict_contains_key"), [_co_copy(4), _co_copy(5)]), span: nil)
val func = _co_function([_co_block([contains1, cmp, contains2, dict_contains1, dict_contains2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_contains")).to_equal(1)
expect(_co_count_named_call(block, "rt_dict_contains_key")).to_equal(1)
expect(opt.pure_queries_reused).to_equal(2)
```

</details>

#### reuses repeated runtime array first reads in a block

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_first") equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.pure_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_first"), [_co_copy(1)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Eq, _co_copy(10), _co_copy(3)), span: nil)
val first2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_first"), [_co_copy(1)]), span: nil)
val func = _co_function([_co_block([first1, cmp, first2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_first")).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)
expect(opt.pure_queries_reused).to_equal(1)
```

</details>

#### reuses repeated typed array length queries for adjacent bounds checks

1. var opt = create collection opt pass
   - Expected: _co_count_rt_array_len(block) equals `1`
   - Expected: _co_count_bounds_checks(block) equals `2`
   - Expected: opt.len_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val len1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val check1 = MirInst(kind: MirInstKind.Intrinsic(nil, "bounds_check", [_co_copy(2), _co_copy(10)]), span: nil)
val len2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val check2 = MirInst(kind: MirInstKind.Intrinsic(nil, "bounds_check", [_co_copy(3), _co_copy(11)]), span: nil)
val func = _co_function([_co_block([len1, check1, len2, check2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_rt_array_len(block)).to_equal(1)
expect(_co_count_bounds_checks(block)).to_equal(2)
expect(opt.len_queries_reused).to_equal(1)
```

</details>

#### reuses repeated typed array length queries for traversal compares

1. var opt = create collection opt pass
   - Expected: _co_count_rt_array_len(block) equals `1`
   - Expected: opt.len_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val len1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val cmp1 = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Lt, _co_copy(2), _co_copy(10)), span: nil)
val len2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val cmp2 = MirInst(kind: MirInstKind.BinOp(_co_lid(21), MirBinOp.Lt, _co_copy(3), _co_copy(11)), span: nil)
val func = _co_function([_co_block([len1, cmp1, len2, cmp2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_rt_array_len(block)).to_equal(1)
expect(opt.len_queries_reused).to_equal(1)
```

</details>

#### replaces duplicate typed array length calls even when the duplicate has multiple consumers

1. var opt = create collection opt pass
   - Expected: _co_count_rt_array_len(block) equals `1`
   - Expected: _co_count_copy_from(block, 10) equals `1`
   - Expected: opt.len_queries_reused equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val len1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val len2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val cmp = MirInst(kind: MirInstKind.BinOp(_co_lid(20), MirBinOp.Lt, _co_copy(2), _co_copy(11)), span: nil)
val check = MirInst(kind: MirInstKind.Intrinsic(nil, "bounds_check", [_co_copy(2), _co_copy(11)]), span: nil)
val func = _co_function([_co_block([len1, len2, cmp, check])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_rt_array_len(block)).to_equal(1)
expect(_co_count_copy_from(block, 10)).to_equal(1)
expect(opt.len_queries_reused).to_equal(1)
```

</details>

#### does not reuse typed array length queries across mutating collection calls

1. var opt = create collection opt pass
   - Expected: _co_count_rt_array_len(block) equals `2`
   - Expected: opt.len_queries_reused equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val len1 = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(nil, _co_func("push"), [_co_copy(1), _co_copy(2)]), span: nil)
val len2 = MirInst(kind: MirInstKind.Call(_co_lid(11), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val func = _co_function([_co_block([len1, push, len2])])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_rt_array_len(block)).to_equal(2)
expect(opt.len_queries_reused).to_equal(0)
```

</details>

<details>
<summary>Advanced: hoists invariant runtime collection metadata reads out of read-only loops</summary>

#### hoists invariant runtime collection metadata reads out of read-only loops

1. var opt = create collection opt pass
   - Expected: _co_count_rt_array_len(optimized[0]) equals `1`
   - Expected: _co_count_rt_array_len(optimized[1]) equals `0`
   - Expected: opt.calls_hoisted equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = _co_block_with(0, [], MirTerminator.Goto(BlockId(id: 1)))
val len = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val body = _co_block_with(1, [len], MirTerminator.Goto(BlockId(id: 0)))

var opt = create_collection_opt_pass()
val optimized = opt.hoist_pure_calls([header, body], _co_loop(0, [1]))

expect(_co_count_rt_array_len(optimized[0])).to_equal(1)
expect(_co_count_rt_array_len(optimized[1])).to_equal(0)
expect(opt.calls_hoisted).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: keeps runtime collection metadata reads inside mutating loops</summary>

#### keeps runtime collection metadata reads inside mutating loops

1. var opt = create collection opt pass
   - Expected: _co_count_rt_array_len(optimized[0]) equals `0`
   - Expected: _co_count_rt_array_len(optimized[1]) equals `1`
   - Expected: opt.calls_hoisted equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = _co_block_with(0, [], MirTerminator.Goto(BlockId(id: 1)))
val len = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_array_len"), [_co_copy(1)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(nil, _co_func("rt_typed_words_u64_push"), [_co_copy(1), _co_copy(2)]), span: nil)
val body = _co_block_with(1, [len, push], MirTerminator.Goto(BlockId(id: 0)))

var opt = create_collection_opt_pass()
val optimized = opt.hoist_pure_calls([header, body], _co_loop(0, [1]))

expect(_co_count_rt_array_len(optimized[0])).to_equal(0)
expect(_co_count_rt_array_len(optimized[1])).to_equal(1)
expect(opt.calls_hoisted).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: hoists invariant scalar tag operations used by collection loops</summary>

#### hoists invariant scalar tag operations used by collection loops

1. var opt = create collection opt pass
   - Expected: _co_count_binop(optimized[0], MirBinOp.Shl) equals `1`
   - Expected: _co_count_binop(optimized[0], MirBinOp.BitOr) equals `1`
   - Expected: _co_count_binop(optimized[1], MirBinOp.Shl) equals `0`
   - Expected: _co_count_binop(optimized[1], MirBinOp.BitOr) equals `0`
   - Expected: opt.scalar_ops_hoisted equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = _co_block_with(0, [], MirTerminator.Goto(BlockId(id: 1)))
val tag = MirInst(kind: MirInstKind.BinOp(_co_lid(10), MirBinOp.Shl, _co_copy(2), _co_int(3)), span: nil)
val mask = MirInst(kind: MirInstKind.BinOp(_co_lid(11), MirBinOp.BitOr, _co_copy(10), _co_int(1)), span: nil)
val body = _co_block_with(1, [tag, mask], MirTerminator.Goto(BlockId(id: 0)))

var opt = create_collection_opt_pass()
val optimized = opt.hoist_pure_calls([header, body], _co_loop(0, [1]))

expect(_co_count_binop(optimized[0], MirBinOp.Shl)).to_equal(1)
expect(_co_count_binop(optimized[0], MirBinOp.BitOr)).to_equal(1)
expect(_co_count_binop(optimized[1], MirBinOp.Shl)).to_equal(0)
expect(_co_count_binop(optimized[1], MirBinOp.BitOr)).to_equal(0)
expect(opt.scalar_ops_hoisted).to_equal(2)
```

</details>


</details>

#### hoists invariant scalar chains through bitcasts

1. var opt = create collection opt pass
   - Expected: _co_count_bitcast(optimized[0]) equals `1`
   - Expected: _co_count_binop(optimized[0], MirBinOp.BitAnd) equals `1`
   - Expected: _co_count_bitcast(optimized[1]) equals `0`
   - Expected: _co_count_binop(optimized[1], MirBinOp.BitAnd) equals `0`
   - Expected: opt.scalar_ops_hoisted equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = _co_block_with(0, [], MirTerminator.Goto(BlockId(id: 1)))
val casted = MirInst(kind: MirInstKind.Bitcast(_co_lid(10), _co_copy(2), MirType.i64()), span: nil)
val mask = MirInst(kind: MirInstKind.BinOp(_co_lid(11), MirBinOp.BitAnd, _co_copy(10), _co_int(255)), span: nil)
val body = _co_block_with(1, [casted, mask], MirTerminator.Goto(BlockId(id: 0)))

var opt = create_collection_opt_pass()
val optimized = opt.hoist_pure_calls([header, body], _co_loop(0, [1]))

expect(_co_count_bitcast(optimized[0])).to_equal(1)
expect(_co_count_binop(optimized[0], MirBinOp.BitAnd)).to_equal(1)
expect(_co_count_bitcast(optimized[1])).to_equal(0)
expect(_co_count_binop(optimized[1], MirBinOp.BitAnd)).to_equal(0)
expect(opt.scalar_ops_hoisted).to_equal(2)
```

</details>

<details>
<summary>Advanced: keeps scalar operations inside loops when they use loop-defined values</summary>

#### keeps scalar operations inside loops when they use loop-defined values

1. var opt = create collection opt pass
   - Expected: _co_count_binop(optimized[0], MirBinOp.Shl) equals `0`
   - Expected: _co_count_binop(optimized[1], MirBinOp.Shl) equals `1`
   - Expected: opt.scalar_ops_hoisted equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = _co_block_with(0, [], MirTerminator.Goto(BlockId(id: 1)))
val next_slot = MirInst(kind: MirInstKind.BinOp(_co_lid(2), MirBinOp.BitXor, _co_copy(2), _co_int(1)), span: nil)
val tag = MirInst(kind: MirInstKind.BinOp(_co_lid(10), MirBinOp.Shl, _co_copy(2), _co_int(3)), span: nil)
val body = _co_block_with(1, [next_slot, tag], MirTerminator.Goto(BlockId(id: 0)))

var opt = create_collection_opt_pass()
val optimized = opt.hoist_pure_calls([header, body], _co_loop(0, [1]))

expect(_co_count_binop(optimized[0], MirBinOp.Shl)).to_equal(0)
expect(_co_count_binop(optimized[1], MirBinOp.Shl)).to_equal(1)
expect(opt.scalar_ops_hoisted).to_equal(0)
```

</details>


</details>

#### specializes proven array index dispatch to direct array get

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_index_get") equals `0`
   - Expected: _co_count_named_call(block, "rt_array_get") equals `1`
   - Expected: opt.array_index_gets_specialized equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index_get = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_index_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals([_co_block([index_get])], [_co_local(1, array_type)])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_index_get")).to_equal(0)
expect(_co_count_named_call(block, "rt_array_get")).to_equal(1)
expect(opt.array_index_gets_specialized).to_equal(1)
```

</details>

#### keeps generic index dispatch when receiver type is not array

1. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_index_get") equals `1`
   - Expected: _co_count_named_call(block, "rt_array_get") equals `0`
   - Expected: opt.array_index_gets_specialized equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index_get = MirInst(kind: MirInstKind.Call(_co_lid(10), _co_func("rt_index_get"), [_co_copy(1), _co_copy(2)]), span: nil)
val func = _co_function_with_locals([_co_block([index_get])], [_co_local(1, MirType.i64())])

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_index_get")).to_equal(1)
expect(_co_count_named_call(block, "rt_array_get")).to_equal(0)
expect(opt.array_index_gets_specialized).to_equal(0)
```

</details>

#### elides dead append-only capacity arrays

1. [ co block

2. [ co local

3. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap") equals `0`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_push") equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alloc = MirInst(kind: MirInstKind.Call(_co_lid(1), _co_func("rt_array_new_with_cap"), [_co_copy(2)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(nil, _co_func("rt_typed_words_u64_push"), [_co_copy(1), _co_copy(3)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals(
    [_co_block([alloc, push])],
    [_co_local(1, array_type), _co_local(2, MirType(kind: MirTypeKind.U64)), _co_local(3, MirType(kind: MirTypeKind.U64))]
)

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap")).to_equal(0)
expect(_co_count_named_call(block, "rt_typed_words_u64_push")).to_equal(0)
```

</details>

#### elides dead append-only u64 capacity arrays

1. [ co block

2. [ co local

3. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap_u64") equals `0`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_push") equals `0`
   - Expected: opt.dead_append_arrays_elided equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alloc = MirInst(kind: MirInstKind.Call(_co_lid(1), _co_func("rt_array_new_with_cap_u64"), [_co_copy(2)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(nil, _co_func("rt_typed_words_u64_push"), [_co_copy(1), _co_copy(3)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals(
    [_co_block([alloc, push])],
    [_co_local(1, array_type), _co_local(2, MirType(kind: MirTypeKind.U64)), _co_local(3, MirType(kind: MirTypeKind.U64))]
)

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap_u64")).to_equal(0)
expect(_co_count_named_call(block, "rt_typed_words_u64_push")).to_equal(0)
expect(opt.dead_append_arrays_elided).to_equal(1)
```

</details>

#### keeps capacity arrays when append result is observed

1. [ co block

2. [ co local

3. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap") equals `1`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_push") equals `1`
   - Expected: opt.dead_append_arrays_elided equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alloc = MirInst(kind: MirInstKind.Call(_co_lid(1), _co_func("rt_array_new_with_cap"), [_co_copy(2)]), span: nil)
val push = MirInst(kind: MirInstKind.Call(_co_lid(4), _co_func("rt_typed_words_u64_push"), [_co_copy(1), _co_copy(3)]), span: nil)
val array_type = MirType(kind: MirTypeKind.Array(MirType(kind: MirTypeKind.U64), 0))
val func = _co_function_with_locals(
    [_co_block([alloc, push])],
    [_co_local(1, array_type), _co_local(2, MirType(kind: MirTypeKind.U64)), _co_local(3, MirType(kind: MirTypeKind.U64)), _co_local(4, MirType.bool())]
)

var opt = create_collection_opt_pass()
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap")).to_equal(1)
expect(_co_count_named_call(block, "rt_typed_words_u64_push")).to_equal(1)
expect(opt.dead_append_arrays_elided).to_equal(0)
```

</details>

#### elides dead write-only capacity arrays

1. [ co block

2.  co local

3.  co local

4.  co local

5.  co local

6. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap") equals `0`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_set") equals `0`
   - Expected: opt.dead_append_arrays_elided equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap")).to_equal(0)
expect(_co_count_named_call(block, "rt_typed_words_u64_set")).to_equal(0)
expect(opt.dead_append_arrays_elided).to_equal(1)
```

</details>

#### keeps write-only capacity arrays when write result is observed

1. [ co block

2.  co local

3.  co local

4.  co local

5.  co local

6.  co local

7. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap") equals `1`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_set") equals `1`
   - Expected: opt.dead_append_arrays_elided equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap")).to_equal(1)
expect(_co_count_named_call(block, "rt_typed_words_u64_set")).to_equal(1)
expect(opt.dead_append_arrays_elided).to_equal(0)
```

</details>

#### elides dead append-only arrays after known data pointer lowering

1. [ co block

2.  co local

3.  co local

4.  co local

5.  co local

6.  co local

7. var opt = create collection opt pass
   - Expected: _co_count_named_call(block, "rt_array_new_with_cap") equals `0`
   - Expected: _co_count_named_call(block, "rt_typed_words_u64_store_known_data_at") equals `0`
   - Expected: opt.dead_append_arrays_elided equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
val optimized = opt.optimize_function(func)
val block = optimized.blocks[0]

expect(_co_count_named_call(block, "rt_array_new_with_cap")).to_equal(0)
expect(_co_count_named_call(block, "rt_typed_words_u64_store_known_data_at")).to_equal(0)
expect(opt.dead_append_arrays_elided).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/collection_opt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MIR Collection Optimization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
