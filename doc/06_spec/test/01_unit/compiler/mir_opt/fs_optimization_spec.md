# fs_optimization_spec

> FS Optimization Pass Specification

<!-- sdn-diagram:id=fs_optimization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fs_optimization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fs_optimization_spec -> std
fs_optimization_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fs_optimization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fs_optimization_spec

FS Optimization Pass Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/fs_optimization_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

FS Optimization Pass Specification

Validates the 3 new MIR optimization passes for FS-aware transforms:
  - io_write_coalesce: merges adjacent writes
  - io_readahead_hoist: lifts reads before loops
  - io_batch_open_close: batches syscalls
  - PassScope.FsDriver recognized in manifest (D-5)

## Scenarios

### MIR FS Passes — write coalesce

#### AC-4: run_named_pass accepts write_coalesce pass name

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = OptimizationStats.create()
val func = MirFunction(name: "wc_fn", blocks: [], locals: [])
val result = optimize_write_coalesce(func, stats)
val n = result.name
expect(n).to_equal("wc_fn")
```

</details>

#### AC-4: write coalesce stat counter exists after pass

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = OptimizationStats.create()
val func = MirFunction(name: "wc_fn2", blocks: [], locals: [])
val result = optimize_write_coalesce(func, stats)
val count = stats.write_coalesce_count
expect(count).to_be_greater_than(-1)
```

</details>

### MIR FS Passes — syscall batch

#### AC-4: optimize_syscall_batch accepts MirFunction

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = OptimizationStats.create()
val func = MirFunction(name: "sb_fn", blocks: [], locals: [])
val result = optimize_syscall_batch(func, stats)
val n = result.name
expect(n).to_equal("sb_fn")
```

</details>

#### AC-4: syscall batch stat counter exists after pass

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = OptimizationStats.create()
val func = MirFunction(name: "sb_fn2", blocks: [], locals: [])
val result = optimize_syscall_batch(func, stats)
val count = stats.syscall_batch_count
expect(count).to_be_greater_than(-1)
```

</details>

### MIR FS Passes — read-ahead hoist

#### AC-4: optimize_read_ahead_hoist accepts MirFunction

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = OptimizationStats.create()
val func = MirFunction(name: "rah_fn", blocks: [], locals: [])
val result = optimize_read_ahead_hoist(func, stats)
val n = result.name
expect(n).to_equal("rah_fn")
```

</details>

#### AC-4: read-ahead hoist stat counter exists after pass

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = OptimizationStats.create()
val func = MirFunction(name: "rah_fn2", blocks: [], locals: [])
val result = optimize_read_ahead_hoist(func, stats)
val count = stats.read_ahead_hoist_count
expect(count).to_be_greater_than(-1)
```

</details>

### Optimizer Manifest — PassScope.FsDriver

#### AC-5: PassScope.FsDriver variant exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = PassScope.FsDriver
val is_fs = scope == PassScope.FsDriver
expect(is_fs).to_equal(true)
```

</details>

#### AC-5: DynamicPassRegistry accepts FsDriver-scoped pass

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = DynamicPassRegistry.new()
val desc = DynamicPassDescriptor(name: "test_fs_pass", scope: PassScope.FsDriver, capability_requires: [])
val r = registry.register(desc)
val ok = r.is_ok()
expect(ok).to_equal(true)
```

</details>

#### AC-5: PassKind includes SyscallBatch variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = PassKind.SyscallBatch
val is_batch = pk == PassKind.SyscallBatch
expect(is_batch).to_equal(true)
```

</details>

#### AC-5: PassKind includes WriteCoalesce variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = PassKind.WriteCoalesce
val is_coalesce = pk == PassKind.WriteCoalesce
expect(is_coalesce).to_equal(true)
```

</details>

#### AC-5: PassKind includes ReadAheadHoist variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = PassKind.ReadAheadHoist
val is_hoist = pk == PassKind.ReadAheadHoist
expect(is_hoist).to_equal(true)
```

</details>

### MIR FS Passes — write coalesce pattern detection

#### detects 2+ stores via same GEP base as coalesce candidate

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gep1 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(10), _fs_copy(0), [_fs_copy(1)]), span: nil)
val store1 = MirInst(kind: MirInstKind.Store(_fs_copy(10), _fs_copy(5)), span: nil)
val gep2 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(11), _fs_copy(0), [_fs_copy(2)]), span: nil)
val store2 = MirInst(kind: MirInstKind.Store(_fs_copy(11), _fs_copy(6)), span: nil)
val block = _fs_block(0, [gep1, store1, gep2, store2], MirTerminator.Ret(nil))
val func = MirFunction(name: "wc_pattern", blocks: [block], locals: [])
val cnt = count_write_coalesce(func)
expect(cnt).to_equal(1)
```

</details>

#### does not count single store as coalesce candidate

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gep1 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(10), _fs_copy(0), [_fs_copy(1)]), span: nil)
val store1 = MirInst(kind: MirInstKind.Store(_fs_copy(10), _fs_copy(5)), span: nil)
val block = _fs_block(0, [gep1, store1], MirTerminator.Ret(nil))
val func = MirFunction(name: "wc_single", blocks: [block], locals: [])
val cnt = count_write_coalesce(func)
expect(cnt).to_equal(0)
```

</details>

#### counts multiple independent GEP bases separately

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gep1 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(10), _fs_copy(0), [_fs_copy(1)]), span: nil)
val store1 = MirInst(kind: MirInstKind.Store(_fs_copy(10), _fs_copy(5)), span: nil)
val gep2 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(11), _fs_copy(0), [_fs_copy(2)]), span: nil)
val store2 = MirInst(kind: MirInstKind.Store(_fs_copy(11), _fs_copy(6)), span: nil)
val gep3 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(12), _fs_copy(3), [_fs_copy(1)]), span: nil)
val store3 = MirInst(kind: MirInstKind.Store(_fs_copy(12), _fs_copy(7)), span: nil)
val gep4 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(13), _fs_copy(3), [_fs_copy(2)]), span: nil)
val store4 = MirInst(kind: MirInstKind.Store(_fs_copy(13), _fs_copy(8)), span: nil)
val block = _fs_block(0, [gep1, store1, gep2, store2, gep3, store3, gep4, store4], MirTerminator.Ret(nil))
val func = MirFunction(name: "wc_multi_base", blocks: [block], locals: [])
val cnt = count_write_coalesce(func)
expect(cnt).to_equal(2)
```

</details>

### MIR FS Passes — syscall batch pattern detection

#### detects consecutive calls to same function as batch candidate

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val call1 = MirInst(kind: MirInstKind.Call(nil, _fs_copy(0), [_fs_copy(1)]), span: nil)
val call2 = MirInst(kind: MirInstKind.Call(nil, _fs_copy(0), [_fs_copy(2)]), span: nil)
val block = _fs_block(0, [call1, call2], MirTerminator.Ret(nil))
val func = MirFunction(name: "sb_pattern", blocks: [block], locals: [])
val cnt = count_syscall_batch(func)
expect(cnt).to_equal(1)
```

</details>

#### does not batch calls to different functions

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val call1 = MirInst(kind: MirInstKind.Call(nil, _fs_copy(0), [_fs_copy(1)]), span: nil)
val call2 = MirInst(kind: MirInstKind.Call(nil, _fs_copy(9), [_fs_copy(2)]), span: nil)
val block = _fs_block(0, [call1, call2], MirTerminator.Ret(nil))
val func = MirFunction(name: "sb_diff", blocks: [block], locals: [])
val cnt = count_syscall_batch(func)
expect(cnt).to_equal(0)
```

</details>

#### breaks batch run on non-call instruction

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val call1 = MirInst(kind: MirInstKind.Call(nil, _fs_copy(0), [_fs_copy(1)]), span: nil)
val load = MirInst(kind: MirInstKind.Load(_fs_lid(20), _fs_copy(5)), span: nil)
val call2 = MirInst(kind: MirInstKind.Call(nil, _fs_copy(0), [_fs_copy(2)]), span: nil)
val block = _fs_block(0, [call1, load, call2], MirTerminator.Ret(nil))
val func = MirFunction(name: "sb_broken", blocks: [block], locals: [])
val cnt = count_syscall_batch(func)
expect(cnt).to_equal(0)
```

</details>

### MIR FS Passes — read-ahead hoist pattern detection

<details>
<summary>Advanced: detects loop-invariant load as hoist candidate</summary>

#### detects loop-invariant load as hoist candidate

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val def_inst = MirInst(kind: MirInstKind.Const(_fs_lid(0), MirConstValue.Int(42), MirType.i64()), span: nil)
val b0 = _fs_block(0, [def_inst], MirTerminator.Goto(BlockId.new(1)))
val load = MirInst(kind: MirInstKind.Load(_fs_lid(10), _fs_copy(0)), span: nil)
val b1 = _fs_block(1, [load], MirTerminator.Goto(BlockId.new(1)))
val func = MirFunction(name: "rah_pattern", blocks: [b0, b1], locals: [])
val cnt = count_read_ahead_hoist(func)
expect(cnt).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: does not hoist load with loop-defined operand</summary>

#### does not hoist load with loop-defined operand

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b0 = _fs_block(0, [], MirTerminator.Goto(BlockId.new(1)))
val def_in_loop = MirInst(kind: MirInstKind.Const(_fs_lid(5), MirConstValue.Int(1), MirType.i64()), span: nil)
val load = MirInst(kind: MirInstKind.Load(_fs_lid(10), _fs_copy(5)), span: nil)
val b1 = _fs_block(1, [def_in_loop, load], MirTerminator.Goto(BlockId.new(1)))
val func = MirFunction(name: "rah_noloop", blocks: [b0, b1], locals: [])
val cnt = count_read_ahead_hoist(func)
expect(cnt).to_equal(0)
```

</details>


</details>

#### skips function with fewer than 2 blocks

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val load = MirInst(kind: MirInstKind.Load(_fs_lid(10), _fs_copy(0)), span: nil)
val b0 = _fs_block(0, [load], MirTerminator.Ret(nil))
val func = MirFunction(name: "rah_short", blocks: [b0], locals: [])
val cnt = count_read_ahead_hoist(func)
expect(cnt).to_equal(0)
```

</details>

### WriteCoalesce Transform

#### inserts bulk_store_hint intrinsic for 2+ stores to same base

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gep1 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(10), _fs_copy(0), [_fs_copy(1)]), span: nil)
val store1 = MirInst(kind: MirInstKind.Store(_fs_copy(10), _fs_copy(5)), span: nil)
val gep2 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(11), _fs_copy(0), [_fs_copy(2)]), span: nil)
val store2 = MirInst(kind: MirInstKind.Store(_fs_copy(11), _fs_copy(6)), span: nil)
val block = _fs_block(0, [gep1, store1, gep2, store2], MirTerminator.Ret(nil))
val func = MirFunction(name: "wc_xform", blocks: [block], locals: [])
val stats = OptimizationStats.create()
val result = optimize_write_coalesce(func, stats)
val rblocks = result.blocks
val rb0 = rblocks[0]
val rinsts = rb0.instructions
val new_len = rinsts.len()
expect(new_len).to_equal(5)
```

</details>

#### does not insert hint for single store

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gep1 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(10), _fs_copy(0), [_fs_copy(1)]), span: nil)
val store1 = MirInst(kind: MirInstKind.Store(_fs_copy(10), _fs_copy(5)), span: nil)
val block = _fs_block(0, [gep1, store1], MirTerminator.Ret(nil))
val func = MirFunction(name: "wc_noxform", blocks: [block], locals: [])
val stats = OptimizationStats.create()
val result = optimize_write_coalesce(func, stats)
val rblocks = result.blocks
val rb0 = rblocks[0]
val rinsts = rb0.instructions
val new_len = rinsts.len()
expect(new_len).to_equal(2)
```

</details>

### SyscallBatch Transform

#### transforms 2+ consecutive same-function calls without error

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val call1 = MirInst(kind: MirInstKind.Call(nil, _fs_copy(0), [_fs_copy(1)]), span: nil)
val call2 = MirInst(kind: MirInstKind.Call(nil, _fs_copy(0), [_fs_copy(2)]), span: nil)
val block = _fs_block(0, [call1, call2], MirTerminator.Ret(nil))
val func = MirFunction(name: "sb_xform", blocks: [block], locals: [])
val cnt = count_syscall_batch(func)
expect(cnt).to_equal(1)
val stats = OptimizationStats.create()
val result = optimize_syscall_batch(func, stats)
val rblocks = result.blocks
val rb0 = rblocks[0]
val rinsts = rb0.instructions
val new_len = rinsts.len()
expect(new_len).to_equal(3)
```

</details>

#### does not insert hint for calls to different functions

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val call1 = MirInst(kind: MirInstKind.Call(nil, _fs_copy(0), [_fs_copy(1)]), span: nil)
val call2 = MirInst(kind: MirInstKind.Call(nil, _fs_copy(9), [_fs_copy(2)]), span: nil)
val block = _fs_block(0, [call1, call2], MirTerminator.Ret(nil))
val func = MirFunction(name: "sb_noxform", blocks: [block], locals: [])
val stats = OptimizationStats.create()
val result = optimize_syscall_batch(func, stats)
val rblocks = result.blocks
val rb0 = rblocks[0]
val rinsts = rb0.instructions
val new_len = rinsts.len()
expect(new_len).to_equal(2)
```

</details>

### Enhanced LICM — Load analysis

<details>
<summary>Advanced: counts loop-invariant Load as hoist candidate</summary>

#### counts loop-invariant Load as hoist candidate

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val def0 = MirInst(kind: MirInstKind.Const(_fs_lid(0), MirConstValue.Int(42), MirType.i64()), span: nil)
val b0 = _fs_block(0, [def0], MirTerminator.Goto(BlockId.new(1)))
val load = MirInst(kind: MirInstKind.Load(_fs_lid(10), _fs_copy(0)), span: nil)
val b1 = _fs_block(1, [load], MirTerminator.Goto(BlockId.new(1)))
val func = MirFunction(name: "licm_load", blocks: [b0, b1], locals: [])
val cnt = count_read_ahead_hoist(func)
expect(cnt).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: does not count Load with loop-defined ptr</summary>

#### does not count Load with loop-defined ptr

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b0 = _fs_block(0, [], MirTerminator.Goto(BlockId.new(1)))
val def_in = MirInst(kind: MirInstKind.Const(_fs_lid(5), MirConstValue.Int(1), MirType.i64()), span: nil)
val load = MirInst(kind: MirInstKind.Load(_fs_lid(10), _fs_copy(5)), span: nil)
val b1 = _fs_block(1, [def_in, load], MirTerminator.Goto(BlockId.new(1)))
val func = MirFunction(name: "licm_noload", blocks: [b0, b1], locals: [])
val cnt = count_read_ahead_hoist(func)
expect(cnt).to_equal(0)
```

</details>


</details>

### Enhanced LICM — GEP analysis

#### GEP with invariant base counts as hoist candidate via write_coalesce

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gep = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(10), _fs_copy(0), [_fs_copy(1)]), span: nil)
val store = MirInst(kind: MirInstKind.Store(_fs_copy(10), _fs_copy(5)), span: nil)
val gep2 = MirInst(kind: MirInstKind.GetElementPtr(_fs_lid(11), _fs_copy(0), [_fs_copy(2)]), span: nil)
val store2 = MirInst(kind: MirInstKind.Store(_fs_copy(11), _fs_copy(6)), span: nil)
val block = _fs_block(0, [gep, store, gep2, store2], MirTerminator.Ret(nil))
val func = MirFunction(name: "licm_gep", blocks: [block], locals: [])
val cnt = count_write_coalesce(func)
expect(cnt).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
