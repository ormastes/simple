# Unsafe capability block cannot initialize a value

**Status:** open parser/lowering bug, source and execution reproduced

The Rust bootstrap parser accepts lexical capability blocks as statements:

```simple
var value: i64 = -1
unsafe(capabilities: [ffi]):
    value = rt_clock()
```

It rejects the equivalent compact block expression:

```simple
val value = unsafe(capabilities: [ffi]):
    rt_clock()
```

`bin/simple check` reports `unexpected token in expression: ':'` at the block
colon, followed by an unexpected indent. This prevents a safe, compact
proof-producing lift at SFFI boundaries and forces a mutable staging local.

The `rt_time` hardening uses the accepted statement form so safety work can
continue. Fix the parser and HIR lowering so an unsafe block is a normal block
expression whose value is its tail expression; retain the same lexical
capability metadata and erase it only after safety checking.
