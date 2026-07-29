# Stage2 drops the else addend of a conditional expression

## Witness

Pinned pure-Simple Stage2 SHA-256:
`7f9f101472ba081ba89e58137820eb24fc8357f0d050c52c24fb725b6b14e142`.

In `ot_layout_gpos_basic.spl`, native lowering of:

```simple
(if kind == 5u32: ligature else: target_array) + anchor_offset
```

zeroes the base for the `else` branch and passes only `anchor_offset`.
MarkToBase and MarkToMark therefore read an anchor from the wrong address.

## Temporary source form

Assign the default base to a mutable local, override it in the `kind == 5`
branch, then add the offset. Remove that workaround after the native
conditional-expression fixture passes under the deployed self-hosted compiler.
