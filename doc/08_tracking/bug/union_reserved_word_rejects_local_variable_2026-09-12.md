# `union` is reserved: a local variable named `union` cannot be used

- Status: OPEN (2026-09-12)
- Component: parser (seed `src/compiler_rust`), statement-start keyword lookahead
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f9ab5704b`
- Found by: L78-INT while integrating the L7/L8 V4 port packets

## Symptom

A local variable may be DECLARED as `union` but cannot be USED at
statement start. The parser reads `union` as a union-declaration keyword
and expects a type name:

```
Unexpected token: expected identifier, found Dot
```

As with the sibling trait-wrap bug, the error names the file but no line.

## Repro (fails)

```simple
pub fn main():
    var union: [i64] = []
    union.push(1)
    print("{union.len()}")
```

## Control (parses, prints 1)

The identical program with the variable renamed to `joined`.

## Impact

Pre-existing at the integration base `e71f20d45212`, not introduced by any
L7/L8 packet: `git show e71f20d45212:src/compiler/80.driver/cache/reference/
reverse_reference_coordinator_v1.spl` fails to parse for this reason, in
`old_new_membership_union_v1`. That made every spec whose module graph
reaches the reverse-reference coordinator report
`outcome=ERROR executed=0`, including
`test/01_unit/compiler/cache/l78_scope_port_v4_spec.spl` and
`l78_affected_domain_port_v4_spec.spl`.

## Workaround applied (this is a workaround, not the fix)

The local was renamed `union` -> `merged` in `old_new_membership_union_v1`.
The public function name `old_new_membership_union_v1` is untouched. Either
`union` should be usable as an identifier, or it should be rejected at its
DECLARATION with a message that names the reserved word and the line.
