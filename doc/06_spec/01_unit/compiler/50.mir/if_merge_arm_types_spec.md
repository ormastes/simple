# if/else arm type merge contract (mir_merge_arm_types)

Requirement: REQ-SSPEC-COMPILER — regression for
`for_in_if_merge_first_arm_i64_wins_2026-10-24`.
Executable source: test/01_unit/compiler/50.mir/if_merge_arm_types_spec.spl.
Five scenarios, zero placeholders.

| Scenario | Inputs | Expected result |
|---|---|---|
| Unresolved first arm | `merge(I64, Struct)` | `Struct` (the fix under test) |
| Same-type arms | `merge(I64, I64)` | `I64` |
| Struct incumbent | `merge(Struct, I64)` | `Struct` |
| Array element refinement | `merge(Array(I64,0), Array(Struct,0))` | `Array(Struct,0)` |
| Refinement keeps size | `merge(Array(I64,2), Array(Struct,0))` | `Array(Struct,2)` |

`val x = if c: <match> else: call()` merges the two arm result types through
`mir_merge_arm_types`. When the then-arm is a match/Result-payload tail the
lowering could not type, it lowers to bare I64; discarding the struct-typed
else-arm made `for e in x.field` fail with #143. The repair keeps a
struct-typed later arm over an unresolved I64 first arm. I64 array elements
are the lowering's stand-in for "element type unknown"
(`mir_elem_type_is_unspecific`), so the pre-existing refinement of an I64
element from a specific second arm — preserving the incumbent size — is
pinned as unchanged behavior.

Discrimination evidence: with the `I64 → Struct` repair arm removed, scenario
1 fails (`expected i64 to equal struct`); with the repair in place all five
scenarios pass.

Reproduce with the admitted self-hosted runtime once deployed:

```bash
bin/simple test test/01_unit/compiler/50.mir/if_merge_arm_types_spec.spl --mode=interpreter
```

Current-session evidence (Rust seed interpreter, aarch64 Linux host):
`outcome=OK declared>=5 executed=5 passed=5 failed=0 skipped=0 dropped=0`.
Sibling integration spec `if_merge_unresolved_arm_struct_for_in_spec.spl`
re-run: 1/1 (unchanged).
