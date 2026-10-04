# module_global_me_method_assign_spec

> For maintainers of the seed interpreter. A module function that reassigns a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# module_global_me_method_assign_spec

For maintainers of the seed interpreter. A module function that reassigns a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/module_global_me_method_assign_spec.spl` |
| Updated | 2026-10-03 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
For maintainers of the seed interpreter. A module function that reassigns a
module `var` from a method called on that same var — `_box = _box.bumped()` —
must leave the NEW value visible to every later call. Under the interpreter the
write used to be reverted when the function returned (the JIT was correct),
which silently broke stateful services such as smux: attaching a client or
closing a pane reported success and changed nothing.
## Operator workflow
bin/simple test test/01_unit/compiler/interpreter/module_global_me_method_assign_spec.spl
## Compatibility and limitations
`simple test` runs specs under the interpreter, which is the engine that had
the defect; `simple run` (JIT) never did.
## Verification guidance and troubleshooting
A value of 0 after a bump means the per-module global store was not updated by
the assignment. See doc/08_tracking/bug/interp_module_global_self_method_assign_reverted_2026-10-03.md.

## Scenarios

### module globals reassigned from their own method result

#### keeps the new value after the function that assigned it returns

- Reset the module counter to zero
- Bump it three times through a function that writes the global in place
- Read the counter back through a different function
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: box_value() equals `3)  # oracle: three bumps from zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-INTERP-GLOBAL-ASSIGN-001
step("Reset the module counter to zero")
reset_box()
step("Bump it three times through a function that writes the global in place")
bump_box_in_place()
bump_box_in_place()
bump_box_in_place()
step("Read the counter back through a different function")
expect(box_value()).to_equal(3)  # oracle: three bumps from zero
```

</details>

#### sees the new value inside the assigning function and after it

- Reset, then bump and read in the same frame
- The in-frame read and the post-return read agree
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: inside equals `1)  # oracle: one bump from zero`
   - Expected: box_value() equals `inside`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-INTERP-GLOBAL-ASSIGN-001
step("Reset, then bump and read in the same frame")
reset_box()
val inside = bump_box_and_read()
step("The in-frame read and the post-return read agree")
expect(inside).to_equal(1)  # oracle: one bump from zero
expect(box_value()).to_equal(inside)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
