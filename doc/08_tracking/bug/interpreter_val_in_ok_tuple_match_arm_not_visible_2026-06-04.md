# Bug: `val` declared inside an `Ok((a, b))` tuple-match arm is not visible later in the same arm

Status: Fixed (2026-06-12, commit 964a30ebe86)

**Date:** 2026-06-04
**Area:** Interpreter, pattern-match arm scoping (SPipe `it` blocks)
**Status:** Fixed (2026-06-12)
**Severity:** Medium

## Summary

Inside an `it` block, when matching a `Result<(A, B), E>` with a destructuring
arm `Ok((a, b)):`, a `val`/`var` declared in that arm's body is not visible to
later statements in the same arm. The interpreter raises
`semantic: variable '<name>' not found` at the use site.

Discovered implementing the SFM codec spec: the "re-encode idempotent" example

```simple
match decode_sfm(first):
    Ok((m2, smf2)):
        val second: [u8] = encode_sfm(m2, smf2)   # declared here
        assert_true(bytes_equal(second, first))     # `second` not found
    Err(e):
        expect("decode-failed: " + e).to_equal("ok")
```

failed with `semantic: variable 'second' not found`, even though the tuple
bindings `m2`/`smf2` from the pattern ARE visible. The problem is specific to a
fresh `val`/`var` *declared inside* the destructuring arm body.

## Reproduction

Minimal shape (interpreter `it`-block execution):

```simple
match (Ok(("x", "y")) as Result<(text, text), text>):
    Ok((a, b)):
        val joined = a + b
        expect(joined).to_equal("xy")   # `joined` reported not found
    Err(_):
        assert_true(false)
```

Run: `bin/release/<triple>/simple run <spec>` (which executes it-blocks).

**Note:** The actual trigger is a *type-annotated* `val` (e.g., `val joined: text = ...`
or `val second: [u8] = ...`). The bare-identifier form `val joined = a + b` was
silently bound even before the fix (the old code hand-rolled `Pattern::Identifier`
extraction). The real reproduction uses an explicit type annotation; the SFM case
used `val second: [u8]`.

## Workaround

Move the logic that needs the local into a top-level helper fn that takes the
pattern bindings as parameters, so no `val`/`var` is declared inside the arm:

```simple
fn reencode_matches(m2: FeatureManifest, smf2: [u8], first: [u8]) -> bool:
    val second: [u8] = encode_sfm(m2, smf2)
    return bytes_equal(second, first)

# in the arm:
Ok((m2, smf2)): assert_true(reencode_matches(m2, smf2, first))
```

Applied in `test/03_system/feature/sfm/sfm_codec_spec.spl`.

## Root Cause and Fix

**Fixed:** 2026-06-12, commit `964a30ebe86` ("fix(interpreter): typed/tuple Let bindings in nested closure blocks bound nothing").

Root cause: `exec_block_closure_mut` in
`src/compiler_rust/compiler/src/interpreter_call/block_execution.rs` hand-rolled
only `Pattern::Identifier` extraction in its `Node::Let` arm, silently dropping
`Pattern::Typed` (i.e., `val x: T = ...`) bindings. When a typed `val` was
declared inside a match arm body (or any nested block within a describe/it
closure), the variable was never inserted into `local_env`, so subsequent reads
produced `semantic: variable '<name>' not found`.

The fix replaced the hand-rolled identifier extraction with a call to the shared
`bind_pattern_value(&let_stmt.pattern, val, is_mutable, local_env)` helper,
which handles all pattern forms including `Pattern::Typed`, `Pattern::Tuple`, and
destructuring patterns.

Regression test added:
`test/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.spl`
(two new `it` blocks covering `Ok((a,b))` match arm with typed vals, 2026-06-14).

## Related

`baremetal_enum_record_result_destructure_2026-05-30.md` and
`spipe_interpreter_tuple_map_result_matcher_binding_2026-05-27.md` touch
adjacent destructure/scoping paths but not this exact arm-local-declaration case.
