# False-@cfg skip swallows the NEXT declaration when its header is multi-line

- **Date:** 2026-10-20
- **Status:** open — tagged source workaround active (the deployed phase-2 producer predates the fix). Root fix MERGED in PR #3932 (`e82781c9304`); retire the workaround once a producer built from it is deployed.
- **Found by:** p4-phase2 lane (producer7 `87b9c74ff39`, source origin/release_phase3 `97aa8eb9e1f`)

## Failure

```
src/os/kernel/scheduler/scheduler_exec.spl: unresolved name: _map_user_process_image   (x4)
src/os/kernel/scheduler/scheduler_executable_adoption.spl: unresolved name: _map_user_process_image
```

Both files import the name correctly from `scheduler_types.spl`, where it is a
`pub fn` and is exported.

## Root cause

The fault is in the `skip_until_dedent` branch of
`src/compiler/10.frontend/core/parser_preprocessor.spl`. After a false-@cfg
declaration, here `@cfg(x86) fn _scheduler_mapped_entry`, the loop adds the
NEXT line's bracket delta before it checks whether the skip has ended.

The next line is the dedented `pub fn _map_user_process_image(`. Its open paren
raises the depth to 1, so the whole following function is blanked: no error,
just a silently missing declaration.

One-file repro. On a non-arm64 target, `b` is dropped:

```
@cfg(arm64)
fn a() -> i64:
    1

fn b(
    x: i64
) -> i64:
    x
```

## Workaround

Tagged `@workaround bug=p4p2_cfg_skip_swallows_next_multiline_decl_2026-10-20`
in `src/os/kernel/scheduler/scheduler_types.spl`, placed before
`pub fn _map_user_process_image(`. The tag is a column-0 comment, which has no
brackets and therefore ends the skip first. The original form is
`97aa8eb9e1f:src/os/kernel/scheduler/scheduler_types.spl:399-400`.

**Risk:** the same thing can happen to any other declaration with a multi-line
header that directly follows an excluded @cfg declaration, anywhere in the tree.

## Root fix

The end-of-skip test now runs before the bracket accumulation when the skip
holds no open bracket. See PR #3932. A producer rebuild is needed before this
workaround can be removed.
