# Bug: local variable named `kernel` shadowed by module name — HIR lowering + interp hard-fail

- **Date:** 2026-07-06
- **Status:** open (workaround applied at call sites)
- **Area:** compiler name resolution (HIR lowering + interpreter semantic pass)

## Symptom

Any function with a local `var kernel = ...` that is later read fails when the
file is inside the repo module map:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown variable: kernel while lowering <fn>
error: semantic: variable `kernel` not found
```

The interpreter fallback ALSO hard-fails, so the function is unusable.

## Minimal repro

Put this anywhere inside the repo (e.g. `build/probe/p1.spl`) and run
`bin/simple run build/probe/p1.spl` — no imports needed:

```simple
fn run(args: [text]) -> i32:
    var kernel = ""
    for arg in args:
        if arg.starts_with("--kernel="):
            kernel = arg.slice(9, arg.len())
    print "kernel={kernel}"
    0

fn main() -> i32:
    run(["packages"])
```

Renaming `kernel` -> `kpath` fixes it. The same file OUTSIDE the repo
(no module map, dynamic interp mode) runs fine, so the local is being
shadowed by the `os.kernel` module namespace (src/os/kernel/) during
name resolution instead of the local binding winning.

## Expected

Local bindings must shadow module/namespace names.

## Workaround applied

Renamed locals `kernel` -> `kernel_elf` in:
- `src/os/installer/release_pipeline.spl` (release_all, release_usb, run_release)
- `src/os/installer/image_builder.spl` (run_image_builder)

These entrypoints were completely broken (release/image-builder CLI unusable)
until the rename.

## Verification (2026-07-17)

Runtime repro at tip 9feac6ef6e5:

Probe: `probe05_kernel_shadow.spl` (doc's exact minimal repro, from worktree
context with module map in scope).

Output matches byte-for-byte:
```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown variable: kernel while lowering run
error: semantic: variable `kernel` not found
```

**Status:** STILL-REPRODUCES (exact match).
