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

## Root cause (corrected, 2026-07-17)

The original hypothesis (local `kernel` shadowed by the `os.kernel` module
namespace) does NOT match the actual mechanism — the repro reproduces
byte-for-byte identically OUTSIDE the repo (no module map in scope, verified
directly), which rules out any module/namespace resolution involvement.

The real root cause is a **parser keyword-capitalization bug** in the Rust
seed (`src/compiler_rust`), unrelated to modules:

- `kernel` is a lexer keyword (`TokenKind::Kernel`, for `kernel fn ...` GPU
  kernel-function declarations; see `src/compiler_rust/parser/src/lexer/identifiers.rs:169`).
- On the **expression** side, reading `kernel` correctly maps the keyword
  token back to the lowercase identifier string `"kernel"`
  (`src/compiler_rust/parser/src/expressions/primary/identifiers.rs:84`,
  `parse_keyword_identifier("kernel")`).
- On the **pattern** side (used by `var`/`val`/`let` declarations AND match
  bindings, via `parse_let_impl` -> `parse_pattern` -> `parse_single_pattern`),
  the same keyword token was mapped through
  `parse_keyword_as_pattern("Kernel")` — **capitalized** — in
  `src/compiler_rust/parser/src/parser_patterns.rs:567`. That capitalization
  is correct for the function's *other* two branches (enum-variant-with-payload
  and qualified-path patterns, where PascalCase is the right convention for a
  variant/enum name), but the plain-identifier fallback branch (no `(`, `.`,
  or `::` following) reused the same capitalized string for a local variable
  *binding* name.

Net effect: `var kernel = ""` binds the local as `Pattern::Identifier("Kernel")`
(capital K) while every *read* of `kernel` looks up lowercase `"kernel"` in the
interpreter `Env` / HIR scope — a permanent mismatch, so the read never finds
the declaration. This is the exact same bug class as the already-partially-fixed
`unit` keyword collision (see the comment in
`expressions/primary/identifiers.rs` about
`interp_unit_param_keyword_collision_2026-06-13`), just on the pattern side
instead of the expression side, and for the `kernel` keyword instead of `unit`.

This also explains every observed data point:
- A subsequent plain `kernel = arg` **assignment** (not a `var` declaration)
  extracts its target name via the expression-side identifier parsing (already
  correctly lowercase), so it creates a *second*, correctly-lowercased `env`
  entry — which is why the bug appeared to "go away" whenever the assignment
  branch actually ran at runtime, and only manifested when the local was read
  without ever being reassigned via a plain `=`.
- It reproduces identically inside and outside the repo, and regardless of
  string content, print format, or method calls on the RHS — none of those
  factors are actually involved.

## Fix

`src/compiler_rust/parser/src/parser_patterns.rs`: `parse_keyword_as_pattern`
now uses `name.to_lowercase()` for the plain-identifier fallback branch only
(the enum-variant branches are untouched, still using the PascalCase `name`
as before). Since every caller's PascalCase spelling differs from the actual
keyword only in the first letter's case (single-word keywords, no internal
caps), this is a safe, minimal, one-line behavioral fix that also resolves the
identical latent bug for every other keyword in that same call list (`Loop`,
`Vec`, `Unit`, `Sync`, `Async`, `Shared`, `Gpu`, `Extern`, `Static`, `Const`,
`Repr`, `Dyn`, `Macro`, `Mixin`, `Actor`, `Ghost`, `Impl`, `Val`, `Literal`,
`Asm`, `Bitfield`, `Newtype`, `Extend`, `Comptime`, `Struct`, `Enum`, `Class`,
`Fn`, `Trait`, `Self`, `Export`) without touching ~40 call sites individually.

**NOTE — inert until seed rebuild:** per repo convention (see the `unit`
keyword comment in `identifiers.rs`), this source fix cannot be exercised by
the currently-deployed binary without a bootstrap rebuild (forbidden in this
lane per `.claude/rules/bootstrap.md` / this session's hard rules). Verified
by static analysis + exhaustive behavioral bisection against the current
(unfixed) binary using safe stand-in names (`kpath`) that hit the exact same
code paths without the keyword collision — see
`doc/08_tracking/bug/interpreter_nested_block_var_redeclare_leaks_scope_2026-07-17.md`
for one unrelated pre-existing scoping gap found (and left unfixed, out of
scope) while probing this.

The self-hosted pure-Simple compiler (`src/compiler/10.frontend/`) also has a
`KwKernel` token but does not implement the same "keyword reused as pattern
identifier with wrong case" mechanism (no analogous `parse_keyword_as_pattern`
found there), so no companion fix was made there — no evidence of the same
defect in that codebase.

The workaround renames (`release_pipeline.spl`, `image_builder.spl`) are safe
to keep or revert once the seed is rebuilt with this fix; not reverted in this
patch (source-only fix, no bootstrap performed in this lane).
