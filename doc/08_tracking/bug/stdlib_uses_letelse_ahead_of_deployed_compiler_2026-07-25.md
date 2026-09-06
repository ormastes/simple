# stdlib used refutable `val Some(x) = e else:` that no shipped compiler binary can parse — broke every build compiling `env/variables.spl`

- **ID:** stdlib_uses_letelse_ahead_of_deployed_compiler_2026-07-25
- **Status:** WORKED AROUND at the single call site; the sequencing gap is OPEN
- **Severity:** high — `src/lib/nogc_sync_mut/env/variables.spl` is core stdlib,
  so **any** build whose import closure reaches it fails at parse time

## Symptom

```
Build failed: failed to parse src/lib/nogc_sync_mut/env/variables.spl
  at 362:43 during discovery: Unexpected token: expected expression, found Else
```

Column 43 is the `else`. This surfaced as
`simpleos_wm_fullscreen_reason=wm-simple-web-build-failed` /
`kernel_build_status=failed-cache-preserved` on the SimpleOS-WM cell, but it is
not specific to that cell — it breaks anything that compiles this file.

## Root cause: source migrated ahead of the toolchain

The offending line was:

```
val Some(dollar_idx) = dollar_pos else: break
```

The refutable let-else binding **is** implemented in the compiler source
(`src/compiler/10.frontend/core/parser_stmts.spl`, grep `let_else`). It is
**not** in any binary anyone actually builds with. Measured directly:

| binary | parses `val Some(x) = e else:` |
|---|---|
| `bin/simple` (Rust seed, currently deployed) | **no** — same parse error |
| `build/bootstrap/stage3/.../simple` (harness's cached binary) | **no** |

So the feature exists in source, the stdlib started using it, and no compiler
that exists on disk can compile the result. A language feature must ship in a
**deployed** compiler before stdlib may depend on it; this inverted that order.

## Why it appeared to regress suddenly

An earlier run of the same harness reported `kernel_build_status=current-source-built`
and got as far as the render stage. The bad line was already present then — it
was simply **cached** (`5 compiled, 657 cached`). A parallel session's refactor
of `simple_web_html_layout_renderer.spl` (9,900 lines -> 472) invalidated the
native cache, so this file was recompiled for the first time and the latent
break surfaced. **A green build over a warm cache is not evidence the sources
compile.**

## Blast radius: exactly one site

```sh
grep -rnE "^\s*val [A-Z][A-Za-z]*\(.*\)\s*=.*\selse:" src/ --include=*.spl
```

returns **1** match — this line. Session memory recalled "22 stdlib sites
migrated"; that is not the current state of the tree, and the recollection
should not be trusted over the grep. A single straggler was left behind, in one
of the most widely-imported files in the stdlib.

## Fix applied

Replaced with the form the file already uses three times elsewhere (lines with
`if val Some(...)`), via a nil-coalesce that the guard above makes total:

```
if not dollar_pos.?:
    break
val dollar_idx = dollar_pos ?? 0
```

Verified against the actual binary that must compile it before editing — a
standalone probe of the `??` form returns `a=2` (found at index 2) and `b=-1`
(absent), i.e. correct Option semantics on the seed parser.

Per the project rule against silently normalizing a workaround, this is
**recorded, not absorbed**: the call site carries a comment pointing here, and
the `??` default is documented as unreachable rather than left looking like a
real fallback.

## What still needs doing

1. **Restore the let-else form once a compiler carrying it is deployed.** The
   feature is good and the original line was clearer. This is a sequencing
   revert, not an abandonment.
2. **Add a guard so stdlib cannot outrun the toolchain again.** A lint that
   parses `src/lib/**` with the *deployed* binary would have caught this at
   commit time instead of inside a 10-minute kernel build.
3. **Do not "fix" this by deploying a new compiler without approval** — that is
   a separate, heavier change with its own verification bar.

## Related

- `.claude/rules/language.md` — reserved keywords / grammar constraints
- Session memory `project_letelse_refutable_val_binding_2026-07-25` records the
  original feature work as "NOT pushed till verified"; the stdlib edit reached
  the tree regardless. Treat that memory as describing intent, not tree state.
