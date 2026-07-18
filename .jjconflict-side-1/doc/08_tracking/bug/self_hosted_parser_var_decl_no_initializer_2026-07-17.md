# self-hosted parser: `var name: Type` without initializer rejected

**Severity:** high (blocks whole entry closures from parsing)
**Found:** 2026-07-17 during stage3 entry-closure hang diagnosis
**Status:** resolved 2026-07-17 (see Resolution below)
**Component:** pure-Simple parser `parse_var_decl_stmt()` — `src/compiler/10.frontend/core/parser_stmts.spl:645-682`

## Symptom

A type-annotated `var` declaration with no initializer, assigned later inside
`if`/`elif`/`match` arms, fails to parse on the self-hosted parser:

```simple
var offscreen: Engine2D
if cond:
    offscreen = make_a()
else:
    offscreen = make_b()
```

`[parser_error] expected =, got Newline`. The seed grammar accepts this form.

First hit at `src/std/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:586`, which
blocks the whole hosted-WM entry closure in phase 2 (see
`stage3_host_entry_closure_retains_unresolved_modules_2026-07-11.md`, 2026-07-17
findings). The same pattern exists in `src/lib/nogc_async_mut/http_server/worker.spl:184,191`,
`static_file.spl:397,505`, `range.spl:64-65`, `spm_service.spl:24-26`,
`test_daemon/daemon.spl:438` — those files simply haven't been in a tested
native-build closure yet.

## Reproduction

Minimal standalone repro (10 lines, no OS/GUI closure needed):
`scratchpad/s4_stage3/minrepro/varnoinit.spl` from the diagnosis session — any
file with `var x: T` + later assignment.

## Root cause

`parse_var_decl_stmt()` unconditionally requires `=` after the optional type
tag; there is no declare-without-initializer branch.

## Fix requirements (why this is not a one-line parser change)

Parser tolerance alone is not enough: a correct fix needs a "no initializer"
representation threaded through HIR lowering, MIR lowering (default-value or
definite-assignment handling), and the interpreter's decl-eval path, so the
declared-but-unassigned local neither crashes nor silently reads garbage.
Must fail loud on read-before-assign or zero-init per seed semantics — match
what the seed does, verified by oracle probes.

## Resolution (2026-07-17)

### Seed-semantics oracle findings

Probed the Rust seed directly (`src/compiler_rust/target/bootstrap/simple`,
`SIMPLE_BOOTSTRAP=1`) with minimal standalone programs:

| Case | Seed behavior |
|------|---------------|
| `var x: i64` declared, assigned in both if/else arms, then read | prints the assigned value (10) — ordinary control flow, no surprises |
| `var x: i64` declared, **read before any assignment** | reads back `0` (silent zero-init) |
| `var t: SomeStruct` declared, assigned before read | works normally |
| `var t: SomeStruct` declared, **field read before assignment** | `runtime error: field access on nil receiver` + crash (SIGILL/core dump) — loud failure, not silent garbage |
| `var s: text` declared, **read before assignment** | undefined/garbage: `.len()` returned `-1`, string interpolation printed `0`, concatenation produced empty/corrupt output — genuine seed-side UB (uninitialized stack bytes), not a stable semantic to replicate |

Conclusion: only two categories have a **safe, well-defined** zero value
worth replicating — scalar primitives (zero) and named struct/class types
(nil, which already fails loud via the existing nil-receiver runtime check on
first field/method access before assignment). `text` (and, by the same
reasoning, `Option`/`Result`/`Dict`/arrays/tuples/fn-types/unions) have no
safe default to copy from the seed, so they are rejected with a located
parser error instead of guessing.

### Fix

Rather than threading a "no initializer" sentinel through HIR/MIR/interpreter
(large blast radius across ~15 files: `closure_analysis.spl`,
`declaration_lowering.spl`, `lowering_helpers.spl`, `cg_stmt.spl`,
`eval_stmts.spl`/`resolve.spl`, several `lint/*.spl` passes, ...), the parser
now **synthesizes a default-value initializer expression** at parse time when
a type-annotated `var` is followed directly by a statement terminator instead
of `=`:

- `bool` → `false` literal
- `i64`/`u8`/`u16`/`u32`/`u64`/`i8`/`i16`/`i32` → `0` literal
- `f64` → `0.0` literal
- resolved named struct/class type (`TYPE_NAMED_BASE+`) → `nil` literal
- an **unresolved** PascalCase identifier type (`TYPE_VOID` fallback because
  `named_type_find` hasn't seen the cross-module struct yet — the case that
  hits for every real-world usage, since `simple check`/native-build on a
  single file has no cross-module type registry populated) → also `nil`
  literal, using the codebase's PascalCase-for-named-types /
  lowercase-for-builtins naming convention as the discriminator
- everything else → a located `parser_error` ("var without initializer not
  yet supported for this declared type...") and a `nil` placeholder so the
  rest of the file still parses structurally, but the build fails loud
  (`par_had_error`)

Because every declare-without-initializer var-decl now carries a normal,
fully-formed init expression by the time it leaves the parser, **zero
downstream files needed changes** — HIR lowering, MIR lowering, the
interpreter, and every lint pass see an ordinary `var x: T = <default>` and
handle it exactly as before. This is the minimal-blast-radius option EXTREME
CAUTION demanded for a hot path interpreted live by every native-build.

Changed: `src/compiler/10.frontend/core/parser_stmts.spl` only (new imports +
`parse_var_decl_stmt` branch + new `var_no_init_default_expr` helper, ~65
added lines, 0 removed).

### Verification

- Minimal repro (`scratchpad/s4_stage3/minrepro/varnoinit.spl`) native-builds
  and runs, printing `1` (matches seed oracle for the assigned-in-both-arms
  struct case).
- All 6 oracle probes re-verified via native-build against the self-hosted
  toolchain: i64 if/else-assign (10), i64 read-before-assign (0), struct
  assign-then-read (1), struct field-read-before-assign (loud SIGSEGV crash,
  matching the seed's loud nil-receiver crash), `var` with initializer still
  works (42/7), `text` no-init rejected with the new located parser error and
  a non-zero native-build exit (no binary produced).
- Real blocker `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:586` now
  parses clean (`All checks passed`) via
  `bin/simple run src/app/check/main.spl <file>`.
- All other files this bug doc named (`http_server/worker.spl`,
  `http_server/static_file.spl`, `http_server/range.spl`,
  `simple_process_manager/spm_service.spl`, `test_daemon/daemon.spl`) now
  parse clean too.
- `sh scripts/check/native-smoke-matrix.shs`: `total=15 pass=15 fail=0
  xfail=0 xpass=0 codegen_fallback_hits=0`.
- Big-file parse sanity (`src/compiler/20.hir/hir_lowering/expressions.spl`
  via the check app): byte-identical output before and after the fix.
