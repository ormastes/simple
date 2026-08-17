# Stage 3 SIGSEGV: unbounded recursion in `register_imported_type_methods` (2026-08-17)

Status: FIX IN VERIFICATION (P1)

Stage 3 self-host (`native-build` of `src/app/cli/bootstrap_main.spl` by the
admitted Stage 2 compiler) dies with **SIGSEGV, exit 139**, from stack
exhaustion in HIR lowering. Parse is NOT implicated: it completes 619/619 and
the crash lands after it.

## Evidence

Reproduced under gdb with argv and env transcribed verbatim from the
bootstrap's own provenance record
(`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`,
schema `simple-bootstrap-command-transcript-v2`).

- Tree: `/mnt/data/worktrees/simple-boot-snap` (frozen snapshot; `find src/compiler
  src/lib src/app -name '*.spl' -newermt '-3 hours'` returned 0 files).
- Binary: `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`,
  131,324,000 bytes, mtime 2026-08-17 09:17. (NOT `bin/simple`, which is a stale
  Rust seed.)

```
Program received signal SIGSEGV, Segmentation fault.
#0  core::hash::BuildHasher::hash_one
#1  simple_runtime::value::heap::is_registered_heap_ptr
#2  simple_runtime::value::heap::validate_heap_obj
#3  simple_runtime::value::heap::get_typed_ptr_mut
#4  rt_string_len
#5  rt_string_replace
#6  compiler.common.module_path_naming.module_logical_name_from_path
#7  HirLowering.register_imported_type_methods
#8  HirLowering.register_imported_symbol
#9  HirLowering.materialize_imported_callable_type_dependencies
#10 HirLowering.register_imported_type_methods
   ... frames #7-#9 repeat for the entire backtrace ...
rsp = 0x7fffff7ff000   <- stack guard page
rbp = 0x1              <- bogus
```

`rsp` on the guard page plus an unbounded repeating 3-frame cycle is stack
exhaustion, not a wild pointer. Frames #0-#6 are incidental: they are merely
what happened to be executing when the last page ran out.

## Mechanism

`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`, cycle:

```
register_imported_type_methods                        (:1453)
  -> materialize_imported_callable_type_dependencies  (:1469, :1492)
  -> register_imported_symbol                         (:1433, :1436, :1440, :1444, :1447, :1451)
  -> register_imported_type_methods                   (:768 composite, :789 enum)
```

Every guard on the path is **check-then-recurse** against the symbol table
(`lookup_qualified_type_raw(...) < 0`; `lookup_or_invalid(...).is_valid()`).
That terminates only if the callee is fully registered BEFORE the descent.

- **Composite path terminates.** `:741-744` defines the symbol and calls
  `bind_qualified_type`, and `:745-746` returns early when `already_bound`, so a
  re-entrant call is refused.
- **Enum path does not.** `:769-789` calls `register_imported_type_methods`
  unconditionally at `:789` with no `already_bound` early return. That is
  deliberate -- gating it inside `not already_bound` silently routed imported
  `DbValue.to_text()` to generic enum stringification (comment at `:784-788`).

So two types declared in one module whose method SIGNATURES mention each other
re-enter the cycle forever.

## Class recurrence

This is the same failure class as
`stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`. The essay at
`src/compiler/20.hir/hir_types.spl:396-433` records that instance: a
`rt_dict_contains` false negative on a struct-valued `Dict` disabled the only
re-entrancy breakers in this cycle, "producing unbounded mutual recursion ...
that overflowed the stack and SIGSEGVed Stage 3 with zero diagnostic output."

Standing lesson: **every breaker in this cycle has historically been a
membership test that can fail open.** A breaker here must not depend on Dict
membership semantics.

## Fix

Re-entrancy breaker at the top of `register_imported_type_methods`; the original
body moved verbatim to `register_imported_type_methods_inner`. Registering a
type's methods is idempotent, so refusing a re-entrant call loses no work -- the
in-flight outer call performs it.

State: `imported_type_methods_in_progress: [text]` on `HirLowering`
(`src/compiler/20.hir/hir_lowering/types.spl` -- field, initializer, and a reset
in `begin_module`).

Deliberately a plain `[text]` used as a stack with a linear scan, **not a Dict**:
per the recurrence note above, a Dict membership breaker in this exact cycle has
already failed open once and cost a full day of Stage 3 debugging. Depth guarded
is type-reference nesting depth, which is small.

Notably the fix does NOT revert `:789`, so the `DbValue.to_text()` behaviour that
motivated the unconditional call is preserved.

## Why this took a day to find

`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log` was
**0 bytes** across every failing run, so the crash was unattributable. The
redirect is correct (`) >"$log" 2>&1`,
`scripts/check/lib/bootstrap-stage3/command-snapshot.shs:227`, status read on
the next line at `:228`). It is empty by design: the provenance gate at
`scripts/bootstrap/bootstrap-from-scratch.sh:2026-2028` relies on the in-process
pure-Simple driver printing nothing to stdout in order to detect Rust-seed
delegation. Diagnostics went only to `SIMPLE_BUILD_PROGRESS_EVENTS`.

Two contributing traps, both since fixed, that sent three lanes to wrong causes:

1. **`exit-2` is not the compiler's status.** The progress log's terminal
   `milestone=exit-2` is the WRAPPER SCRIPT's exit code (non-strict mode ->
   warning -> "Stage 3 unavailable" -> 2). The compiler's real status is 139.
   `bootstrap-from-scratch.sh:2069` also sets `stage3_status=2` for a genuine
   sanity failure, which is a DIFFERENT event -- distinguish them by whether
   `stage3/<platform>/stage3-sanity.env` exists. In every run here it did not,
   so sanity never ran.
2. **Progress `current=` was stale by up to 63 files** (the `% 64 == 0` cadence
   at `driver_source_pipeline_parsing.spl:275` pre-`4d1aca2d799`), which framed
   this as a "parse tail stall" and named an innocent file. Now one receipt per
   file. Same trap still live for the `source_closure` phase
   (`driver_source_pipeline_loading.spl:192,196`).

Also note **stack-overflow depth is sensitive to environment size**, so the
crash appears to move: the same binary died at parse file 1 in one run and
completed all 619 files then crashed in HIR lowering under gdb. That is not
nondeterminism or ASLR -- do not read it as a wild pointer.
