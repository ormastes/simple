# Stage 3 SEGV: the HIR enum-payload closure recurses the main stack to death on `compiler.driver.driver` (2026-09-14)

- **Status:** OPEN — reproduced twice, crash class and recursion cycle both
  identified from a real backtrace. Fix NOT landed; see "Which fix" below, which
  turns on one measurement that was in flight when this record was written.
- **Blocks:** the whole Stage 3 → Stage 4 → deploy chain on macOS
  (`aarch64-apple-darwin`). No Stage 3 artifact, no Stage 4, nothing deployed.
- **Supersedes as the live blocker:** the F74 round-3 entry "Stage 3
  native-build SEGFAULTS in the HIR phase at unit 2 of 833".

## Symptom

Stage 3 (`resume-stage3-from-admitted.sh`, direct route, `--threads 1`) dies
after ~22 minutes with `Segmentation fault: 11` (shell rc 139) while HIR-lowering
unit 2 of 833:

```
[build] phase=hir ... done=1 total=833 ... current=app.cli.bootstrap_main    <- OK
[build] phase=hir ... done=1 total=833 ... current=compiler.driver.driver    <- dies ~6 s later
command-snapshot.shs: line 274: 69063 Segmentation fault: 11  env -i ...
```

`app.cli.bootstrap_main` (unit 1) lowers cleanly, so this is not a general HIR
failure — it is specific to the import fan-out of `src/compiler/driver/driver.spl`.

## Reproduction

`scripts/bootstrap/resume-stage3-from-admitted.sh` writes the exact env and argv
to `<stage3 dir>/stage3-command.transcript`. Replaying that transcript
byte-for-byte under lldb, with only the cache / output / evidence paths
redirected to a scratch dir, reproduces it deterministically at ~22 minutes:

```
lldb --batch --source-quietly -o run \
  -k 'thread info' -k 'register read pc sp fp' -k 'thread backtrace -c N' -k quit \
  -o quit -- <stage2-admitted>/simple native-build --target aarch64-apple-darwin \
  --backend llvm --runtime-bundle core-c-bootstrap --threads 1 \
  --cache-dir <scratch> --mode dynload --runtime-path <stage2-runtime-authority> \
  -o <scratch>/out-simple src/app/cli/bootstrap_main.spl
```

**Use `-k` (crash commands), not `-o`.** With `-o 'bt 80'` after `-o run`, lldb
printed the stop banner and then exited without ever emitting a backtrace — the
first repro run produced the crash class and nothing else. The `-k` form works,
and `-c <count>` is required: an unbounded `bt` on a stack this deep does not
return.

## Crash class: stack overflow (not a miscompile, not a heap defect)

```
Process 12291 stopped
* thread #1, queue = 'com.apple.main-thread',
  stop reason = EXC_BAD_ACCESS (code=2, address=0x16f603ff0)
  frame #0: simple`core::hash::sip::Hasher::write
  ->  0x1008bea38 <+0>:  stp  x26, x25, [sp, #-0x50]!
      sp = 0x000000016f604040
```

Three independent facts pin this:

- `code=2` is a **write** fault, and the faulting address `0x16f603ff0` sits
  immediately **below `sp`** (`0x16f604040`) in the main-thread stack region;
- the faulting instruction is the **first instruction of a function prologue** —
  the `stp ..., [sp, #-0x50]!` that allocates the frame;
- the thread is `#1, queue = 'com.apple.main-thread'`, so this is the 8 MB main
  stack, **not** a 512 KB pthread-default secondary stack.

That is the signature of stepping onto the stack guard page.

It **rules out** two branches that were on the table:

- a seed-codegen miscompile of an erased receiver / Option-or-enum payload would
  be `code=1` at a small or wild address, not `code=2` one word below `sp`;
- a runtime/C defect such as `rt_transient_heap_promote` on a large array would
  put an `rt_*` symbol at frame #0 as the *cause*, not as an innocent bystander.

`rt_string_new` / `rt_string_replace` appear at frames #6-#7 only because they
are the callee that happened to need the next frame. They are not the defect.

## The recursion (verbatim, from the backtrace)

Frames #11-#15 repeat as an exact four-symbol unit for the entire captured
backtrace:

```
 #11  module_import_registration       HirLowering.register_imported_symbol_inner + 4648
 #12  module_import_registration       HirLowering.register_imported_symbol + 768
 #13  module_reexport_materialization  HirLowering.register_materialized_payload_named_dependency_inner
 #14  module_reexport_materialization  HirLowering.register_materialized_enum_payload_dependencies
 #15  module_import_registration       HirLowering.register_imported_symbol_inner + 1772
 #16  module_import_registration       HirLowering.register_imported_symbol + 768
 #17  module_reexport_materialization  HirLowering.register_materialized_payload_named_dependency_inner
 #18  module_reexport_materialization  HirLowering.register_materialized_enum_payload_dependencies
 ... (repeats)
```

i.e. the cycle is

```
register_imported_symbol
  -> register_imported_symbol_inner            (call site at +1772, module_import_registration.spl:367)
     -> register_materialized_enum_payload_dependencies   (module_reexport_materialization.spl:564)
        -> register_materialized_payload_named_dependency(_inner)  (:485/:491)
           -> register_imported_symbol         (:537, materialize_enum = true)
              -> ...
```

**This is NOT the cycle fixed on 2026-08-17.** That one was
`register_imported_type_methods -> materialize_imported_callable_type_dependencies
-> register_imported_symbol -> register_imported_type_methods`, and its breaker
(`imported_type_methods_in_progress`, `module_reexport_materialization.spl:1048-1091`)
does not sit on any edge of the cycle above. Do not assume the old fix covers this.

Note also that `register_imported_symbol`'s own `registered_import_memo`
(`module_import_registration.spl:126-146`) is **deliberately not** a re-entrancy
breaker — its own comment says so: *"A key is recorded only AFTER the body
returns. Marking on entry would have been a cheap re-entrancy breaker, but ..."*.
It delegates cycle-breaking to "the existing guards", and on this cycle the only
such guard is the mark-on-entry in `register_materialized_enum_payload_dependencies`:

```
val identity = hir_payload_terminal_identity(imported_mod.module_name, enum_.name, "enum")
if self.materialized_payload_origins.contains_key(identity): return
self.materialized_payload_origins[identity] = true
```

## Which fix — this turns on one measurement

The guard above marks on ENTRY, so *if it is working*, every level of the
observed recursion is a **distinct** enum identity and the depth is bounded by
the number of distinct enums reachable from `driver.spl`'s closure. The tree
declares **2,280** enums across `src/compiler`, `src/lib` and `src/app`
(`grep -rhoE '^\s*(pub )?enum [A-Za-z_]+' | wc -l`). 8 MB / 2,280 levels is
~3.6 KB per four-frame level, which is entirely plausible for functions this
large (`register_imported_symbol_inner` is multi-KB — the two call sites are at
+1772 and +4648 of the same function).

So there are two candidate root causes and the measured stack DEPTH separates
them:

1. **Depth ≈ 2,000-2,500 → the guard works; the recursion is finite but too
   deep for an 8 MB stack.** The fix is to flatten the enum-payload closure walk
   into an explicit worklist (trampoline the `register_imported_symbol` call at
   `module_reexport_materialization.spl:537` onto a pending queue drained by the
   outermost frame), not to add another breaker. Raising the stack is NOT
   available as a lever — see below.
2. **Depth >> 2,280 → the `materialized_payload_origins` mark-on-entry is not
   taking effect**, i.e. a genuine infinite cycle. The fix is a re-entrancy
   breaker on `register_materialized_payload_named_dependency_inner` keyed on its
   input tuple `(imported_mod_name, dependency)`, built as a plain `[text]` stack
   rather than a Dict — **exactly** the shape used for
   `imported_type_methods_in_progress`, and for the reason given there: a Dict
   membership memo in this very file was silently disabled once before by
   `rt_dict_contains` under-reporting under native codegen
   (`stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`). If this
   branch is the live one, the under-reporting is itself a native-codegen defect
   and needs its own record.

A depth-measuring repro (`thread backtrace -c 6000`) was in flight when this
record was written; its log is `build/f75logs/repro-lldb-3.log`.

**Do not guess between these two.** Both fixes are invasive in a delicate area
(the "binding and expansion are deliberately distinct" comment at
`module_reexport_materialization.spl:529-534` exists because an earlier
simplification broke aliases in a cycle), each verification cycle costs ~22
minutes, and shipping the wrong one would be a compiler regression.

## There is no stack-size lever

`--compile-stack-mib` looks like one and is not: it is passed on the **Stage 2**
argv and has **zero consumers in product code**. `grep -rn stack_mib src`
returns nothing; the flag appears only in
`scripts/bootstrap/resume-stage3-from-admitted.sh`,
`scripts/check/lib/bootstrap-stage3-candidate-builder.shs` and
`scripts/check/lib/bootstrap-stage3/{self-test,manifest-verify}.shs`. The Stage 3
argv does not carry it at all. Nothing under `src/` calls
`pthread_attr_setstacksize` on this path either (the only owned-code hit is
`src/os/libc/simpleos_pthread.c`, a different target).

## Why it surfaced now

F74 round 3 landed #952, which eliminated all 12 `has no declaration owner`
failures. Unit 1 now lowers where it previously failed, and more names resolve —
which makes the payload closure *deeper*, not shallower. The chain did not
regress; it advanced past the old defect into this one.

## Evidence

- `build/f75logs/repro-lldb.log:12077-12085` — crash class (run 1).
- `build/f75logs/repro-lldb-2.log:12075-12238` — the 151-frame backtrace quoted
  above (run 2).
- `build/f75logs/repro-lldb-3.log` — depth measurement (run 3).
- `build/f74logs/stage3-run5-native-build.log:11971-12081` — the original lane
  failure.
- Source: `src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl:485-600`,
  `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:97-150,367`.
- Related, NOT the same defect:
  `stage3_register_imported_type_methods_infinite_recursion_2026-08-17.md`,
  `hir_phase_per_module_cost_2026-08-21.md` (which already measured `driver.spl`
  as the worst case in this phase: 377 s of its 427 s HIR inside
  `materialize_imported_field_dependency`, 8,284 registrations).
