# JIT SEGV: `AggregateCopy` truncates trait-implementing structs by 8 bytes (2026-08-27)

Status: **ROOT-CAUSED AND FIXED** in the Rust seed (Cranelift JIT codegen).
Originally filed as an `sj` bug against the "hybrid-interp-splice engine"; that
attribution was **wrong** and is corrected below. The source-side `sj` workaround
is no longer needed.

## Corrected diagnosis

The defect is in **Cranelift JIT codegen**, not the interpreter and not the
hybrid interp-splice.

- `SIMPLE_EXECUTION_MODE=interpreter` — always correct, exit 0.
- default (JIT) — SIGSEGV.
- The minimal reproducer below crashes with **no stdlib, no externs, and no
  `[engine-demotion]` line at all**, which exonerates the splice entirely. The
  splice was merely co-present in the original `sj` runs.

Crash signature (gdb, launch not attach): every frame is in anonymous mmap'd JIT
memory (`??`, base re-randomises per run). Faulting instruction
`mov (%r10),%r9` with `si_addr = 0x30` — a near-null base used as an object
pointer, i.e. a field slot read from outside its allocation.

## Minimal reproducer

`repro/min.spl` in the worktree (38 lines, self-contained):

```
trait Handler:
    fn handle(self, req: text) -> text

class Mgr:
    n: i64
    me bump(k: i64) -> i64:
        self.n = self.n + k
        self.n

struct Inner:
    name: text
    limit: i64
    mgr: Mgr

struct Outer:
    flag: bool
    inner: Inner

impl Handler for Inner:
    fn handle(self, req: text) -> text:
        "{use_inner(self)}"

fn use_inner(h: Inner) -> i64:
    h.mgr.bump(h.limit)

fn takes_outer(o: Outer) -> i64:
    val h = o.inner
    use_inner(h)

fn main() -> i64:
    val o = Outer(flag: false, inner: Inner(name: ".", limit: 5i64, mgr: Mgr(n: 0i64)))
    print("r={takes_outer(o)}")
    0i64
```

`bin/simple run repro/min.spl` -> rc=139. `SIMPLE_EXECUTION_MODE=interpreter` -> `r=5`, rc=0.

### Load-bearing ingredients (ablation, each independently necessary)

| variant | JIT rc |
|---|---|
| baseline | **139** |
| remove `impl Handler for Inner` | 0 |
| move the impl to `Outer` instead | 0 |
| `Mgr` a `struct` instead of a `class` | 0 |
| caller passes `Inner` directly (no `Outer` param) | 0 |
| `use_inner(o.inner)` without the `val h` temp | **139** (temp is NOT required) |

So: a **trait impl on the inner struct** + that struct reached as a **field of an
outer struct parameter** + a **class-typed field** in it. The impl's *body* is
irrelevant — replacing it with a constant `"x"` still crashes; a plain non-impl
function with the same signature does not. Only the impl's **existence** matters.

MIR is identical between the crashing and non-crashing variants except for the
extra `Inner.handle` function — proving the miscompile is **below MIR**.

## Root cause

A struct that implements a trait carries an 8-byte vtable pointer at offset 0.
Two codegen sites already account for it and agree:

- `StructInit` (`src/compiler_rust/compiler/src/codegen/instr/mod.rs:929-965`)
  allocates `struct_size + 8` and shifts every field offset by +8 when the
  struct name is in `vtable_data_ids`.
- `effective_field_offset` (`.../codegen/instr/mod.rs:322-342`) applies the same
  +8 to every `FieldGet`/`FieldSet`.

**`AggregateCopy` did not.**
`compile_aggregate_copy` / `emit_aggregate_block_copy`
(`.../codegen/instr/closures_structs.rs:508-590`) consumed MIR's *unshifted*
`byte_size` and `word_index` verbatim and never consulted `vtable_data_ids`.

For `Inner` (3 fields, MIR `byte_size: 24`, real allocation 32) the copy
therefore allocated and copied **24 of 32 bytes**: the vtable word plus the first
two fields. The last field (`mgr`) fell outside the copy, so the subsequent
`FieldGet` at effective offset 24 read past the allocation. Because `mgr` is a
**class** (a pointer) the garbage word was dereferenced -> SIGSEGV. Had it been a
scalar the value would simply have been silently wrong.

The nested path had the same defect: `AggregateFieldCopy` (`word_index`,
`byte_size`) is likewise the unshifted layout, and it carried **no type name**,
so codegen could not tell whether a nested field's struct had a vtable.

## Fix

1. `compiler/src/mir/inst_enum.rs` — add `type_name: Option<String>` to
   `AggregateFieldCopy` so codegen can identify a nested field's struct type.
2. `compiler/src/mir/lower/lowering_core.rs:998-1002` — populate it.
3. `compiler/src/codegen/instr/closures_structs.rs` — `compile_aggregate_copy` /
   `emit_aggregate_block_copy` now take the block's `type_name`; when it is in
   `ctx.vtable_data_ids` they use `byte_size + 8` and shift each `word_index`
   by +1. `type_name: None` keeps the previous behaviour exactly, so the
   no-vtable path is unchanged.
4. `compiler/src/codegen/instr/mod.rs`, `codegen/dispatch.rs`,
   `codegen/emitter_trait.rs`, `codegen/cranelift_emitter.rs`,
   `codegen/llvm/emitter.rs`, `codegen/mir_interpreter.rs` — thread `type_name`
   through the emitter trait (it was being dropped by a `..` pattern).
5. `codegen/instr/mod.rs` — corrected the `effective_field_offset` doc comment,
   which claimed the shift is keyed on `vtable_type_ids`; both it and
   `StructInit` actually prefer `vtable_data_ids` (keyed on the collision-free
   struct NAME), with `vtable_type_ids` only as the no-name fallback.

### Known remaining gap (NOT fixed)

`compiler/src/codegen/llvm/functions.rs:886` has its own `AggregateCopy` arm with
the **same truncation defect**. Fixing it needs a name -> vtable lookup that this
backend does not thread into scope. Marked with a `TODO(sj-segv-2026-08-27)`
there. The LLVM lane is unverified for this defect class.

## Verification (worktree `/mnt/data/structfix-1`, own build at `/mnt/data/structfix-target/release/simple`)

```
# minimal reproducer
$ bin/simple run repro/min.spl                       # deployed seed
rc=139
$ /mnt/data/structfix-target/release/simple run repro/min.spl   # fixed
r=5
rc=0
$ SIMPLE_EXECUTION_MODE=interpreter ... run repro/min.spl
r=5
rc=0

# full ablation matrix, fixed binary: all 6 variants JIT rc=0, output == interpreter output

# ORIGINAL pre-workaround sj shape restored (exec_args(client: SjClient), main.spl exec_args(client, argv))
### sj --version
  deployed seed: rc=139 (SIGSEGV)
  fixed        : rc=0   jj --no-pager --color never --version
### sj --help
  deployed seed: rc=0
  fixed        : rc=0
### sj raw jj log -r @ --no-graph -T commit_id
  deployed seed: rc=139 (SIGSEGV)
  fixed        : rc=0   jj --ignore-working-copy --no-pager --color never log -r @ --no-graph -T commit_id
```

The `NOTE(sj-segv-2026-08-27)` workaround in `src/app/sj/client.spl` can be
removed once a fixed seed is deployed. Until then, `SIMPLE_EXECUTION_MODE=interpreter`
is a correct runtime workaround for any affected program.

## Environment findings (incidental, both worth acting on separately)

1. **The shared tree `/home/ormastes/dev/pub/simple` `src/compiler_rust` does not
   compile** — `cargo check --release --bin simple` fails with E0433
   (`crate::read_trace` missing, `compiler/src/hir/lower/import_loader.rs:44`),
   E0425 (`perf_counters::IMPORT_AST_HITS` / `IMPORT_AST_PARSES`,
   `crate::interpreter::probe_source_cached`) and E0609
   (`Lowerer::importer_glob_sources`, `compiler/src/hir/lower/lowerer.rs:790`) —
   8 errors, a half-landed change. This is the failure mode
   `scripts/check/check-seed-builds-push.shs` exists to catch.
2. **The deployed seed is not reproducible from either tree**: the binary
   contains the string literal `hybrid-interp-splice`, which exists in **no**
   `.rs` or `.spl` file in the shared tree or at `f8aeb0caea69`.

## Scope of impact

Any program where a struct that implements a trait is copied by value —
struct-literal init, local binding, parameter passing, field store, return — and
holds a class/actor-typed field. Silent wrong values for scalar fields; SIGSEGV
for reference fields. Interpreter unaffected.

## Unchanged pre-existing gap (NOT this bug, NOT a regression)

`handle_cli_args` (`src/app/sj_daemon/request_handler.spl:49`) **builds and
returns the jj command string; it never executes it.** `plan.commands` are
formatted through `build_command` and joined into `stdout` with `exit_code: 0`.
So `sj` is currently a command *planner*, not a jj wrapper — which is why the
verification transcript above shows `sj --version` printing
`jj --no-pager --color never --version` rather than running it. No
`rt_shell_exec` is reached on this path at all. That is exactly the scope of plan
item **SCV-IMPL-B-02 (jj mutating adapter)** and must not be mistaken for a
regression, nor for this SEGV being unfixed. `.claude/rules/vcs.md` documents
`sj` as the preferred push path; that documentation is ahead of the
implementation at this commit.

## Regression evidence

- **Differential sweep, 45 programs** (`test/01_unit/compiler/dup_struct_name/**`
  + a random sample of `examples/**`), each run three ways — deployed seed (JIT),
  fixed binary (JIT), fixed binary (interpreter) — comparing exit code AND stdout
  on two axes: (a) deployed-seed JIT vs fixed JIT, and (b) fixed JIT vs fixed
  interpreter. Axis (a): **0 regressions**. Axis (b): 2 engine divergences
  (`examples/06_io/restaurant_webapp/services/email_service.spl`,
  `examples/10_tooling/libraries/external_compression/demo.spl`) — both
  **pre-existing and unrelated**, reproducing identically on the deployed seed
  (rc=1 on both binaries) and both caused by an unavailable external bridge whose
  handling differs per engine, not by value layout. One program changed from fail to pass
  (`examples/10_tooling/trace32_tools/cmm_lsp/lsp_server.spl`); on inspection that
  is a flaky 10s example timeout on an interactive stdin-reading server, **not**
  attributable to this fix, and it is recorded as such rather than claimed.
- **`sh scripts/check/check-dup-struct-name-jit-soundness.shs`**: `PASS — 5 case(s)
  checked, JIT never disagrees with the interpreter`. (Note: this gate invokes
  `bin/simple`, i.e. the deployed seed, so it is a no-change baseline here, not a
  test of the fixed binary.)
- Regression fixture added at
  `test/01_unit/compiler/vtable_aggregate_copy/case_trait_struct_nested_class.spl`
  (the minimal reproducer). It is **not yet wired into a check script** — doing so
  needs a gate that runs it under both engines and diffs, in the shape of
  `check-dup-struct-name-jit-soundness.shs`. **Follow-up for whoever lands this.**

- **Ablation matrix re-run on the fixed binary with both engines' stdout
  asserted equal**: all 6 variants `MATCH=True`, `jitout == interpout == 'r=5'`.

### Not verified

- `cargo test -p simple-compiler` **cannot run at this commit**: the lib *test*
  target fails to compile with 2 pre-existing E0433 errors in
  `compiler/src/interpreter/expr/collections.rs:1210,1213` (undeclared
  `CompileError`, unresolved `codes` module) — a file this change does not touch.
  The `--bin simple` build itself is clean. So no Rust unit-test evidence was
  obtainable; the evidence above is all behavioural.
- The LLVM backend lane (see "Known remaining gap").
