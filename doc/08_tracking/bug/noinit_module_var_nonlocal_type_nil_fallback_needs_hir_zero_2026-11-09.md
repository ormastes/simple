# No-initializer module var of class/enum/imported/later-declared type still defaults to nil

- **Date:** 2026-11-09
- **Status:** open
- **Parent:** p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20 (PR #7871)

The flat parser zero-initializes `var g: S` and `[S; N]` only when `S` is a
struct declared EARLIER in the same module (it needs the field list). Class,
enum, imported, and later-declared types keep the nil-until-assignment fallback,
which conflicts with the owner decision (module var without initializer ->
zero/default; nil only in unsafe).

Fix needs type information, so it belongs in a HIR pass: after name resolution,
synthesize the zero value (recursive field zero, error naming the field when a
field has no safe zero) for any initializer-less module var, then drop the
parser nil fallback in `struct_zero_expr_v1` callers (parser_stmts.spl,
parser_decls_use.spl).

## 2026-11-09 kernel/noalloc gap (PR #7871 review)
Zero struct-literal init is disabled for sources whose path contains `/os/`, `noalloc` or `baremetal`
(driver `set_noinit_kernel_module_v1`): those modules keep the nil zero-BSS global, e.g.
`src/os/kernel/interrupts/gdt.spl` `var tss: TssEntry`. A struct literal there could need runtime
init/heap before the allocator exists, and no native objdump/boot gate could be run on this host to
show a static-zero landing. Open: prove static-zero emission (or an HIR zero pass) then lift the gate.

## 2026-11-09 fix (owner decision item 14) — status fix-implemented-verification-pending

Owner decision: compiler (robust/compile path) requires an explicit initializer —
already enforced by `noinit_robust_mode_v1` (`parser_decls_use.spl`), now pinned for
enum and class vars; the INTERPRETER defaults an initializer-less enum var to its
FIRST variant and a class var to its default construction with undefaulted fields
zero-filled (0 / false / 0.0 / "" / [] / nested enum first variant / nested class).

- Seed interpreter (`src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs`
  `noinit_named_type_default`, wired in `interpreter/node_exec.rs` and
  `interpreter_module/module_evaluator/evaluation_helpers.rs`): covers same-module,
  later-declared and imported class/enum types. Before: the name was never bound
  (`variable `light` not found`).
- Flat parser (`parser_stmts.spl` `struct_zero_expr_v1`): enum declared earlier ->
  `E.First` (payload-carrying first variant = parse error), `text` fields -> `""`,
  enum/class fields recurse. Imported / later-declared types still return the -2
  nil fallback in the flat parser (needs the HIR pass described above) — the seed
  interpreter covers them at run time.
- Red/green: `test/01_unit/compiler/interp/module_noinit_class_enum_default_spec.spl`
  0/5 on the deployed seed -> 5/5 on the rebuilt seed;
  `test/01_unit/compiler/parser/module_noinit_enum_class_zero_spec.spl` 1/4 -> 4/4.
- Kernel/noalloc gate (`set_noinit_kernel_module_v1`) unchanged.

## 2026-11-09 fix (later-declared types) — superseded
An earlier fix deferred no-init named variables until the end of the module,
zero-initializing later-declared structs and defaulting classes and enums. The
owner decision below supersedes that behavior and removes the deferred pass.

## Fix 2026-11-09 (owner decision item 14) — fix-implemented-verification-pending
No HIR zero pass: the compiler (flat parser) now reports `explicit initializer required for module-level
var '<name>'` for a no-init module var of class or enum type (all modes), and for any named type it
cannot zero (imported, later-declared, `any`, and every named type in kernel/noalloc modules). The nil
fallback is gone. A struct declared earlier still zero-initializes (item 8); robust mode still rejects
every no-init var. The seed interpreter keeps its first-variant / default-construction default (#7965).
Classes are recognised through a `classdecl:<name>|` marker in the parser's ENUM_ATTRIBUTES pool.
src/ site given an explicit initializer: `src/os/kernel/interrupts/gdt.spl` (`tss`, `gdt_pointer`).
Not changed: fixed-size ARRAYS of an unzeroable named element in kernel/noalloc modules keep the
zero-BSS nil slots (`riscv/startup.spl`, `riscv32/startup.spl` `trap_frames`); native static-zero
proof is deferred to stage3 verification.

## 2026-11-10 P2 triage (lane p2-compiler-triage-20261110)

VERDICT: SUPERSEDED on compiler(simple). Commit 0e9cf3282498 is an ancestor of
release/1.0.0 d7a430cc2baf; parser_decls_use.spl:459-474 rejects no-init
class/enum/unzeroable named module vars ("explicit initializer required"),
nil fallback gone. Qualified on the deployed seed (seed-smoke):
test/01_unit/compiler/parser/module_noinit_enum_class_zero_spec.spl 7/7 PASS.
The interp spec is 0/5 on the deployed seed, matching this document's recorded
"0/5 deployed -> 5/5 rebuilt" red/green; seed source carries the fix
(6109d315b22e, class_instantiation.rs:570), so interp qualification belongs to
the seed-fix lane (src/compiler_rust, out of scope here). Kernel/noalloc
static-zero proof remains deferred per this document. Cycles: 1. Evidence:
build/review/p2fix-compiler-20261110.sdn.

## 2026-11-12 fix (lane fable-bug-noinitvar-20261112) — the last nil residue was the fixed-array path

Different class than the title: no HIR zero pass is needed (owner item 14 superseded it) and
both existing specs were already green on the fresh seed (parser 7/7, interp 5/5). The one
live residue was `fixed_array_no_init_default_expr` (`parser_stmts.spl`): for a module var
`var g: [T; N]` whose element `T` is imported, later-declared, a class (classes register as
`DECL_STRUCT`, so `struct_zero_expr_v1` zero-filled them), or any named type under the
kernel/noalloc gate, it returned `expr_array_repeat(expr_nil_lit(0), N)` — a nil array in
safe code, with a stale comment still citing the retired item-8 nil contract.

- Fix: the helper reports `explicit initializer required for fixed-size array of <T>` and
  returns -1; both callers (`parser_decls_use.spl` module path, `var_no_init_default_expr`
  local path) stop on -1 without a second generic error. The module path additionally
  rejects a class element via `parser_is_class_decl_v1`, mirroring the bare-var check.
  An earlier-declared struct element still zero-fills with one literal per slot.
- Red/green: `test/01_unit/compiler/parser/module_noinit_enum_class_zero_spec.spl` new
  scenario (imported / later-declared / class / kernel-mode struct element arrays) 7/8 ->
  8/8; `module_noinit_zero_default_spec.spl` k2 flipped from pinning the nil slots to
  requiring the initializer, 15/15. `module_noinit_named_nil_parity_spec.spl` is 8/9 both
  before and after (the MIR `parse_full_frontend` zero-lowering harness issue, unrelated).
- src/ sites: the only two module-level `[Named; N]` no-init declarations were the unused
  `trap_frames` in `baremetal/riscv/startup.spl` and `riscv32/startup.spl` (zero references
  anywhere; struct declared after the var) — deleted. Both files' flat-parser first error is
  unchanged before/after (line 40/60 `[u8; STACK_SIZE * 4]`, non-literal size; pre-existing).
- Still deferred, unchanged: native static-zero proof for kernel BSS globals (item 14 keeps
  the explicit-initializer rule there instead).
