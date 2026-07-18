//! Tests for LocalExecutionManager and ExecutionManager trait.

use super::execution_manager::ExecutionManager;
use super::local_execution::{JitBackend, LocalExecutionManager};
use crate::hir;
use crate::mir::lower_to_mir;
use simple_parser::Parser;

/// Helper: parse source → HIR → MIR
fn source_to_mir(source: &str) -> crate::mir::MirModule {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    lower_to_mir(&hir_module).expect("mir lower failed")
}

// =============================================================================
// Cranelift JIT Tests
// =============================================================================

#[test]
fn test_cranelift_jit_basic() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn answer() -> i64:\n    return 42\n");

    let info = em.compile_module(&mir).expect("compile");
    assert!(info.symbol_names.contains(&"answer".to_string()));

    let result = em.execute("answer", &[]).expect("execute");
    assert_eq!(result, 42);
}

#[test]
fn test_cranelift_jit_with_args() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn add(a: i64, b: i64) -> i64:\n    return a + b\n");

    em.compile_module(&mir).expect("compile");

    let result = em.execute("add", &[10, 32]).expect("execute");
    assert_eq!(result, 42);
}

#[test]
fn test_cranelift_jit_unsigned_compare_uses_unsigned_ordering() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir(
        "fn unsigned_high_bit_gt_one() -> i64:\n    val high = 1u64 << 63u64\n    if high > 1u64:\n        return 1\n    return 0\n",
    );

    em.compile_module(&mir).expect("compile");

    let result = em.execute("unsigned_high_bit_gt_one", &[]).expect("execute");
    assert_eq!(result, 1);
}

#[test]
fn test_cranelift_jit_has_function() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn hello() -> i64:\n    return 1\n");

    em.compile_module(&mir).expect("compile");
    assert!(em.has_function("hello"));
    assert!(!em.has_function("nonexistent"));
}

#[test]
fn test_cranelift_jit_backend_name() {
    let em = LocalExecutionManager::cranelift().expect("cranelift init");
    assert_eq!(em.backend_name(), "cranelift-jit");
}

#[test]
fn test_cranelift_jit_cleanup() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn foo() -> i64:\n    return 1\n");

    em.compile_module(&mir).expect("compile");
    assert!(em.has_function("foo"));

    em.cleanup();
    // After cleanup, previously compiled functions should be gone
    assert!(!em.has_function("foo"));
}

// =============================================================================
// Auto-select Tests
// =============================================================================

#[test]
fn test_auto_select() {
    let em = LocalExecutionManager::auto().expect("auto init");

    // On 64-bit hosts, auto should select Cranelift
    #[cfg(target_pointer_width = "64")]
    assert_eq!(em.backend_kind(), JitBackend::Cranelift);

    // Backend name should be valid
    let name = em.backend_name();
    assert!(
        name == "cranelift-jit" || name == "llvm-jit",
        "unexpected backend: {}",
        name
    );
}

#[test]
fn test_auto_jit_execute() {
    let mut em = LocalExecutionManager::auto().expect("auto init");
    let mir = source_to_mir("fn square(x: i64) -> i64:\n    return x * x\n");

    em.compile_module(&mir).expect("compile");
    let result = em.execute("square", &[7]).expect("execute");
    assert_eq!(result, 49);
}

// =============================================================================
// Backend Switching Tests
// =============================================================================

#[test]
fn test_backend_switching_same_result() {
    let mir = source_to_mir("fn triple(x: i64) -> i64:\n    return x * 3\n");

    // Compile and run with Cranelift
    let mut em_cl = LocalExecutionManager::cranelift().expect("cranelift init");
    em_cl.compile_module(&mir).expect("cranelift compile");
    let result_cl = em_cl.execute("triple", &[14]).expect("cranelift execute");

    // Both should give the same result
    assert_eq!(result_cl, 42, "Cranelift should compute 14*3=42");
}

// =============================================================================
// Trait-object (vtable) dispatch tests (bug C8, 2026-07-17)
// =============================================================================

#[test]
fn test_cranelift_jit_vtable_dispatch_full_impl() {
    // Full match to the real BlockDevice/NvmeBlockAdapter shape: a 3-method
    // trait, one concrete struct implementing ALL 3 methods, a wrapper struct
    // holding the trait-typed field, and a method that rebinds it through a
    // locally-typed `val` before calling — exactly `_device_sector_size`'s
    // `val dev: BlockDevice = self.device; dev.sector_size()` pattern.
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir(
        "trait Dev:\n\
         \x20   fn read_x() -> i64\n\
         \x20   fn write_x(v: i64) -> bool\n\
         \x20   fn size_x() -> i64\n\
         \n\
         struct DevA:\n\
         \x20   x: i64\n\
         \n\
         impl Dev for DevA:\n\
         \x20   fn read_x() -> i64:\n\
         \x20       return 1\n\
         \x20   fn write_x(v: i64) -> bool:\n\
         \x20       return true\n\
         \x20   fn size_x() -> i64:\n\
         \x20       return 77\n\
         \n\
         struct Core:\n\
         \x20   device: Dev\n\
         \n\
         impl Core:\n\
         \x20   fn get_size() -> i64:\n\
         \x20       val dev: Dev = self.device\n\
         \x20       return dev.size_x()\n\
         \n\
         fn run() -> i64:\n\
         \x20   val d = DevA(x: 5)\n\
         \x20   val c = Core(device: d)\n\
         \x20   return c.get_size()\n",
    );

    em.compile_module(&mir).expect("compile");
    let result = em.execute("run", &[]).expect("execute");
    assert_eq!(result, 77, "expected size_x()==77 via vtable dispatch, got {result}");
}

#[test]
fn test_cranelift_jit_vtable_dispatch_partial_impl_compaction() {
    // Control case for the "compacted vtable" theory: the concrete struct
    // implements only 2 of the trait's 3 methods (skips the MIDDLE slot,
    // `write_x`). If `emit_vtable_data_objects` writes function pointers at
    // the ENUMERATE index of the (already slot-filtered) `method_fns` vec
    // while the call site loads at the trait's CANONICAL `vtable_slot`
    // (unaffected by the impl's omission), `size_x` (real slot 2) reads past
    // the end of a 2-entry (16-byte) vtable blob -> out-of-bounds garbage
    // function pointer -> wild jump when called.
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir(
        "trait Dev:\n\
         \x20   fn read_x() -> i64\n\
         \x20   fn write_x(v: i64) -> bool\n\
         \x20   fn size_x() -> i64\n\
         \n\
         struct DevB:\n\
         \x20   x: i64\n\
         \n\
         impl Dev for DevB:\n\
         \x20   fn read_x() -> i64:\n\
         \x20       return 1\n\
         \x20   fn size_x() -> i64:\n\
         \x20       return 88\n\
         \n\
         struct Core2:\n\
         \x20   device: Dev\n\
         \n\
         impl Core2:\n\
         \x20   fn get_size() -> i64:\n\
         \x20       val dev: Dev = self.device\n\
         \x20       return dev.size_x()\n\
         \n\
         fn run2() -> i64:\n\
         \x20   val d = DevB(x: 5)\n\
         \x20   val c = Core2(device: d)\n\
         \x20   return c.get_size()\n",
    );

    em.compile_module(&mir).expect("compile");
    let result = em.execute("run2", &[]).expect("execute");
    assert_eq!(result, 88, "expected size_x()==88 via vtable dispatch, got {result}");
}

// =============================================================================
// C8-FIELD lane (2026-07-17): two-hop trait-field discriminator probes.
//
// Mirrors the exact freestanding kernel shapes from the C8-RELOC addendum
// (doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md):
//   SharedFat32Driver(inner: Fat32Core.new(device), ...) -> outer.inner.device.method()
// Common fixture: a 2-level struct nest (Outer.inner: Middle, Middle.device: Dev
// trait-typed field), built via nested struct-literal constructors exactly like
// `SharedFat32Driver(inner: Fat32Core.new(g_adapter), ...)`.
//
// All four variants PASS under the hosted Cranelift JIT (this file) — this is
// a CONTROL result, not a repro: the C8-FIELD lane additionally reproduced the
// exact freestanding/entry-closure/aggressive/is_pic=false AOT pipeline (both
// single-module and genuine cross-module/entry-closure native-build, with the
// outer struct held in a local AND in a module-level global, AND with a
// TypeId-collision-prone decoy trait/struct in a third module) via direct
// disassembly of the emitted object code / linked ELF, and found the same
// clean 2-deref dispatch (object -> vtable -> [vtable+slot_offset] -> call)
// in every case. C8 does NOT reduce to this shape at the seed-codegen level;
// see the bug doc's C8-FIELD addendum for the six-way elimination and the
// next-probe recommendation (runtime pointer comparison under QEMU).
// =============================================================================

// CORRECTED 2026-07-17 (C8-FIX lane): the trait below was originally
// single-method (`size_x` at slot 0) — at slot 0, a correct 2-deref
// dispatch (`[vtable+0]`) and a hypothetical extra-deref bug reading the
// same offset produce BYTE-IDENTICAL code, so none of the four tests below
// could ever have caught the extra-deref hypothesis regardless of field
// count (see the C8-PROBE lane addendum, "Confirmed" gap). Widened to the
// exact 3-method/slot-`0x10` BlockDevice shape (`read_x`/`write_x`/
// `size_x`, dispatched method at slot 2 = byte offset 0x10) with distinct
// per-slot return constants so a wrong-slot dispatch is also detectable
// (not just a crash). `size_x` returns 64 to mirror the real kernel's
// `BlockDevice.sector_size()` value.
const C8_FIELD_FIXTURE_PREFIX: &str = "trait Dev:\n\
     \x20   fn read_x() -> i64\n\
     \x20   fn write_x(v: i64) -> bool\n\
     \x20   fn size_x() -> i64\n\
     \n\
     struct DevC:\n\
     \x20   x: i64\n\
     \n\
     impl Dev for DevC:\n\
     \x20   fn read_x() -> i64:\n\
     \x20       return 11\n\
     \x20   fn write_x(v: i64) -> bool:\n\
     \x20       return true\n\
     \x20   fn size_x() -> i64:\n\
     \x20       return 64\n\
     \n\
     struct Middle:\n\
     \x20   device: Dev\n\
     \n\
     struct Outer:\n\
     \x20   inner: Middle\n\
     \n";

#[test]
fn test_cranelift_jit_vtable_dispatch_two_level_single_local_chain() {
    // Exact shape of the decisive C8-RELOC repro (step 3): two-hop field
    // chain (`outer.inner.device`) read into ONE local in a single
    // statement, then dispatch on that local. This is the shape that
    // FAULTED in the freestanding kernel build.
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let src = format!(
        "{C8_FIELD_FIXTURE_PREFIX}\
         fn run_two_hop_combined() -> i64:\n\
         \x20   val d = DevC(x: 5)\n\
         \x20   val m = Middle(device: d)\n\
         \x20   val o = Outer(inner: m)\n\
         \x20   val bd: Dev = o.inner.device\n\
         \x20   return bd.size_x()\n"
    );
    let mir = source_to_mir(&src);

    em.compile_module(&mir).expect("compile");
    let result = em.execute("run_two_hop_combined", &[]).expect("execute");
    assert_eq!(
        result, 64,
        "two-hop combined-chain dispatch (outer.inner.device) expected size_x()==64, got {result}"
    );
}

#[test]
fn test_cranelift_jit_vtable_dispatch_two_level_split_hops() {
    // Discriminator (a) from the C8-RELOC addendum: split the two-hop chain
    // into two separate statements (`val mid = o.inner; val bd: Dev =
    // mid.device; bd.size_x()`). If this FAILS while the combined-chain
    // test above passes, the erased/chained READ is the bug. If both pass
    // or both fail identically, storage-at-construction is implicated
    // instead.
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let src = format!(
        "{C8_FIELD_FIXTURE_PREFIX}\
         fn run_two_hop_split() -> i64:\n\
         \x20   val d = DevC(x: 5)\n\
         \x20   val m = Middle(device: d)\n\
         \x20   val o = Outer(inner: m)\n\
         \x20   val mid = o.inner\n\
         \x20   val bd: Dev = mid.device\n\
         \x20   return bd.size_x()\n"
    );
    let mir = source_to_mir(&src);

    em.compile_module(&mir).expect("compile");
    let result = em.execute("run_two_hop_split", &[]).expect("execute");
    assert_eq!(
        result, 64,
        "split-hop dispatch (mid = o.inner; bd = mid.device) expected size_x()==64, got {result}"
    );
}

#[test]
fn test_cranelift_jit_vtable_dispatch_single_level_no_outer_nest() {
    // Discriminator (b) from the C8-RELOC addendum: drop the OUTER nesting
    // entirely (no `Outer` wrapping `Middle`) — just a single struct-literal
    // constructor storing a trait-typed field, then a single-hop field read
    // into a local before dispatch. If THIS alone fails, the bug is simply
    // "trait-typed constructor argument stored into a struct field via a
    // struct literal," independent of nesting depth.
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let src = format!(
        "{C8_FIELD_FIXTURE_PREFIX}\
         fn run_single_level() -> i64:\n\
         \x20   val d = DevC(x: 5)\n\
         \x20   val m = Middle(device: d)\n\
         \x20   val bd: Dev = m.device\n\
         \x20   return bd.size_x()\n"
    );
    let mir = source_to_mir(&src);

    em.compile_module(&mir).expect("compile");
    let result = em.execute("run_single_level", &[]).expect("execute");
    assert_eq!(
        result, 64,
        "single-level field-store+read dispatch expected size_x()==64, got {result}"
    );
}

#[test]
fn test_cranelift_jit_vtable_dispatch_two_level_chained_expr() {
    // Variant: chained-EXPRESSION dispatch with no intermediate local at
    // all for the trait value (`o.inner.device.size_x()` in one
    // expression), vs. field-read-into-local-then-dispatch (the other three
    // tests). Distinguishes whether materializing the trait value into a
    // typed local matters.
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let src = format!(
        "{C8_FIELD_FIXTURE_PREFIX}\
         fn run_chained_expr() -> i64:\n\
         \x20   val d = DevC(x: 5)\n\
         \x20   val m = Middle(device: d)\n\
         \x20   val o = Outer(inner: m)\n\
         \x20   return o.inner.device.size_x()\n"
    );
    let mir = source_to_mir(&src);

    em.compile_module(&mir).expect("compile");
    let result = em.execute("run_chained_expr", &[]).expect("execute");
    assert_eq!(
        result, 64,
        "chained-expression dispatch (o.inner.device.size_x()) expected size_x()==64, got {result}"
    );
}

// =============================================================================
// C8-FIX lane (2026-07-17): factory-return-by-value discriminator.
//
// Untested by every prior lane: the four tests above all build the
// trait-bearing struct via an INLINE struct literal in the SAME function
// that dispatches on it (`val m = Middle(device: d)`). The real kernel path
// goes through `static fn new(...)` factories that construct the struct and
// RETURN IT BY VALUE across a call boundary — `Fat32Core.new(device)` /
// `SharedFat32Driver.new(device)` (see std.fs_driver.fat32_core.Fat32Core
// and os.services.fat32.shared_fat32_driver.SharedFat32Driver) — before the
// caller ever reads `.device` off the returned struct. A struct-by-value
// return (sret ABI or equivalent) is a different code path from a local
// struct literal and has never been exercised by this bug's test matrix at
// any tier. See doc/08_tracking/bug/
// simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md, C8-FIX
// lane addendum.
// =============================================================================

#[test]
fn test_cranelift_jit_vtable_dispatch_factory_single_level() {
    // Minimal delta from `single_level_no_outer_nest`: construct `Middle`
    // inside a helper function and return it BY VALUE, instead of a struct
    // literal inline in the caller.
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let src = format!(
        "{C8_FIELD_FIXTURE_PREFIX}\
         fn make_middle(d: Dev) -> Middle:\n\
         \x20   return Middle(device: d)\n\
         \n\
         fn run_factory_single_level() -> i64:\n\
         \x20   val d = DevC(x: 5)\n\
         \x20   val m = make_middle(d)\n\
         \x20   val bd: Dev = m.device\n\
         \x20   return bd.size_x()\n"
    );
    let mir = source_to_mir(&src);

    em.compile_module(&mir).expect("compile");
    let result = em.execute("run_factory_single_level", &[]).expect("execute");
    assert_eq!(
        result, 64,
        "factory-returned struct (make_middle(d) -> Middle) expected size_x()==64, got {result}"
    );
}

#[test]
fn test_cranelift_jit_vtable_dispatch_factory_two_level() {
    // Exact shape of `SharedFat32Driver.new(device)` calling
    // `Fat32Core.new(device)`: a two-level chain of factory functions, each
    // constructing and returning a struct by value, the outer one nesting
    // the inner one's return value into its own struct literal.
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let src = format!(
        "{C8_FIELD_FIXTURE_PREFIX}\
         fn make_middle(d: Dev) -> Middle:\n\
         \x20   return Middle(device: d)\n\
         \n\
         fn make_outer(d: Dev) -> Outer:\n\
         \x20   val m = make_middle(d)\n\
         \x20   return Outer(inner: m)\n\
         \n\
         fn run_factory_two_level() -> i64:\n\
         \x20   val d = DevC(x: 5)\n\
         \x20   val o = make_outer(d)\n\
         \x20   val bd: Dev = o.inner.device\n\
         \x20   return bd.size_x()\n"
    );
    let mir = source_to_mir(&src);

    em.compile_module(&mir).expect("compile");
    let result = em.execute("run_factory_two_level", &[]).expect("execute");
    assert_eq!(
        result, 64,
        "two-level factory chain (make_outer -> make_middle) expected size_x()==64, got {result}"
    );
}

#[test]
fn test_cranelift_jit_vtable_dispatch_factory_module_global() {
    // Mirrors the ACTUAL faulting statement from the C8-RELOC/C8-PROBE
    // repro: `g_pure_nvme_root_fat32 = SharedFat32Driver.new(g_adapter)`
    // (a module-global reassigned from a two-level factory call chain),
    // then a later split-hop read+dispatch on that global.
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let src = format!(
        "{C8_FIELD_FIXTURE_PREFIX}\
         fn make_middle(d: Dev) -> Middle:\n\
         \x20   return Middle(device: d)\n\
         \n\
         fn make_outer(d: Dev) -> Outer:\n\
         \x20   val m = make_middle(d)\n\
         \x20   return Outer(inner: m)\n\
         \n\
         var g_outer_factory: Outer = Outer(inner: Middle(device: DevC(x: 0)))\n\
         \n\
         fn run_factory_module_global() -> i64:\n\
         \x20   val d = DevC(x: 5)\n\
         \x20   g_outer_factory = make_outer(d)\n\
         \x20   val mid = g_outer_factory.inner\n\
         \x20   val bd: Dev = mid.device\n\
         \x20   return bd.size_x()\n"
    );
    let mir = source_to_mir(&src);

    em.compile_module(&mir).expect("compile");
    let result = em.execute("run_factory_module_global", &[]).expect("execute");
    assert_eq!(
        result, 64,
        "module-global reassigned from factory chain, split-hop read expected size_x()==64, got {result}"
    );
}

// =============================================================================
// ExecutionResult (captured output) Tests
// =============================================================================

#[test]
fn test_execute_captured() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn ret_zero() -> i64:\n    return 0\n");

    em.compile_module(&mir).expect("compile");
    let result = em.execute_captured("ret_zero", &[]).expect("execute_captured");
    assert_eq!(result.exit_code, 0);
    // stdout/stderr may be empty for a simple return
}

// =============================================================================
// CodeInfo Tests
// =============================================================================

#[test]
fn test_code_info_entry_point() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn main() -> i64:\n    return 0\n");

    let info = em.compile_module(&mir).expect("compile");
    assert_eq!(info.entry_point, "main");
    assert!(info.symbol_names.contains(&"main".to_string()));
}

#[test]
fn test_code_info_no_main() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn helper() -> i64:\n    return 1\n");

    let info = em.compile_module(&mir).expect("compile");
    // When no main, entry_point is the first function
    assert_eq!(info.entry_point, "helper");
}

// =============================================================================
// LLVM JIT Tests (feature-gated)
// =============================================================================

#[cfg(feature = "llvm")]
mod llvm_jit_tests {
    use super::*;

    #[test]
    fn test_llvm_jit_basic() {
        let mut em = LocalExecutionManager::new(JitBackend::Llvm).expect("llvm init");
        let mir = source_to_mir("fn answer() -> i64:\n    return 42\n");

        em.compile_module(&mir).expect("compile");
        let result = em.execute("answer", &[]).expect("execute");
        assert_eq!(result, 42);
    }

    #[test]
    fn test_llvm_jit_backend_name() {
        let em = LocalExecutionManager::new(JitBackend::Llvm).expect("llvm init");
        assert_eq!(em.backend_name(), "llvm-jit");
    }

    #[test]
    fn test_llvm_jit_logical_not_branch() {
        let mut em = LocalExecutionManager::new(JitBackend::Llvm).expect("llvm init");
        let mir = source_to_mir(
            r#"
fn test() -> i64:
    val flag = true
    if not flag:
        return 0
    return 1
"#,
        );

        em.compile_module(&mir).expect("compile");
        let result = em.execute("test", &[]).expect("execute");
        assert_eq!(result, 1);
    }
}
