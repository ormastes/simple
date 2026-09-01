use simple_compiler::interpreter;
use simple_parser::Parser;
use std::collections::HashSet;
use std::fs;
use std::sync::{Mutex, MutexGuard};
use tempfile::tempdir;

/// Serialize all interpreter evaluations in this test binary.
///
/// The interpreter's fault-detection counters (RECURSION_DEPTH,
/// INSTRUCTION_COUNT, TIMEOUT_EXCEEDED) are process-global atomics while the
/// rest of its state is thread-local. Under the default parallel test
/// harness, one test's `clear_interpreter_state()` zeroes the shared
/// recursion depth mid-flight for another test, whose RAII guards then
/// underflow it — every later `push_call_depth` fails as a phantom
/// StackOverflow (the reentrant/vmm in-suite flakes). Holding this lock for
/// the whole clear+evaluate span makes each test's reset-and-run atomic.
static INTERP_TEST_LOCK: Mutex<()> = Mutex::new(());

fn interp_lock() -> MutexGuard<'static, ()> {
    // A panicking test (failed assertion inside an evaluation) poisons the
    // lock; later tests must still run.
    INTERP_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

fn evaluate_loaded(main_path: &std::path::Path) -> i32 {
    let _serial = interp_lock();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    result.unwrap()
}

fn evaluate_unflattened_locked(main_path: &std::path::Path) -> i32 {
    let source = fs::read_to_string(main_path).unwrap();
    let module = Parser::new(&source).parse().unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    result.unwrap()
}

fn evaluate_unflattened(main_path: &std::path::Path) -> i32 {
    let _serial = interp_lock();
    evaluate_unflattened_locked(main_path)
}

fn evaluate_unflattened_clean(main_path: &std::path::Path) -> i32 {
    let _serial = interp_lock();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    evaluate_unflattened_locked(main_path)
}

#[test]
fn imported_functions_share_live_module_globals() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "static mut enabled = false\n\nfn enable():\n    enabled = true\n\nfn read() -> i32:\n    if enabled:\n        return 1\n    return 0\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import state\n\nfn main() -> i32:\n    state.enable()\n    return state.read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_unflattened_clean(&main_path), 1);
}

#[test]
fn nested_write_survives_enclosing_frame_return() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var enabled = false\n\nfn reset():\n    enabled = false\n\nfn enable():\n    enabled = true\n\nfn reset_then_enable():\n    reset()\n    enable()\n\nfn read() -> i32:\n    if enabled:\n        return 1\n    return 0\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import state\n\nfn main() -> i32:\n    state.reset_then_enable()\n    return state.read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_unflattened_clean(&main_path), 1);
}

#[test]
fn inner_write_survives_two_enclosing_frame_returns() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nfn set_value(next: i32):\n    value = next\n\nfn inner():\n    set_value(2)\n\nfn middle():\n    inner()\n\nfn outer() -> i32:\n    value = 1\n    middle()\n    return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import state\n\nfn main() -> i32:\n    return state.outer() * 10 + state.read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_unflattened_clean(&main_path), 22);
}

#[test]
fn reentrant_cross_module_write_survives_enclosing_frame_return() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let bridge_path = dir.path().join("bridge.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "import bridge\n\nvar value = 0\n\nfn inner():\n    value = 2\n\nfn outer() -> i32:\n    value = 1\n    bridge.middle(inner)\n    return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(bridge_path, "fn middle(callback: fn()):\n    callback()\n").unwrap();
    fs::write(
        &main_path,
        "import state\n\nfn main() -> i32:\n    return state.outer() * 10 + state.read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_unflattened_clean(&main_path), 22);
}

#[test]
fn reentrant_callback_refreshes_foreign_imported_array_before_mutation() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let bridge_path = dir.path().join("bridge.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var values: [i32] = []\n\nfn inner():\n    values.push(2)\n\nfn outer(middle: fn(fn())) -> i32:\n    values.clear()\n    values.push(1)\n    middle(inner)\n    return values.len()\n\nfn sum() -> i32:\n    var total = 0\n    for value in values:\n        total = total + value\n    return total\n",
    )
    .unwrap();
    fs::write(
        bridge_path,
        "use state.{values}\n\nfn middle(callback: fn()):\n    callback()\n    values.push(3)\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{outer, sum}\nuse bridge.{middle}\n\nfn main() -> i32:\n    return outer(middle) * 10 + sum()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 36);
}

#[test]
fn ownerless_nested_frame_relays_newer_global_write() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nfn inner():\n    value = 2\n\nfn outer() -> i32:\n    value = 1\n    fn wrapper():\n        inner()\n    wrapper()\n    return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import state\n\nfn main() -> i32:\n    return state.outer() * 10 + state.read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_unflattened_clean(&main_path), 22);
}

#[test]
fn function_parameter_shadow_relays_newer_same_owner_global() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nfn inner():\n    value = 2\n\nfn wrapper(value: i32) -> i32:\n    inner()\n    return value\n\nfn outer() -> i32:\n    value = 1\n    wrapper(9)\n    return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{outer, read}\n\nfn main() -> i32:\n    return outer() * 10 + read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 22);
}

#[test]
fn imported_parallel_arena_reset_updates_defining_owner() {
    let dir = tempdir().unwrap();
    let decls_path = dir.path().join("decls.spl");
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        decls_path,
        "var decl_body: [[i32]] = []\n\nfn seed_old():\n    decl_body.clear()\n    decl_body.push([199])\n\nfn first_index() -> i32:\n    return decl_body[0][0]\n",
    )
    .unwrap();
    fs::write(
        state_path,
        "use decls.{decl_body}\n\nvar stmt_tag: [i32] = []\n\nfn seed_old():\n    stmt_tag.clear()\n    var i = 0\n    while i < 200:\n        stmt_tag.push(i)\n        i = i + 1\n\nfn reset_and_build():\n    stmt_tag.clear()\n    stmt_tag.push(7)\n    decl_body.clear()\n    decl_body.push([0])\n\nfn first_tag() -> i32:\n    return stmt_tag[0]\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import decls\nimport state\n\nfn main() -> i32:\n    decls.seed_old()\n    state.seed_old()\n    state.reset_and_build()\n    return decls.first_index() * 10 + state.first_tag()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 7);
}

#[test]
fn unflattened_transitive_alias_sees_growing_global_array() {
    let dir = tempdir().unwrap();
    let arena_path = dir.path().join("arena.spl");
    let facade_path = dir.path().join("facade.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        arena_path,
        "var values: [i32] = []\n\nfn push_value(value: i32):\n    values.push(value)\n",
    )
    .unwrap();
    fs::write(
        facade_path,
        "use arena.{values as imported_values, push_value}\n\nfn push_then_read(value: i32) -> i32:\n    push_value(value)\n    return imported_values[0]\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import facade\n\nfn main() -> i32:\n    return facade.push_then_read(41)\n",
    )
    .unwrap();

    assert_eq!(evaluate_unflattened_clean(&main_path), 41);
}

#[test]
fn flattened_functions_share_growing_module_global_arrays() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var values: [i32] = []\n\nfn push_value(value: i32):\n    values.push(value)\n\nfn read_value(index: i32) -> i32:\n    return values[index]\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{push_value, read_value}\n\nfn main() -> i32:\n    push_value(17)\n    return read_value(0)\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 17);
}

#[test]
fn flattened_transitive_import_sees_growing_global_array() {
    let dir = tempdir().unwrap();
    let arena_path = dir.path().join("arena.spl");
    let facade_path = dir.path().join("facade.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        arena_path,
        "var values: [i32] = []\n\nfn push_value(value: i32):\n    values.push(value)\n",
    )
    .unwrap();
    fs::write(
        facade_path,
        "use arena.{values, push_value}\n\nfn push_then_read(value: i32) -> i32:\n    push_value(value)\n    return values[0]\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use facade.{push_then_read}\n\nfn main() -> i32:\n    return push_then_read(17)\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 17);
}

#[test]
fn flattened_transitive_alias_sees_growing_global_array() {
    let dir = tempdir().unwrap();
    let arena_path = dir.path().join("arena.spl");
    let facade_path = dir.path().join("facade.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        arena_path,
        "var values: [i32] = []\n\nfn push_value(value: i32):\n    values.push(value)\n",
    )
    .unwrap();
    fs::write(
        facade_path,
        "use arena.{values as imported_values, push_value}\n\nfn push_then_read(value: i32) -> i32:\n    push_value(value)\n    return imported_values[0]\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use facade.{push_then_read}\n\nfn main() -> i32:\n    return push_then_read(31)\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 31);
}

#[test]
fn flattened_same_named_global_arrays_remain_owner_isolated() {
    let dir = tempdir().unwrap();
    let left_path = dir.path().join("left.spl");
    let right_path = dir.path().join("right.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        left_path,
        "var values: [i32] = []\n\nfn push_left(value: i32):\n    values.push(value)\n\nfn read_left(index: i32) -> i32:\n    return values[index]\n",
    )
    .unwrap();
    fs::write(
        right_path,
        "var values: [i32] = []\n\nfn push_right(value: i32):\n    values.push(value)\n\nfn read_right(index: i32) -> i32:\n    return values[index]\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use left.{push_left, read_left}\nuse right.{push_right, read_right}\n\nfn main() -> i32:\n    push_left(11)\n    push_right(22)\n    return read_left(0) * 100 + read_right(0)\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 1122);
}

#[test]
fn nested_local_shadow_reveals_latest_owner_global() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nfn set_value():\n    value = 7\n\nfn shadow_then_update() -> i32:\n    if true:\n        val value = 5\n        set_value()\n    return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import state\n\nfn main() -> i32:\n    return state.shadow_then_update() * 10 + state.read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_unflattened_clean(&main_path), 77);
}

#[test]
fn imported_global_shadow_reveals_latest_defining_owner_value() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let worker_path = dir.path().join("worker.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nfn set_value():\n    value = 7\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        worker_path,
        "use state.{value, set_value}\n\nfn shadow_then_update() -> i32:\n    if true:\n        val value = 5\n        set_value()\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{read}\nuse worker.{shadow_then_update}\n\nfn main() -> i32:\n    return shadow_then_update() * 10 + read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 77);
}

#[test]
fn nested_shadow_preserves_prior_write_and_same_value_nested_write() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nfn set_value(next: i32):\n    value = next\n\nfn assign_then_shadow() -> i32:\n    value = 7\n    if true:\n        val value = 5\n    return value\n\nfn assign_then_same_value_nested() -> i32:\n    value = 7\n    if true:\n        val value = 5\n        set_value(0)\n    return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import state\n\nfn main() -> i32:\n    val first = state.assign_then_shadow()\n    val second = state.assign_then_same_value_nested()\n    return first * 100 + second * 10 + state.read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_unflattened_clean(&main_path), 700);
}

#[test]
fn tuple_shadow_reveals_latest_owner_global() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nfn set_value(next: i32):\n    value = next\n\nfn tuple_shadow_then_update() -> i32:\n    if true:\n        val (value, other) = (5, 6)\n        set_value(8)\n    return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import state\n\nfn main() -> i32:\n    return state.tuple_shadow_then_update() * 10 + state.read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_unflattened_clean(&main_path), 88);
}

#[test]
fn imported_static_method_preserves_module_owner() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nclass Worker:\n    static fn set_value(next: i32) -> i32:\n        value = next\n        return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import state\n\nfn main() -> i32:\n    return state.Worker.set_value(9) * 10 + state.read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_unflattened_clean(&main_path), 99);
}

#[test]
fn flattened_static_method_preserves_module_owner() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nclass Worker:\n    static fn set_value(next: i32) -> i32:\n        value = next\n        return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{Worker, read}\n\nfn main() -> i32:\n    return Worker.set_value(9) * 10 + read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 99);
}

#[test]
fn flattened_instance_method_preserves_module_owner() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nclass Worker:\n    tag: i32\n\n    me set_value(next: i32) -> i32:\n        value = next\n        return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{Worker, read}\n\nfn main() -> i32:\n    var worker = Worker(tag: 0)\n    return worker.set_value(9) * 10 + read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 99);
}

#[test]
fn flattened_context_hooks_preserve_module_owner() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nclass Guard:\n    tag: i32\n\n    fn __enter__() -> i32:\n        value = 7\n        return value\n\n    fn __exit__(exc, detail, trace):\n        if detail == nil and trace == nil:\n            value = 9\n        else:\n            value = 3\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{Guard, read}\n\nfn main() -> i32:\n    var entered = 0\n    with Guard(tag: 0) as value:\n        entered = value\n    return entered * 10 + read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 79);
}

#[test]
fn flattened_lambda_publishes_captured_global_array_mutation() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var values: [i32] = [1]\n\nfn run() -> i32:\n    val append = \\:\n        values.push(7)\n    append()\n    return values.len()\n\nfn read_len() -> i32:\n    return values.len()\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{run, read_len}\n\nfn main() -> i32:\n    return run() * 10 + read_len()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 22);
}

#[test]
fn flattened_lambda_relays_nested_same_owner_write() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nfn inner():\n    value = 2\n\nfn run() -> i32:\n    value = 1\n    val update = \\:\n        inner()\n    update()\n    return value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{run, read}\n\nfn main() -> i32:\n    return run() * 10 + read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 22);
}

#[test]
fn flattened_lambda_return_preserves_global_mutation() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var values: [i32] = []\n\nfn run() -> i32:\n    values.push(1)\n    val append = \\:\n        values.push(7)\n        return values.len()\n    append()\n    return values.len()\n\nfn read_len() -> i32:\n    return values.len()\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{run, read_len}\n\nfn main() -> i32:\n    return run() * 10 + read_len()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 22);
}

#[test]
fn flattened_lambda_local_shadow_does_not_publish_global() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 1\n\nfn run() -> i32:\n    val compute = \\:\n        val value = 7\n        return value\n    return compute() * 10 + value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{run, read}\n\nfn main() -> i32:\n    return run() * 10 + read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 711);
}

#[test]
fn flattened_lambda_nested_shadow_does_not_publish_global() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 1\n\nfn run() -> i32:\n    val compute = \\:\n        if true:\n            val value = 7\n        return value\n    return compute() * 10 + value\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{run, read}\n\nfn main() -> i32:\n    return run() * 10 + read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 111);
}

#[test]
fn selective_cache_retains_module_owner_metadata() {
    let dir = tempdir().unwrap();
    let lib_dir = dir.path().join("src/lib");
    fs::create_dir_all(&lib_dir).unwrap();
    let state_path = lib_dir.join("state.spl");
    let main_path = lib_dir.join("main.spl");
    let read_main_path = lib_dir.join("read_main.spl");
    fs::write(
        state_path,
        "var enabled = false\n\nfn enable():\n    enabled = true\n\nfn read() -> i32:\n    if enabled:\n        return 1\n    return 0\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import state\n\nfn main() -> i32:\n    state.enable()\n    return state.read()\n",
    )
    .unwrap();
    fs::write(
        &read_main_path,
        "import state\n\nfn main() -> i32:\n    return state.read()\n",
    )
    .unwrap();

    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    assert_eq!(evaluate_unflattened(&main_path), 1);
    interpreter::clear_interpreter_state();
    interpreter::clear_module_cache_selective();
    assert_eq!(evaluate_unflattened(&read_main_path), 0);
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
}

#[test]
fn flattened_transitive_import_preserves_global_owner() {
    let dir = tempdir().unwrap();
    let leaf_path = dir.path().join("leaf.spl");
    let facade_path = dir.path().join("facade.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        leaf_path,
        "var value: i32 = 0\n\nfn set_value():\n    value = 7\n\nfn read_value() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        facade_path,
        "use leaf.{set_value, read_value}\n\nfn write_value():\n    set_value()\n\nfn read_through() -> i32:\n    return read_value()\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use facade.{write_value, read_through}\n\nfn main() -> i32:\n    write_value()\n    return read_through()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 7);
}

#[test]
fn flattened_export_use_alias_facade_reads_live_mutable_globals() {
    let dir = tempdir().unwrap();
    let leaf_path = dir.path().join("leaf.spl");
    let facade_path = dir.path().join("facade.spl");
    let consumer_path = dir.path().join("consumer.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        leaf_path,
        "var values: [i32] = []\n\nfn push_value(value: i32):\n    values.push(value)\n",
    )
    .unwrap();
    fs::write(facade_path, "export use leaf.{values as facade_values, push_value}\n").unwrap();
    fs::write(
        consumer_path,
        "use facade.{facade_values, push_value}\n\nfn push_then_read(value: i32) -> i32:\n    push_value(value)\n    return facade_values[0]\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use consumer.{push_then_read}\n\nfn main() -> i32:\n    return push_then_read(41)\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 41);
}

#[test]
fn flattened_export_use_glob_facade_keeps_two_live_global_owners() {
    // Glob marker expansion is intentionally eager: record_flattened_import_binding
    // copies globals/bindings that the source owner has registered already. This
    // proves the supported acyclic flattening order; cyclic re-export facades do
    // not yet have a deferred/fixpoint binding contract and must not be claimed
    // as supported by this regression.
    let dir = tempdir().unwrap();
    let leaf_path = dir.path().join("leaf.spl");
    let facade_path = dir.path().join("facade.spl");
    let consumer_path = dir.path().join("consumer.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        leaf_path,
        "var left: [i32] = []\nvar right: [i32] = []\n\nfn push_both(a: i32, b: i32):\n    left.push(a)\n    right.push(b)\n",
    )
    .unwrap();
    fs::write(facade_path, "export use leaf.*\n").unwrap();
    fs::write(
        consumer_path,
        "use facade.{left, right, push_both}\n\nfn push_then_read(a: i32, b: i32) -> i32:\n    push_both(a, b)\n    return left[0] * 100 + right[0]\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use consumer.{push_then_read}\n\nfn main() -> i32:\n    return push_then_read(12, 3)\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 1203);
}

#[test]
fn flattened_owner_keeps_private_state_across_colliding_helpers() {
    let dir = tempdir().unwrap();
    let core_path = dir.path().join("vmm_core.spl");
    let facade_path = dir.path().join("facade.spl");
    let collision_path = dir.path().join("paging.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        core_path,
        "var fallback_root: u64 = 0\n\nfn _load_root(value: u64):\n    fallback_root = value\n\nfn _read_root() -> u64:\n    return fallback_root\n\nfn init_root(value: u64):\n    _load_root(value)\n\nfn active_root() -> u64:\n    return _read_root()\n",
    )
    .unwrap();
    fs::write(facade_path, "use vmm_core.{init_root, active_root}\n").unwrap();
    fs::write(
        collision_path,
        "fn _load_root(value: u64):\n    val ignored = value\n\nfn _read_root() -> u64:\n    return 0\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import vmm_core\nimport paging\nuse facade.{init_root, active_root}\n\nfn main() -> i32:\n    init_root(123)\n    return active_root().to_i32()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 123);
}

#[test]
fn real_vmm_sparse_init_preserves_active_root() {
    let dir = tempdir().unwrap();
    let main_path = dir.path().join("main.spl");
    fs::write(
        &main_path,
        "use os.kernel.boot.mmio.{mmio_reset_for_test}\nuse os.kernel.memory.pmm.{pmm_init_identity_range, pmm_get_manager}\nuse os.kernel.memory.vmm.{vmm_init_sparse_for_test, vmm_active_root}\n\nfn main() -> i32:\n    mmio_reset_for_test()\n    if not pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024):\n        return 1\n    if not vmm_init_sparse_for_test(pmm_get_manager(), 0):\n        return 2\n    if vmm_active_root() == 0:\n        return 3\n    return 0\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 0);
}

// --- Lambda frame-lifecycle protocol (stage-4 stale-global class) ---
// Lambdas historically bypassed publish/refresh/sync, and selective capture
// (CowEnv::from_map) dropped imported-global owner metadata. Each test below
// fails without exec_lambda routing through the function-frame protocol.

#[test]
fn selective_lambda_capture_preserves_imported_global_owner_on_write() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var values: [i32] = []\n\nfn count() -> i32:\n    return values.len()\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{values, count}\n\nfn main() -> i32:\n    val f = \\x: values.push(x)\n    f(1)\n    f(2)\n    return count()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 2);
}

#[test]
fn lambda_sees_global_written_after_capture() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nfn set_two():\n    value = 2\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{set_two, read, value}\n\nfn main() -> i32:\n    val f = \\x: value + x\n    set_two()\n    return f(10)\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 12);
}

#[test]
fn deeper_global_write_inside_lambda_survives_lambda_return() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(
        state_path,
        "var value = 0\n\nfn set_two():\n    value = 2\n\nfn read() -> i32:\n    return value\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "use state.{set_two, read}\n\nfn main() -> i32:\n    val f = \\x: set_two()\n    f(0)\n    return read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 2);
}

#[test]
fn lambda_parameter_shadowing_global_stays_local() {
    let dir = tempdir().unwrap();
    let state_path = dir.path().join("state.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(state_path, "var value = 0\n\nfn read() -> i32:\n    return value\n").unwrap();
    fs::write(
        &main_path,
        "use state.{read, value}\n\nfn main() -> i32:\n    val f = \\value: value + 1\n    val r = f(41)\n    return r * 10 + read()\n",
    )
    .unwrap();

    assert_eq!(evaluate_loaded(&main_path), 420);
}
