use simple_compiler::interpreter;
use simple_parser::Parser;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

fn evaluate_loaded(main_path: &std::path::Path) -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    result.unwrap()
}

fn evaluate_unflattened(main_path: &std::path::Path) -> i32 {
    let source = fs::read_to_string(main_path).unwrap();
    let module = Parser::new(&source).parse().unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    result.unwrap()
}

fn evaluate_unflattened_clean(main_path: &std::path::Path) -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    evaluate_unflattened(main_path)
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
