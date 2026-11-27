// A packed `[u32]` (the 1M-word Vulkan font atlas) must not be expanded to a
// boxed `Vec<Value>` view (~80 bytes per element, ~80 MB for 1M words) just
// because it is passed to an extern that only READS it, or because a short
// slice is taken from it. Measured on seed1126b: one
// `rt_vulkan_copy_to_buffer_u32(0, atlas, 0)` call raised peak RSS 106 -> 186 MB,
// and 64K-word slices of it 106 -> 178 MB.
//
// One #[test] on purpose: `ARRAY_MATERIALIZE_ELEMS` is process-wide, and the
// test harness runs tests of one binary on parallel threads.
use simple_compiler::interpreter;
use simple_compiler::value::ARRAY_MATERIALIZE_ELEMS;
use simple_parser::Parser;
use std::sync::atomic::Ordering;

fn run(source: &str) -> (i64, u64) {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{source}\nmain = main()\n");
    let module = Parser::new(&source).parse().expect("source must parse");
    let before = ARRAY_MATERIALIZE_ELEMS.load(Ordering::Relaxed);
    let rc = interpreter::evaluate_module(&module.items).expect("source must run") as i64;
    (rc, ARRAY_MATERIALIZE_ELEMS.load(Ordering::Relaxed) - before)
}

const SLICE: &str = r#"
fn main() -> i64:
    val atlas: [u32] = [7u32; 1048576]
    val s = atlas[10:20]
    if s.len() != 10: return 1
    if s[0] != 7u32: return 2
    val tail = atlas[1048570:1048580]
    if tail.len() != 6: return 3
    if atlas[5] != 7u32: return 4
    0
"#;

const EXTERN: &str = r#"
@unsafe(reason: "test: typed word upload marshaller", capabilities: [ffi])
extern fn rt_vulkan_copy_to_buffer_u32(handle: i64, words: [u32], offset: i64) -> bool

@unsafe(reason: "test calls the raw extern", capabilities: [ffi])
fn upload(px: [u32]) -> bool:
    rt_vulkan_copy_to_buffer_u32(0, px, 0)

fn main() -> i64:
    var atlas: [u32] = [7u32; 1048576]
    # handle 0: the extern converts its words, then declines without a device.
    if upload(atlas): return 1
    if atlas.len() != 1048576: return 2
    if atlas[1048575] != 7u32: return 3
    # The array stays a normal mutable value after the extern read it.
    atlas[5] = 9u32
    if atlas[5] != 9u32: return 4
    if atlas[6] != 7u32: return 5
    val s = atlas[4:7]
    if s[1] != 9u32: return 6
    0
"#;

#[test]
fn packed_array_is_not_materialized_by_slice_or_read_only_extern() {
    let (rc, slice_elems) = run(SLICE);
    assert_eq!(rc, 0, "slice program result");
    let (rc, extern_elems) = run(EXTERN);
    assert_eq!(rc, 0, "extern program result");
    eprintln!("materialized elements: slice={slice_elems} extern={extern_elems}");
    assert_eq!(
        (slice_elems, extern_elems),
        (0, 0),
        "packed 1M-word array was materialized (boxed elements: slice, extern)"
    );
}
