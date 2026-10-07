//! Bootstrap extern metrics must report real process memory, in KiB.
#![cfg(target_os = "linux")]
use simple_compiler::interpreter;
use simple_parser::Parser;

#[test]
fn registered_memory_metrics_observe_resident_allocation() {
    let mut memory = vec![0u8; 64 * 1024 * 1024];
    for page in memory.chunks_mut(4096) { page[0] = 1; }
    std::hint::black_box(&memory);
    let source = "extern fn rt_process_rss_kib() -> i64\nextern fn rt_process_hwm_kib() -> i64\nval rss = rt_process_rss_kib()\nval peak = rt_process_hwm_kib()\nmain = if rss >= 65536 and peak >= rss: 0 else: 1\n";
    let module = Parser::new(source).parse().unwrap();
    assert_eq!(interpreter::evaluate_module(&module.items).unwrap(), 0);
    std::hint::black_box(memory);
}
