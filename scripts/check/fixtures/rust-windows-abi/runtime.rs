//! Runtime crate boundary stays separate from compiler's extern declarations.
#![deny(clashing_extern_declarations)]
mod value { pub mod heap {
    pub fn rt_heap_live_bytes() -> i64 { panic!("heap serialization outside ABI fixture") }
    pub fn rt_heap_peak_bytes() -> i64 { panic!("heap serialization outside ABI fixture") }
} }
#[path="../../../../src/compiler_rust/runtime/src/child_peak_rss.rs"]
mod child_peak_rss;
#[path="../../../../src/compiler_rust/runtime/src/mem_snapshot.rs"]
mod mem_snapshot;
fn main() {
    let (rss,peak)=mem_snapshot::windows_process_memory_kib();
    assert!(rss>0 && peak>=rss);
    child_peak_rss::reset();
    let mut child=std::process::Command::new("cmd.exe").args(["/C", "exit 0"]).spawn().unwrap();
    assert!(child_peak_rss::reap(&mut child,false).unwrap().unwrap().success());
    assert!(child_peak_rss::rt_process_last_child_peak_rss_kib()>0);
    println!("PASS: real runtime process memory and child peak RSS");
}
