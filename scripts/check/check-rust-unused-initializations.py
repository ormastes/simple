#!/usr/bin/env python3
"""Compile production retry/layer snippets with deterministic effect adapters.
No Cargo build or product qualification. Tests exact edited production regions.
"""
import argparse
from pathlib import Path
import subprocess
ap = argparse.ArgumentParser()
ap.add_argument('--output', required=True)
ap.add_argument('--rustc', default='rustc')
a = ap.parse_args()
root = Path(__file__).resolve().parents[2]
out = Path(a.output).resolve()
out.mkdir(parents=True, exist_ok=True)
file_io = (root/'src/compiler_rust/compiler/src/interpreter_extern/file_io.rs').read_text()
owner = file_io[file_io.index('pub fn rt_hosted_safe_artifact_read_v1('):]
start = owner.index('        let mut used = 0usize;')
end = owner.index('        let mut after:', start)
retry = owner[start:end].replace('std::io::Error::last_os_error().raw_os_error()', 'fixture_errno()')
assert retry.count('let mut retries = 0;') == 1
instance = (root/'src/compiler_rust/runtime/src/vulkan/instance.rs').read_text()
start = instance.index('        // Enable validation layers in debug builds')
end = instance.index('        // Required extensions', start)
layers = instance[start:end]
pre = r"""
use std::ffi::CString;
use std::ffi::CStr;
use std::os::raw::c_char;
use std::collections::VecDeque;
use std::sync::Mutex;
#[derive(Clone)] enum Step { Interrupt, Data(Vec<u8>), Eof }
static STEPS: Mutex<VecDeque<Step>> = Mutex::new(VecDeque::new());
static READS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static TEST_SERIAL: Mutex<()> = Mutex::new(());
fn fixture_errno() -> Option<i32> { Some(libc::EINTR) }
mod libc {
    pub const EINTR: i32 = 4;
    pub unsafe fn read(_fd: i32, p: *mut u8, n: usize) -> isize {
        super::READS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        match super::STEPS.lock().unwrap().pop_front().expect("unexpected read") {
            super::Step::Interrupt => -1,
            super::Step::Eof => 0,
            super::Step::Data(bytes) => {
                assert!(bytes.len() <= n);
                unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), p, bytes.len()); }
                bytes.len() as isize
            }
        }
    }
}
fn read_fixture(wanted: usize, mut ok: bool, steps: Vec<Step>) -> (bool, Vec<u8>, usize, usize) {
    let _guard = TEST_SERIAL.lock().unwrap();
    *STEPS.lock().unwrap() = steps.into();
    READS.store(0, std::sync::atomic::Ordering::Relaxed);
    let fd = 1;
    let mut bytes = vec![0u8; wanted];
"""
mid = r"""
    (ok, bytes, used, READS.load(std::sync::atomic::Ordering::Relaxed))
}
#[cfg(debug_assertions)] struct LayerProperty { layer_name: [c_char; 256] }
#[cfg(debug_assertions)] struct FakeEntry { available: bool }
#[cfg(debug_assertions)] impl FakeEntry {
    unsafe fn enumerate_instance_layer_properties(&self) -> Result<Vec<LayerProperty>, ()> {
        let mut name = [0; 256];
        for (dst, src) in name.iter_mut().zip(b"VK_LAYER_KHRONOS_validation") { *dst = *src as c_char; }
        Ok(if self.available { vec![LayerProperty {layer_name: name}] } else {vec![]})
    }
}
fn validation_layers(_available: bool) -> Vec<String> {
    #[cfg(debug_assertions)] let entry = FakeEntry {available: _available};
"""
end = r"""
    #[cfg(debug_assertions)] if !layer_names.is_empty() {
        assert_eq!(layer_names[0], layer_names_raw[0].as_ptr());
    }
    // This represents vkCreateInstance consuming the pointer array while the
    // CString storage is still alive; no storage read is added in release.
    layer_names.iter().map(|p| unsafe { CStr::from_ptr(*p) }.to_string_lossy().into_owned()).collect()
}
#[test] fn short_reads_reset_interrupt_budget() {
    let mut steps = vec![Step::Interrupt; 31];
    steps.push(Step::Data(vec![7,8]));
    steps.extend(vec![Step::Interrupt; 31]);
    steps.push(Step::Data(vec![9]));
    assert_eq!(read_fixture(3, true, steps), (true, vec![7,8,9], 3, 64));
}
#[test] fn interrupt_limit_and_eof_stop() {
    assert_eq!(read_fixture(1, true, vec![Step::Interrupt;32]), (false, vec![0], 0, 32));
    assert_eq!(read_fixture(2, true, vec![Step::Data(vec![5]),Step::Eof]), (false,vec![5,0],1,2));
}
#[test] fn disabled_or_empty_reads_have_no_effects() {
    assert_eq!(read_fixture(0, true, vec![]), (true, vec![], 0, 0));
    assert_eq!(read_fixture(1, false, vec![]), (false, vec![0], 0, 0));
}
#[test] fn validation_pointer_storage_remains_live() {
    let names = validation_layers(true);
    #[cfg(debug_assertions)] assert_eq!(names, ["VK_LAYER_KHRONOS_validation"]);
    #[cfg(not(debug_assertions))] assert!(names.is_empty());
    assert!(validation_layers(false).is_empty());
}
"""
fixture = out/'unused-production.rs'
fixture.write_text(pre + retry + mid + layers + end)
for debug in ['yes','no']:
    exe = out/('unused-'+debug+'.exe')
    subprocess.run([a.rustc,'--edition=2021','--test','-Dwarnings','-C','debug-assertions='+debug,
        str(fixture),'-o',str(exe)],check=True)
    subprocess.run([str(exe)],check=True)
# Former integer initialization must trigger the precise warning being fixed.
negative = out/'unused-retries-negative.rs'
old_retry = '        let mut retries = 0;\n'+retry.replace('let mut retries = 0;', 'retries = 0;', 1)
negative.write_text(pre + old_retry + mid + layers + end)
r = subprocess.run([a.rustc,'--edition=2021','--test','-Dunused_assignments',str(negative),
    '-o',str(out/'negative.exe')],capture_output=True,text=True)
(out/'unused-retries-negative.log').write_text(r.stdout+r.stderr)
assert r.returncode != 0 and 'value assigned to `retries` is never read' in r.stderr, r.stderr
print('former retry initialization warning negative control: PASS')
