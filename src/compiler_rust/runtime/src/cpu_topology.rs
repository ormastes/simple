//! CPU topology + thread pinning for the build-runner fiber scheduler.
//!
//! Rust twin of the C block in `src/runtime/runtime_core_host_services.c`
//! (same symbols, same contract):
//! - `rt_cpu_topology_count()`: logical processors across ALL processor groups
//! - `rt_cpu_topology_field(i, f)`: f = 0 group, 1 number in group (Linux: OS
//!   cpu id), 2 socket/package, 3 NUMA node; -1 when out of range
//! - `rt_thread_pin_current(i)`: pin the calling thread to entry i
//! - `rt_thread_current_cpu()`: `(group << 16) | number`, -1 if unknown
//!
//! Windows hosts with more than 64 logical CPUs have several processor groups;
//! a thread stays in its process's initial group unless assigned explicitly,
//! which is what `rt_thread_pin_current` does (`SetThreadGroupAffinity`).

use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TopoCpu {
    pub group: i64,
    pub number: i64,
    pub socket: i64,
    pub numa: i64,
}

const MAX_CPUS: usize = 1024;

fn topology() -> &'static [TopoCpu] {
    static TOPO: OnceLock<Vec<TopoCpu>> = OnceLock::new();
    TOPO.get_or_init(|| {
        let mut cpus = enumerate();
        cpus.truncate(MAX_CPUS);
        cpus
    })
}

#[cfg(windows)]
mod win {
    #[repr(C)]
    pub struct GroupAffinity {
        pub mask: usize,
        pub group: u16,
        pub reserved: [u16; 3],
    }
    #[repr(C)]
    pub struct ProcessorNumber {
        pub group: u16,
        pub number: u8,
        pub reserved: u8,
    }
    pub const RELATION_NUMA_NODE: i32 = 1;
    pub const RELATION_PROCESSOR_PACKAGE: i32 = 3;
    #[link(name = "kernel32")]
    extern "system" {
        pub fn GetActiveProcessorGroupCount() -> u16;
        pub fn GetActiveProcessorCount(group: u16) -> u32;
        pub fn GetLogicalProcessorInformationEx(relation: i32, buffer: *mut u8, length: *mut u32) -> i32;
        pub fn GetCurrentThread() -> isize;
        pub fn SetThreadGroupAffinity(thread: isize, affinity: *const GroupAffinity, previous: *mut GroupAffinity) -> i32;
        pub fn GetCurrentProcessorNumberEx(number: *mut ProcessorNumber);
    }
}

/// Parse `GetLogicalProcessorInformationEx(relation)` into
/// `(id, [(group, mask)])` records. Layout (x64): header {Relationship u32,
/// Size u32}; PROCESSOR_RELATIONSHIP has GroupCount u16 @30 and GROUP_AFFINITY[]
/// @32; NUMA_NODE_RELATIONSHIP has NodeNumber u32 @8, GroupCount u16 @30
/// (0 on older systems = one mask) and GROUP_AFFINITY[] @32.
#[cfg(windows)]
fn relation_masks(relation: i32) -> Vec<(i64, Vec<(u16, usize)>)> {
    let mut len: u32 = 0;
    unsafe { win::GetLogicalProcessorInformationEx(relation, std::ptr::null_mut(), &mut len) };
    if len == 0 {
        return Vec::new();
    }
    let mut buf = vec![0u8; len as usize];
    if unsafe { win::GetLogicalProcessorInformationEx(relation, buf.as_mut_ptr(), &mut len) } == 0 {
        return Vec::new();
    }
    let read_u16 = |at: usize| u16::from_le_bytes([buf[at], buf[at + 1]]);
    let read_u32 = |at: usize| u32::from_le_bytes([buf[at], buf[at + 1], buf[at + 2], buf[at + 3]]);
    let read_usize = |at: usize| {
        let mut b = [0u8; 8];
        b.copy_from_slice(&buf[at..at + 8]);
        u64::from_le_bytes(b) as usize
    };
    let mut out = Vec::new();
    let mut off = 0usize;
    let mut index = 0i64;
    while off + 32 <= len as usize {
        let size = read_u32(off + 4) as usize;
        if size == 0 {
            break;
        }
        let count = match read_u16(off + 30) {
            0 => 1,
            n => n as usize,
        };
        let id = if relation == win::RELATION_NUMA_NODE { read_u32(off + 8) as i64 } else { index };
        let mut masks = Vec::new();
        for g in 0..count {
            let at = off + 32 + g * 16;
            if at + 16 > off + size {
                break;
            }
            masks.push((read_u16(at + 8), read_usize(at)));
        }
        out.push((id, masks));
        index += 1;
        off += size;
    }
    out
}

#[cfg(windows)]
fn enumerate() -> Vec<TopoCpu> {
    let packages = relation_masks(win::RELATION_PROCESSOR_PACKAGE);
    let nodes = relation_masks(win::RELATION_NUMA_NODE);
    let owner = |records: &[(i64, Vec<(u16, usize)>)], group: u16, number: u32| {
        records
            .iter()
            .find(|(_, masks)| masks.iter().any(|&(g, m)| g == group && number < 64 && (m >> number) & 1 == 1))
            .map(|(id, _)| *id)
            .unwrap_or(0)
    };
    let mut cpus = Vec::new();
    let groups = unsafe { win::GetActiveProcessorGroupCount() };
    for group in 0..groups {
        let count = unsafe { win::GetActiveProcessorCount(group) };
        for number in 0..count {
            cpus.push(TopoCpu {
                group: group as i64,
                number: number as i64,
                socket: owner(&packages, group, number),
                numa: owner(&nodes, group, number),
            });
        }
    }
    cpus
}

#[cfg(not(windows))]
fn enumerate() -> Vec<TopoCpu> {
    let read_int = |path: String| -> Option<i64> { std::fs::read_to_string(path).ok()?.trim().parse().ok() };
    let conf = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let mut configured = 0usize;
    if let Ok(entries) = std::fs::read_dir("/sys/devices/system/cpu") {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().to_string();
            if name.len() > 3 && name.starts_with("cpu") && name[3..].bytes().all(|b| b.is_ascii_digit()) {
                configured += 1;
            }
        }
    }
    let total = configured.max(conf);
    let mut cpus = Vec::new();
    for cpu in 0..total {
        let base = format!("/sys/devices/system/cpu/cpu{cpu}");
        if cpu > 0 && read_int(format!("{base}/online")) == Some(0) {
            continue;
        }
        if configured > 0 && !std::path::Path::new(&base).exists() {
            continue;
        }
        let socket = read_int(format!("{base}/topology/physical_package_id")).unwrap_or(0).max(0);
        let numa = std::fs::read_dir(&base)
            .ok()
            .and_then(|entries| {
                entries.flatten().find_map(|entry| {
                    let name = entry.file_name().to_string_lossy().to_string();
                    name.strip_prefix("node").and_then(|n| n.parse::<i64>().ok())
                })
            })
            .unwrap_or(0);
        cpus.push(TopoCpu { group: 0, number: cpu as i64, socket, numa });
    }
    cpus
}

#[no_mangle]
pub extern "C" fn rt_cpu_topology_count() -> i64 {
    topology().len() as i64
}

#[no_mangle]
pub extern "C" fn rt_cpu_topology_field(index: i64, field: i64) -> i64 {
    let cpus = topology();
    if index < 0 || index as usize >= cpus.len() {
        return -1;
    }
    let cpu = cpus[index as usize];
    match field {
        0 => cpu.group,
        1 => cpu.number,
        2 => cpu.socket,
        3 => cpu.numa,
        _ => -1,
    }
}

#[no_mangle]
pub extern "C" fn rt_thread_pin_current(index: i64) -> bool {
    let cpus = topology();
    if index < 0 || index as usize >= cpus.len() {
        return false;
    }
    let cpu = cpus[index as usize];
    #[cfg(windows)]
    {
        if cpu.number >= 64 {
            return false;
        }
        let affinity = win::GroupAffinity { mask: 1usize << cpu.number, group: cpu.group as u16, reserved: [0; 3] };
        unsafe { win::SetThreadGroupAffinity(win::GetCurrentThread(), &affinity, std::ptr::null_mut()) != 0 }
    }
    #[cfg(target_os = "linux")]
    {
        unsafe {
            let mut set: libc::cpu_set_t = std::mem::zeroed();
            libc::CPU_SET(cpu.number as usize, &mut set);
            libc::sched_setaffinity(0, std::mem::size_of::<libc::cpu_set_t>(), &set) == 0
        }
    }
    #[cfg(not(any(windows, target_os = "linux")))]
    {
        let _ = cpu;
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_thread_current_cpu() -> i64 {
    #[cfg(windows)]
    {
        let mut pn = win::ProcessorNumber { group: 0, number: 0, reserved: 0 };
        unsafe { win::GetCurrentProcessorNumberEx(&mut pn) };
        ((pn.group as i64) << 16) | pn.number as i64
    }
    #[cfg(target_os = "linux")]
    {
        let cpu = unsafe { libc::sched_getcpu() };
        if cpu < 0 {
            -1
        } else {
            cpu as i64
        }
    }
    #[cfg(not(any(windows, target_os = "linux")))]
    {
        -1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn topology_is_non_empty_and_fields_in_range() {
        let n = rt_cpu_topology_count();
        assert!(n >= 1);
        for i in 0..n {
            assert!(rt_cpu_topology_field(i, 0) >= 0);
            assert!(rt_cpu_topology_field(i, 1) >= 0);
        }
        assert_eq!(rt_cpu_topology_field(n, 0), -1);
        assert_eq!(rt_cpu_topology_field(0, 9), -1);
    }
}
