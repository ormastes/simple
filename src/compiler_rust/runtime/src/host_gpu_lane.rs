//! Host/GPU lane marker runtime bridge.
//!
//! The compiler lowers Pure Simple `target.later() gpu|host \:` blocks to
//! MIR begin/end markers. These functions are the low-cost runtime boundary
//! consumed by interpreter, bytecode, and native codegen. Backend-specific
//! queue submitters attach below this boundary.

use std::collections::VecDeque;
use std::ffi::{c_char, CStr};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Mutex, OnceLock};

pub const RT_HOST_GPU_LANE_HOST: i64 = 1;
pub const RT_HOST_GPU_LANE_GPU: i64 = 2;

pub const RT_HOST_GPU_PHASE_BEGIN: i64 = 1;
pub const RT_HOST_GPU_PHASE_END: i64 = 2;

pub const RT_HOST_GPU_QUEUE_STATUS_EMPTY: i64 = 0;
pub const RT_HOST_GPU_QUEUE_STATUS_QUEUED: i64 = 1;
pub const RT_HOST_GPU_QUEUE_STATUS_SUBMITTED: i64 = 2;
pub const RT_HOST_GPU_QUEUE_STATUS_COMPLETED: i64 = 3;
pub const RT_HOST_GPU_QUEUE_STATUS_UNAVAILABLE: i64 = 4;
pub const RT_HOST_GPU_QUEUE_CAPACITY: usize = 1024;

static EVENT_COUNT: AtomicI64 = AtomicI64::new(0);
static BEGIN_COUNT: AtomicI64 = AtomicI64::new(0);
static END_COUNT: AtomicI64 = AtomicI64::new(0);
static LAST_LANE: AtomicI64 = AtomicI64::new(0);
static LAST_PHASE: AtomicI64 = AtomicI64::new(0);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostGpuQueuePacket {
    pub id: i64,
    pub lane_code: i64,
    pub kind_code: i64,
    pub payload_size: i64,
    pub backend_handle: i64,
    pub payload_hash: i64,
    pub payload_text: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostGpuQueueReceipt {
    pub packet_id: i64,
    pub status_code: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostGpuQueueDrain {
    pub drained_count: i64,
    pub last_status_code: i64,
}

#[derive(Debug)]
struct HostGpuQueueState {
    next_packet_id: i64,
    packets: VecDeque<HostGpuQueuePacket>,
    in_flight: VecDeque<HostGpuQueuePacket>,
    packet_count: i64,
    submitted_count: i64,
    completed_count: i64,
    last_status: i64,
    last_backend_handle: i64,
    last_payload_size: i64,
    last_payload_hash: i64,
    last_payload_text: String,
    last_device_time_us: i64,
}

impl HostGpuQueueState {
    fn new() -> Self {
        Self {
            next_packet_id: 1,
            packets: VecDeque::new(),
            in_flight: VecDeque::new(),
            packet_count: 0,
            submitted_count: 0,
            completed_count: 0,
            last_status: RT_HOST_GPU_QUEUE_STATUS_EMPTY,
            last_backend_handle: 0,
            last_payload_size: 0,
            last_payload_hash: 0,
            last_payload_text: String::new(),
            last_device_time_us: 0,
        }
    }

    fn reset(&mut self) {
        *self = Self::new();
    }
}

static QUEUE_STATE: OnceLock<Mutex<HostGpuQueueState>> = OnceLock::new();
static LAST_PAYLOAD_TEXT_C: Mutex<[u8; 4096]> = Mutex::new([0; 4096]);

fn queue_state() -> &'static Mutex<HostGpuQueueState> {
    QUEUE_STATE.get_or_init(|| Mutex::new(HostGpuQueueState::new()))
}

#[inline]
fn valid_lane(lane_code: i64) -> bool {
    lane_code == RT_HOST_GPU_LANE_HOST || lane_code == RT_HOST_GPU_LANE_GPU
}

#[inline]
fn valid_phase(phase_code: i64) -> bool {
    phase_code == RT_HOST_GPU_PHASE_BEGIN || phase_code == RT_HOST_GPU_PHASE_END
}

pub fn record_host_gpu_lane_event(lane_code: i64, phase_code: i64) -> i64 {
    if !valid_lane(lane_code) || !valid_phase(phase_code) {
        return 0;
    }

    EVENT_COUNT.fetch_add(1, Ordering::Relaxed);
    if phase_code == RT_HOST_GPU_PHASE_BEGIN {
        BEGIN_COUNT.fetch_add(1, Ordering::Relaxed);
    } else {
        END_COUNT.fetch_add(1, Ordering::Relaxed);
    }
    LAST_LANE.store(lane_code, Ordering::Relaxed);
    LAST_PHASE.store(phase_code, Ordering::Relaxed);
    1
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_lane_event(lane_code: i64, phase_code: i64) -> i64 {
    record_host_gpu_lane_event(lane_code, phase_code)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_lane_reset() {
    EVENT_COUNT.store(0, Ordering::Relaxed);
    BEGIN_COUNT.store(0, Ordering::Relaxed);
    END_COUNT.store(0, Ordering::Relaxed);
    LAST_LANE.store(0, Ordering::Relaxed);
    LAST_PHASE.store(0, Ordering::Relaxed);
    rt_host_gpu_queue_reset();
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_lane_event_count() -> i64 {
    EVENT_COUNT.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_lane_begin_count() -> i64 {
    BEGIN_COUNT.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_lane_end_count() -> i64 {
    END_COUNT.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_lane_last_lane() -> i64 {
    LAST_LANE.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_lane_last_phase() -> i64 {
    LAST_PHASE.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_reset() {
    if let Ok(mut state) = queue_state().lock() {
        state.reset();
    }
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_emit(
    lane_code: i64,
    kind_code: i64,
    payload_size: i64,
    backend_handle: i64,
) -> i64 {
    rt_host_gpu_queue_emit_payload_text(lane_code, kind_code, payload_size, backend_handle, 0, "")
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_emit_payload(
    lane_code: i64,
    kind_code: i64,
    payload_size: i64,
    backend_handle: i64,
    payload_hash: i64,
) -> i64 {
    rt_host_gpu_queue_emit_payload_text(lane_code, kind_code, payload_size, backend_handle, payload_hash, "")
}

pub fn rt_host_gpu_queue_emit_payload_text(
    lane_code: i64,
    kind_code: i64,
    payload_size: i64,
    backend_handle: i64,
    payload_hash: i64,
    payload_text: &str,
) -> i64 {
    if !valid_lane(lane_code) || kind_code < 0 || payload_size < 0 || backend_handle < 0 {
        return 0;
    }

    let Ok(mut state) = queue_state().lock() else {
        return 0;
    };
    if state.packets.len() + state.in_flight.len() >= RT_HOST_GPU_QUEUE_CAPACITY {
        return 0;
    }
    let packet_id = state.next_packet_id;
    state.next_packet_id += 1;
    state.packet_count += 1;
    state.last_status = RT_HOST_GPU_QUEUE_STATUS_QUEUED;
    state.packets.push_back(HostGpuQueuePacket {
        id: packet_id,
        lane_code,
        kind_code,
        payload_size,
        backend_handle,
        payload_hash,
        payload_text: payload_text.to_string(),
    });
    packet_id
}

#[export_name = "rt_host_gpu_queue_emit_payload_text"]
pub unsafe extern "C" fn rt_host_gpu_queue_emit_payload_text_c(
    lane_code: i64,
    kind_code: i64,
    payload_size: i64,
    backend_handle: i64,
    payload_hash: i64,
    payload_text: *const c_char,
) -> i64 {
    let payload_text = if payload_text.is_null() {
        ""
    } else {
        unsafe { CStr::from_ptr(payload_text) }.to_str().unwrap_or("")
    };
    rt_host_gpu_queue_emit_payload_text(
        lane_code,
        kind_code,
        payload_size,
        backend_handle,
        payload_hash,
        payload_text,
    )
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_submit(max_packets: i64) -> i64 {
    if max_packets <= 0 {
        return 0;
    }
    let Ok(mut state) = queue_state().lock() else {
        return 0;
    };

    let mut submitted = 0;
    while submitted < max_packets {
        let Some(packet) = state.packets.pop_front() else {
            break;
        };
        state.submitted_count += 1;
        state.last_status = RT_HOST_GPU_QUEUE_STATUS_SUBMITTED;
        state.last_backend_handle = packet.backend_handle;
        state.in_flight.push_back(packet);
        submitted += 1;
    }
    submitted
}

fn complete_packet(state: &mut HostGpuQueueState, packet: HostGpuQueuePacket) {
    state.completed_count += 1;
    state.last_backend_handle = packet.backend_handle;
    state.last_payload_size = packet.payload_size;
    state.last_payload_hash = packet.payload_hash;
    state.last_payload_text = packet.payload_text.clone();
    state.last_status = if packet.lane_code == RT_HOST_GPU_LANE_GPU && packet.backend_handle == 0 {
        RT_HOST_GPU_QUEUE_STATUS_UNAVAILABLE
    } else {
        RT_HOST_GPU_QUEUE_STATUS_COMPLETED
    };
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_complete(max_packets: i64) -> i64 {
    if max_packets <= 0 {
        return 0;
    }
    let Ok(mut state) = queue_state().lock() else {
        return 0;
    };

    let mut completed = 0;
    while completed < max_packets {
        let Some(packet) = state.in_flight.pop_front() else {
            break;
        };
        complete_packet(&mut state, packet);
        completed += 1;
    }
    completed
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_drain(max_packets: i64) -> i64 {
    if max_packets <= 0 {
        return 0;
    }
    let Ok(mut state) = queue_state().lock() else {
        return 0;
    };

    let mut drained = 0;
    while drained < max_packets {
        if let Some(packet) = state.in_flight.pop_front() {
            complete_packet(&mut state, packet);
            drained += 1;
            continue;
        }
        let Some(packet) = state.packets.pop_front() else {
            break;
        };
        state.submitted_count += 1;
        state.last_status = RT_HOST_GPU_QUEUE_STATUS_SUBMITTED;
        complete_packet(&mut state, packet);
        drained += 1;
    }
    drained
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_packet_count() -> i64 {
    queue_state().lock().map(|state| state.packet_count).unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_submitted_count() -> i64 {
    queue_state().lock().map(|state| state.submitted_count).unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_completed_count() -> i64 {
    queue_state().lock().map(|state| state.completed_count).unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_in_flight_count() -> i64 {
    queue_state()
        .lock()
        .map(|state| state.in_flight.len() as i64)
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_last_status() -> i64 {
    queue_state()
        .lock()
        .map(|state| state.last_status)
        .unwrap_or(RT_HOST_GPU_QUEUE_STATUS_EMPTY)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_last_backend_handle() -> i64 {
    queue_state().lock().map(|state| state.last_backend_handle).unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_last_payload_size() -> i64 {
    queue_state().lock().map(|state| state.last_payload_size).unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_last_payload_hash() -> i64 {
    queue_state().lock().map(|state| state.last_payload_hash).unwrap_or(0)
}

pub fn rt_host_gpu_queue_last_payload_text() -> String {
    queue_state()
        .lock()
        .map(|state| state.last_payload_text.clone())
        .unwrap_or_default()
}

#[export_name = "rt_host_gpu_queue_last_payload_text"]
pub extern "C" fn rt_host_gpu_queue_last_payload_text_c() -> *const c_char {
    let text = rt_host_gpu_queue_last_payload_text();
    let Ok(mut buffer) = LAST_PAYLOAD_TEXT_C.lock() else {
        return std::ptr::null();
    };
    buffer.fill(0);
    let bytes = text.as_bytes();
    let len = bytes.len().min(buffer.len() - 1);
    buffer[..len].copy_from_slice(&bytes[..len]);
    buffer.as_ptr().cast()
}

#[no_mangle]
pub extern "C" fn rt_host_gpu_queue_last_device_time_us() -> i64 {
    queue_state().lock().map(|state| state.last_device_time_us).unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn records_valid_lane_begin_and_end_events() {
        rt_host_gpu_lane_reset();

        assert_eq!(rt_host_gpu_lane_event(RT_HOST_GPU_LANE_GPU, RT_HOST_GPU_PHASE_BEGIN), 1);
        assert_eq!(rt_host_gpu_lane_event(RT_HOST_GPU_LANE_GPU, RT_HOST_GPU_PHASE_END), 1);

        assert_eq!(rt_host_gpu_lane_event_count(), 2);
        assert_eq!(rt_host_gpu_lane_begin_count(), 1);
        assert_eq!(rt_host_gpu_lane_end_count(), 1);
        assert_eq!(rt_host_gpu_lane_last_lane(), RT_HOST_GPU_LANE_GPU);
        assert_eq!(rt_host_gpu_lane_last_phase(), RT_HOST_GPU_PHASE_END);
    }

    #[test]
    fn emits_and_drains_gpu_queue_packets_with_typed_unavailable_status() {
        rt_host_gpu_lane_reset();

        let packet_id = rt_host_gpu_queue_emit(RT_HOST_GPU_LANE_GPU, 1, 256, 0);
        assert_eq!(packet_id, 1);
        assert_eq!(rt_host_gpu_queue_packet_count(), 1);
        assert_eq!(rt_host_gpu_queue_last_status(), RT_HOST_GPU_QUEUE_STATUS_QUEUED);

        assert_eq!(rt_host_gpu_queue_drain(1), 1);
        assert_eq!(rt_host_gpu_queue_submitted_count(), 1);
        assert_eq!(rt_host_gpu_queue_completed_count(), 1);
        assert_eq!(rt_host_gpu_queue_last_status(), RT_HOST_GPU_QUEUE_STATUS_UNAVAILABLE);
        assert_eq!(rt_host_gpu_queue_last_backend_handle(), 0);
    }

    #[test]
    fn carries_runtime_backend_handle_through_submitted_packet() {
        rt_host_gpu_lane_reset();

        let packet_id = rt_host_gpu_queue_emit(RT_HOST_GPU_LANE_GPU, 1, 512, 7);
        assert_eq!(packet_id, 1);
        assert_eq!(rt_host_gpu_queue_last_backend_handle(), 0);

        assert_eq!(rt_host_gpu_queue_drain(1), 1);
        assert_eq!(rt_host_gpu_queue_submitted_count(), 1);
        assert_eq!(rt_host_gpu_queue_completed_count(), 1);
        assert_eq!(rt_host_gpu_queue_last_status(), RT_HOST_GPU_QUEUE_STATUS_COMPLETED);
        assert_eq!(rt_host_gpu_queue_last_backend_handle(), 7);
    }

    #[test]
    fn c_payload_bridge_preserves_text_and_numeric_metadata() {
        rt_host_gpu_lane_reset();
        let payload = std::ffi::CString::new("draw-text").unwrap();

        let packet_id =
            unsafe { rt_host_gpu_queue_emit_payload_text_c(RT_HOST_GPU_LANE_GPU, 2, 9, 7, 42, payload.as_ptr()) };
        assert_eq!(packet_id, 1);
        assert_eq!(rt_host_gpu_queue_drain(1), 1);
        assert_eq!(rt_host_gpu_queue_last_payload_size(), 9);
        assert_eq!(rt_host_gpu_queue_last_payload_hash(), 42);
        let text = unsafe { CStr::from_ptr(rt_host_gpu_queue_last_payload_text_c()) };
        assert_eq!(text.to_str().unwrap(), "draw-text");
    }

    #[test]
    fn submit_phase_leaves_packet_observably_in_flight_until_complete() {
        rt_host_gpu_lane_reset();

        let packet_id = rt_host_gpu_queue_emit(RT_HOST_GPU_LANE_GPU, 1, 512, 7);
        assert_eq!(packet_id, 1);
        assert_eq!(rt_host_gpu_queue_last_status(), RT_HOST_GPU_QUEUE_STATUS_QUEUED);

        assert_eq!(rt_host_gpu_queue_submit(1), 1);
        assert_eq!(rt_host_gpu_queue_submitted_count(), 1);
        assert_eq!(rt_host_gpu_queue_completed_count(), 0);
        assert_eq!(rt_host_gpu_queue_in_flight_count(), 1);
        assert_eq!(rt_host_gpu_queue_last_status(), RT_HOST_GPU_QUEUE_STATUS_SUBMITTED);
        assert_eq!(rt_host_gpu_queue_last_backend_handle(), 7);

        assert_eq!(rt_host_gpu_queue_complete(1), 1);
        assert_eq!(rt_host_gpu_queue_completed_count(), 1);
        assert_eq!(rt_host_gpu_queue_in_flight_count(), 0);
        assert_eq!(rt_host_gpu_queue_last_status(), RT_HOST_GPU_QUEUE_STATUS_COMPLETED);
        assert_eq!(rt_host_gpu_queue_last_backend_handle(), 7);
    }

    #[test]
    fn rejects_queue_emits_past_capacity_like_c_runtime() {
        rt_host_gpu_lane_reset();

        for expected_id in 1..=RT_HOST_GPU_QUEUE_CAPACITY as i64 {
            assert_eq!(rt_host_gpu_queue_emit(RT_HOST_GPU_LANE_GPU, 1, 8, 1), expected_id);
        }
        assert_eq!(rt_host_gpu_queue_emit(RT_HOST_GPU_LANE_GPU, 1, 8, 1), 0);
        assert_eq!(rt_host_gpu_queue_packet_count(), RT_HOST_GPU_QUEUE_CAPACITY as i64);

        assert_eq!(
            rt_host_gpu_queue_drain(RT_HOST_GPU_QUEUE_CAPACITY as i64),
            RT_HOST_GPU_QUEUE_CAPACITY as i64
        );
        assert_eq!(
            rt_host_gpu_queue_emit(RT_HOST_GPU_LANE_GPU, 1, 8, 1),
            RT_HOST_GPU_QUEUE_CAPACITY as i64 + 1
        );
    }

    #[test]
    fn rejects_invalid_lane_or_phase_without_mutating_counters() {
        rt_host_gpu_lane_reset();

        assert_eq!(rt_host_gpu_lane_event(99, RT_HOST_GPU_PHASE_BEGIN), 0);
        assert_eq!(rt_host_gpu_lane_event(RT_HOST_GPU_LANE_HOST, 99), 0);

        assert_eq!(rt_host_gpu_lane_event_count(), 0);
        assert_eq!(rt_host_gpu_lane_begin_count(), 0);
        assert_eq!(rt_host_gpu_lane_end_count(), 0);
        assert_eq!(rt_host_gpu_lane_last_lane(), 0);
        assert_eq!(rt_host_gpu_lane_last_phase(), 0);
    }
}
