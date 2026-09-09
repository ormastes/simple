//! Executes the actual async owner modules with an injected Vulkan boundary.
//! This proves runtime state/lock/resource behavior, not hardware execution.
//! Run directly with rustc --test --cfg 'feature="vulkan"' --test-threads=1.
extern crate self as ash;
extern crate self as parking_lot;
extern crate self as lazy_static;

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicBool, AtomicI64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Weak};
use std::time::Duration;

pub struct Mutex<T>(std::sync::Mutex<T>);
impl<T> Mutex<T> {
    pub const fn new(value: T) -> Self {
        Self(std::sync::Mutex::new(value))
    }
    pub fn lock(&self) -> std::sync::MutexGuard<'_, T> {
        self.0.lock().unwrap()
    }
}
impl<T: Default> Default for Mutex<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

#[macro_export]
macro_rules! lazy_static {
    ($( $(#[$attr:meta])* $vis:vis static ref $name:ident : $ty:ty = $init:expr; )+) => {
        $( $(#[$attr])* $vis static $name: std::sync::LazyLock<$ty> = std::sync::LazyLock::new(|| $init); )+
    };
}

pub mod vk {
    #[derive(Clone, Copy)]
    pub struct CommandBuffer(pub u64);
    pub trait Handle: Sized {
        fn from_raw(value: u64) -> Self;
        fn as_raw(&self) -> u64;
    }
    impl Handle for CommandBuffer {
        fn from_raw(value: u64) -> Self {
            Self(value)
        }
        fn as_raw(&self) -> u64 {
            self.0
        }
    }
}

pub mod vulkan {
    pub mod device {
        pub enum FencedSubmitError {
            NotSubmitted(&'static str),
            CompletionUnknown(&'static str),
        }
    }
}

mod vulkan_graphics_runtime_core {
    use super::*;
    pub use crate::vk;
    use vk::Handle;

    static NEXT: AtomicI64 = AtomicI64::new(1);
    pub fn alloc_handle() -> i64 {
        NEXT.fetch_add(1, Ordering::Relaxed)
    }

    pub struct Buffer {
        pub drops: Arc<AtomicUsize>,
        pub bytes: u64,
    }
    impl Buffer {
        pub fn size(&self) -> u64 {
            self.bytes
        }
    }
    impl Drop for Buffer {
        fn drop(&mut self) {
            self.drops.fetch_add(1, Ordering::SeqCst);
        }
    }
    #[derive(Default)]
    pub struct ComputeCommandOwners {
        pub buffers: Vec<Arc<Buffer>>,
    }

    pub struct FenceState {
        status: std::sync::Mutex<i64>,
        wake: Condvar,
    }
    pub struct Fence {
        device: Arc<VulkanDevice>,
        state: Arc<FenceState>,
    }
    impl Fence {
        pub fn new(device: Arc<VulkanDevice>, _: bool) -> Result<Self, &'static str> {
            if device.fail_fence.load(Ordering::SeqCst) {
                return Err("fence allocation");
            }
            let state = Arc::new(FenceState {
                status: std::sync::Mutex::new(0),
                wake: Condvar::new(),
            });
            device.fences.lock().push(Arc::downgrade(&state));
            Ok(Self { device, state })
        }
        pub fn is_signaled(&self) -> Result<bool, &'static str> {
            match *self.state.status.lock().unwrap() {
                0 => Ok(false),
                1 => Ok(true),
                _ => Err("device lost"),
            }
        }
        pub fn wait(&self, timeout: u64) -> Result<(), &'static str> {
            if let Some(sender) = self.device.wait_notice.lock().take() {
                sender.send(()).unwrap();
            }
            let status = self.state.status.lock().unwrap();
            let (status, _) = self
                .state
                .wake
                .wait_timeout_while(status, Duration::from_nanos(timeout), |s| *s == 0)
                .unwrap();
            if *status == 1 {
                Ok(())
            } else {
                Err("pending or lost")
            }
        }
    }

    #[derive(Default)]
    pub struct VulkanDevice {
        pub submit_outcome: AtomicI64,
        pub fail_fence: AtomicBool,
        pub idle_fails: AtomicBool,
        pub idle_calls: AtomicUsize,
        pub freed: AtomicUsize,
        live_commands: Mutex<HashSet<u64>>,
        fences: Mutex<Vec<Weak<FenceState>>>,
        pub wait_notice: Mutex<Option<std::sync::mpsc::Sender<()>>>,
    }
    impl VulkanDevice {
        pub fn begin_compute_command(&self) -> Result<vk::CommandBuffer, &'static str> {
            let handle = alloc_handle() as u64;
            assert!(self.live_commands.lock().insert(handle));
            Ok(vk::CommandBuffer(handle))
        }
        pub fn free_compute_command(&self, command: vk::CommandBuffer) {
            assert!(
                self.live_commands.lock().remove(&command.as_raw()),
                "double free or stale command"
            );
            self.freed.fetch_add(1, Ordering::SeqCst);
        }
        pub fn submit_compute_command_no_wait(
            &self,
            command: vk::CommandBuffer,
            _: &Fence,
        ) -> Result<(), vulkan::device::FencedSubmitError> {
            use vulkan::device::FencedSubmitError::*;
            match self.submit_outcome.load(Ordering::SeqCst) {
                1 => {
                    self.free_compute_command(command);
                    Err(NotSubmitted("not accepted"))
                }
                2 => Err(CompletionUnknown("ambiguous acceptance")),
                _ => Ok(()),
            }
        }
        pub fn wait_idle(&self) -> Result<(), &'static str> {
            self.idle_calls.fetch_add(1, Ordering::SeqCst);
            if self.idle_fails.load(Ordering::SeqCst) {
                return Err("device lost");
            }
            self.signal_all();
            Ok(())
        }
        pub fn signal(&self, index: usize, value: i64) {
            let state = self.fences.lock()[index].upgrade().unwrap();
            *state.status.lock().unwrap() = value;
            state.wake.notify_all();
        }
        pub fn signal_all(&self) {
            for state in self.fences.lock().iter().filter_map(Weak::upgrade) {
                *state.status.lock().unwrap() = 1;
                state.wake.notify_all();
            }
        }
    }

    pub struct QuarantinedComputeSubmission {
        pub device: Arc<VulkanDevice>,
        pub fence: Arc<Fence>,
        pub command_buffer: vk::CommandBuffer,
        pub owners: ComputeCommandOwners,
        pub wait_handle: i64,
    }
    #[derive(Default)]
    pub struct VulkanState {
        pub device: Option<Arc<VulkanDevice>>,
        pub compute_commands: HashMap<i64, ComputeCommandOwners>,
        pub quarantined_compute: Vec<QuarantinedComputeSubmission>,
        pub async_compute_session_active: bool,
        pub async_compute_session_fences: HashSet<i64>,
        pub accepted_compute_submit_count: i64,
        pub device_generation_quarantined: bool,
    }
    impl VulkanState {
        pub fn new() -> Self {
            Self::default()
        }
        pub fn require_device(&self) -> Result<Arc<VulkanDevice>, &'static str> {
            if self.device_generation_quarantined {
                return Err("quarantined");
            }
            self.device.clone().ok_or("no device")
        }
        pub fn set_error(&mut self, _: String) {}
        pub fn fence_by_handle(&self, handle: i64) -> Option<&Fence> {
            self.quarantined_compute
                .iter()
                .find(|s| s.wait_handle == handle)
                .map(|s| s.fence.as_ref())
        }
    }
    lazy_static! {
        pub static ref STATE: Mutex<VulkanState> = Mutex::new(VulkanState::new());
    }
}

#[path = "../src/vulkan_graphics_runtime_async.rs"]
mod api;
use api::*;
use vulkan_graphics_runtime_core::*;

static TEST_GATE: Mutex<()> = Mutex::new(());
fn setup(capacity: i64, wait_ns: i64) -> (Arc<VulkanDevice>, i64) {
    let device = Arc::new(VulkanDevice::default());
    *STATE.lock() = VulkanState::new();
    STATE.lock().device = Some(device.clone());
    let session = rt_vulkan_async_session_create_with_wait(capacity, wait_ns);
    assert!(session > 0);
    (device, session)
}
fn submit(session: i64) -> i64 {
    let token = rt_vulkan_async_session_acquire(session);
    assert!(token > 0);
    assert!(rt_vulkan_async_session_command(session, token) > 0);
    assert!(rt_vulkan_async_session_submit(session, token) > 0);
    token
}
fn word(session: i64, index: i64) -> i64 {
    let snapshot = rt_vulkan_async_session_snapshot(session);
    assert!(snapshot > 0);
    rt_vulkan_async_session_snapshot_word(session, snapshot, index)
}
fn finish(device: &VulkanDevice, session: i64, tokens: &[i64]) {
    device.signal_all();
    for token in tokens {
        assert_eq!(rt_vulkan_async_session_poll(session, *token), ASYNC_RETIRED);
        assert_eq!(rt_vulkan_async_session_retire(session, *token), ASYNC_RETIRED);
    }
    assert_eq!(rt_vulkan_async_session_close(session), 1);
    assert_eq!(rt_vulkan_async_session_close(session), 1);
}

#[test]
fn injected_three_submissions_recycle_fourth_without_idle() {
    let _test = TEST_GATE.lock();
    let (device, session) = setup(3, 0);
    let tokens = [submit(session), submit(session), submit(session)];
    assert_eq!(word(session, 8), 3);
    assert_eq!(word(session, 15), 0);
    assert_eq!(rt_vulkan_async_session_acquire(session), ASYNC_WOULD_BLOCK);
    device.signal(0, 1);
    assert_eq!(rt_vulkan_async_session_poll(session, tokens[0]), 1);
    assert_eq!(rt_vulkan_async_session_retire(session, tokens[0]), 1);
    let fourth = submit(session);
    assert_eq!(rt_vulkan_async_session_retire(session, tokens[0]), ASYNC_INVALID);
    finish(&device, session, &[tokens[1], tokens[2], fourth]);
    assert_eq!(device.idle_calls.load(Ordering::SeqCst), 0);
    assert_eq!(device.freed.load(Ordering::SeqCst), 4);
    assert_eq!(word(session, 17), 4);
    assert_eq!(word(session, 4), 0);
}

#[test]
fn injected_wait_keeps_other_poll_and_snapshot_available() {
    let _test = TEST_GATE.lock();
    let (device, session) = setup(3, 1_000_000_000);
    let tokens = [submit(session), submit(session), submit(session)];
    let (sender, receiver) = std::sync::mpsc::channel();
    *device.wait_notice.lock() = Some(sender);
    let waiter = std::thread::spawn(move || rt_vulkan_async_session_acquire(session));
    receiver.recv_timeout(Duration::from_secs(2)).unwrap();
    // These observations must finish BEFORE the one-second waiter can time
    // out. Merely checking them after the wait would miss a held registry lock.
    let (observed, observations) = std::sync::mpsc::channel();
    let observer = std::thread::spawn(move || {
        observed
            .send((
                word(session, 8),
                rt_vulkan_async_session_poll(session, tokens[1]),
                rt_vulkan_async_session_poll(session, tokens[0]),
            ))
            .unwrap();
    });
    assert_eq!(
        observations.recv_timeout(Duration::from_millis(200)).unwrap(),
        (3, ASYNC_PENDING, ASYNC_PENDING)
    );
    device.signal(0, 1);
    observer.join().unwrap();
    assert_eq!(waiter.join().unwrap(), ASYNC_WOULD_BLOCK);
    assert_eq!(word(session, 15), 1);
    finish(&device, session, &tokens);
}

#[test]
fn injected_timeout_retains_exact_command_and_buffer_owners() {
    let _test = TEST_GATE.lock();
    let (device, session) = setup(3, 1);
    let token = rt_vulkan_async_session_acquire(session);
    let command = rt_vulkan_async_session_command(session, token);
    let drops = Arc::new(AtomicUsize::new(0));
    STATE
        .lock()
        .compute_commands
        .get_mut(&command)
        .unwrap()
        .buffers
        .push(Arc::new(Buffer {
            drops: drops.clone(),
            bytes: 256,
        }));
    assert!(rt_vulkan_async_session_submit(session, token) > 0);
    let more = [submit(session), submit(session)];
    assert_eq!(rt_vulkan_async_session_acquire(session), ASYNC_WOULD_BLOCK);
    assert_eq!(rt_vulkan_async_session_retire(session, token), ASYNC_PENDING);
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    assert_eq!(word(session, 19), 256);
    assert_eq!(word(session, 20), 0);
    finish(&device, session, &[token, more[0], more[1]]);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert_eq!(word(session, 20), 256);
}

#[test]
fn injected_rejected_and_ambiguous_submits_have_distinct_lifecycles() {
    let _test = TEST_GATE.lock();
    let (device, session) = setup(3, 0);
    device.submit_outcome.store(1, Ordering::SeqCst);
    let rejected = rt_vulkan_async_session_acquire(session);
    assert_eq!(rt_vulkan_async_session_submit(session, rejected), 0);
    assert_eq!(word(session, 9), 1);
    assert_eq!(rt_vulkan_async_session_command(session, rejected), ASYNC_INVALID);
    assert_eq!(device.freed.load(Ordering::SeqCst), 1);
    device.submit_outcome.store(2, Ordering::SeqCst);
    let unknown = rt_vulkan_async_session_acquire(session);
    assert_eq!(rt_vulkan_async_session_submit(session, unknown), ASYNC_UNKNOWN);
    assert_eq!(rt_vulkan_async_session_poll(session, unknown), ASYNC_UNKNOWN);
    assert_eq!(rt_vulkan_async_session_close(session), ASYNC_UNKNOWN);
    assert_eq!(rt_vulkan_async_session_acquire(session), ASYNC_CLOSED);
    assert_eq!(device.freed.load(Ordering::SeqCst), 1);
    assert_eq!(word(session, 10), 1);
    assert_eq!(rt_vulkan_async_session_recover(session), 1);
    assert_eq!(device.freed.load(Ordering::SeqCst), 2);
    assert_eq!(rt_vulkan_async_session_receipt(session, 1), 0);
    assert_eq!(rt_vulkan_async_session_close(session), 1);
}

#[test]
fn injected_fence_creation_failure_releases_unsubmitted_command_once() {
    let _test = TEST_GATE.lock();
    let (device, session) = setup(8, 0);
    device.fail_fence.store(true, Ordering::SeqCst);
    let token = rt_vulkan_async_session_acquire(session);
    assert_eq!(rt_vulkan_async_session_submit(session, token), 0);
    assert_eq!(device.freed.load(Ordering::SeqCst), 1);
    assert_eq!(rt_vulkan_async_session_in_flight(session), 0);
    assert_eq!(rt_vulkan_async_session_close(session), 1);
}

#[test]
fn injected_cancellation_discards_recordings_but_drains_accepted_work() {
    let _test = TEST_GATE.lock();
    let (device, session) = setup(16, 0);
    let token = submit(session);
    let recording = rt_vulkan_async_session_acquire(session);
    assert!(recording > 0);
    assert_eq!(rt_vulkan_async_session_cancel(session), 1);
    assert_eq!(rt_vulkan_async_session_cancel(session), 1);
    assert_eq!(rt_vulkan_async_session_submit(session, recording), ASYNC_CLOSED);
    assert_eq!(rt_vulkan_async_session_close(session), ASYNC_PENDING);
    assert_eq!(device.freed.load(Ordering::SeqCst), 1);
    assert_eq!(word(session, 18), 1);
    finish(&device, session, &[token]);
    assert_eq!(device.freed.load(Ordering::SeqCst), 2);
}

#[test]
fn injected_snapshots_reject_stale_tokens_and_wrong_sessions() {
    let _test = TEST_GATE.lock();
    let (_, session) = setup(3, 0);
    let first = rt_vulkan_async_session_snapshot(session);
    let second = rt_vulkan_async_session_snapshot(session);
    assert_ne!(first, second);
    assert_eq!(rt_vulkan_async_session_snapshot_word(session, first, 0), ASYNC_INVALID);
    assert_eq!(
        rt_vulkan_async_session_snapshot_word(session + 1000, second, 0),
        ASYNC_INVALID
    );
    assert_eq!(
        rt_vulkan_async_session_snapshot_word(session, second, 64),
        ASYNC_INVALID
    );
    assert_eq!(rt_vulkan_async_session_snapshot_word(session, second, 0), 1);
    assert_eq!(rt_vulkan_async_session_close(session), 1);
    assert_eq!(word(session, 4), 0);
}

#[test]
fn injected_status_failure_can_recover_without_publishing_a_frame() {
    let _test = TEST_GATE.lock();
    let (device, session) = setup(3, 0);
    let token = submit(session);
    device.signal(0, -1);
    assert_eq!(rt_vulkan_async_session_poll(session, token), ASYNC_UNKNOWN);
    assert_eq!(rt_vulkan_async_session_retire(session, token), ASYNC_UNKNOWN);
    assert_eq!(rt_vulkan_async_session_recover(session), 1);
    assert_eq!(rt_vulkan_async_session_receipt(session, 1), 0);
    assert_eq!(word(session, 22), 1);
    assert_eq!(rt_vulkan_async_session_close(session), 1);
}

#[test]
fn z_injected_failed_recovery_quarantines_without_fabricated_release() {
    let _test = TEST_GATE.lock();
    let (device, session) = setup(3, 0);
    let token = submit(session);
    assert_eq!(rt_vulkan_async_session_abandon_device(session), ASYNC_INVALID);
    device.signal(0, -1);
    assert_eq!(rt_vulkan_async_session_poll(session, token), ASYNC_UNKNOWN);
    device.idle_fails.store(true, Ordering::SeqCst);
    assert_eq!(rt_vulkan_async_session_recover(session), ASYNC_UNKNOWN);
    assert_eq!(device.freed.load(Ordering::SeqCst), 0);
    assert_eq!(rt_vulkan_async_session_abandon_device(session), ASYNC_QUARANTINED);
    assert_eq!(device.freed.load(Ordering::SeqCst), 0);
    assert!(STATE.lock().device_generation_quarantined);
    assert_eq!(word(session, 25), 1);
    assert_eq!(word(session, 4), 1);
    assert_eq!(rt_vulkan_async_session_create(3), 0);
    assert_eq!(rt_vulkan_async_session_receipt(session, 1), 0);
}
