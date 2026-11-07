// Architecture ABI declarations only; implementation and qualification required.
const _: () = assert!(core::mem::size_of::<usize>() == 8);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1Deadline {
    pub version: u64,
    pub size: u64,
    pub clock_tag: u64,
    pub expires_ms: i64,
}
const _: () = assert!(core::mem::size_of::<Oiv1Deadline>() == 32);
const _: () = assert!(core::mem::align_of::<Oiv1Deadline>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1Deadline, version) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1Deadline, size) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1Deadline, clock_tag) == 16);
const _: () = assert!(core::mem::offset_of!(Oiv1Deadline, expires_ms) == 24);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1ConstSpan {
    pub data: *const u8,
    pub len: u64,
}
const _: () = assert!(core::mem::size_of::<Oiv1ConstSpan>() == 16);
const _: () = assert!(core::mem::align_of::<Oiv1ConstSpan>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1ConstSpan, data) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1ConstSpan, len) == 8);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1MutableSpan {
    pub data: *mut u8,
    pub capacity: u64,
}
const _: () = assert!(core::mem::size_of::<Oiv1MutableSpan>() == 16);
const _: () = assert!(core::mem::align_of::<Oiv1MutableSpan>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1MutableSpan, data) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1MutableSpan, capacity) == 8);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1Argv {
    pub data: *const Oiv1ConstSpan,
    pub count: u64,
}
const _: () = assert!(core::mem::size_of::<Oiv1Argv>() == 16);
const _: () = assert!(core::mem::align_of::<Oiv1Argv>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1Argv, data) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1Argv, count) == 8);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1Ticket {
    pub word0: u64,
    pub word1: u64,
    pub word2: u64,
    pub word3: u64,
}
const _: () = assert!(core::mem::size_of::<Oiv1Ticket>() == 32);
const _: () = assert!(core::mem::align_of::<Oiv1Ticket>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1Ticket, word0) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1Ticket, word1) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1Ticket, word2) == 16);
const _: () = assert!(core::mem::offset_of!(Oiv1Ticket, word3) == 24);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1Receipt {
    pub version: u64,
    pub size: u64,
    pub status: u64,
    pub validity_mask: u64,
    pub handle_echo: i64,
    pub phase: u64,
    pub stdin_state: u64,
    pub stdout_state: u64,
    pub stderr_state: u64,
    pub exit_kind: u64,
    pub exit_value: i64,
    pub error_domain: u64,
    pub error_code: u64,
    pub accepted_delta: u64,
    pub accepted_total: u64,
    pub written_total: u64,
    pub stdin_queued: u64,
    pub stdout_seen_total: u64,
    pub stderr_seen_total: u64,
    pub stdout_delivered_total: u64,
    pub stderr_delivered_total: u64,
    pub stdout_count: u64,
    pub stderr_count: u64,
    pub stdout_discarded_total: u64,
    pub stderr_discarded_total: u64,
    pub flags: u64,
    pub operation_sequence: u64,
    pub reserved0: u64,
    pub ticket0: u64,
    pub ticket1: u64,
    pub ticket2: u64,
    pub ticket3: u64,
}
const _: () = assert!(core::mem::size_of::<Oiv1Receipt>() == 256);
const _: () = assert!(core::mem::align_of::<Oiv1Receipt>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, version) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, size) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, status) == 16);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, validity_mask) == 24);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, handle_echo) == 32);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, phase) == 40);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stdin_state) == 48);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stdout_state) == 56);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stderr_state) == 64);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, exit_kind) == 72);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, exit_value) == 80);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, error_domain) == 88);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, error_code) == 96);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, accepted_delta) == 104);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, accepted_total) == 112);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, written_total) == 120);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stdin_queued) == 128);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stdout_seen_total) == 136);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stderr_seen_total) == 144);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stdout_delivered_total) == 152);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stderr_delivered_total) == 160);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stdout_count) == 168);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stderr_count) == 176);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stdout_discarded_total) == 184);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, stderr_discarded_total) == 192);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, flags) == 200);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, operation_sequence) == 208);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, reserved0) == 216);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, ticket0) == 224);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, ticket1) == 232);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, ticket2) == 240);
const _: () = assert!(core::mem::offset_of!(Oiv1Receipt, ticket3) == 248);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1Capabilities {
    pub version: u64,
    pub size: u64,
    pub status: u64,
    pub capability_mask: u64,
    pub max_leases: u64,
    pub stdin_capacity_max: u64,
    pub stdout_capacity_max: u64,
    pub stderr_capacity_max: u64,
    pub write_quantum: u64,
    pub output_chunk_max: u64,
    pub poll_wait_max: u64,
    pub segment_max: u64,
    pub clock_tag: u64,
    pub error_domain: u64,
    pub error_code: u64,
    pub reserved0: u64,
}
const _: () = assert!(core::mem::size_of::<Oiv1Capabilities>() == 128);
const _: () = assert!(core::mem::align_of::<Oiv1Capabilities>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, version) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, size) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, status) == 16);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, capability_mask) == 24);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, max_leases) == 32);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, stdin_capacity_max) == 40);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, stdout_capacity_max) == 48);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, stderr_capacity_max) == 56);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, write_quantum) == 64);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, output_chunk_max) == 72);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, poll_wait_max) == 80);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, segment_max) == 88);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, clock_tag) == 96);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, error_domain) == 104);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, error_code) == 112);
const _: () = assert!(core::mem::offset_of!(Oiv1Capabilities, reserved0) == 120);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1StartRequest {
    pub version: u64,
    pub size: u64,
    pub command: Oiv1ConstSpan,
    pub args: Oiv1Argv,
    pub deadline: Oiv1Deadline,
    pub stdin_capacity: u64,
    pub stdout_capacity: u64,
    pub stderr_capacity: u64,
    pub flags: u64,
}
const _: () = assert!(core::mem::size_of::<Oiv1StartRequest>() == 112);
const _: () = assert!(core::mem::align_of::<Oiv1StartRequest>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1StartRequest, version) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1StartRequest, size) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1StartRequest, command) == 16);
const _: () = assert!(core::mem::offset_of!(Oiv1StartRequest, args) == 32);
const _: () = assert!(core::mem::offset_of!(Oiv1StartRequest, deadline) == 48);
const _: () = assert!(core::mem::offset_of!(Oiv1StartRequest, stdin_capacity) == 80);
const _: () = assert!(core::mem::offset_of!(Oiv1StartRequest, stdout_capacity) == 88);
const _: () = assert!(core::mem::offset_of!(Oiv1StartRequest, stderr_capacity) == 96);
const _: () = assert!(core::mem::offset_of!(Oiv1StartRequest, flags) == 104);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1WriteRequest {
    pub version: u64,
    pub size: u64,
    pub handle: i64,
    pub bytes: Oiv1ConstSpan,
    pub data_offset: u64,
    pub max_bytes: u64,
    pub expected_accepted_total: u64,
    pub deadline: Oiv1Deadline,
}
const _: () = assert!(core::mem::size_of::<Oiv1WriteRequest>() == 96);
const _: () = assert!(core::mem::align_of::<Oiv1WriteRequest>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1WriteRequest, version) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1WriteRequest, size) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1WriteRequest, handle) == 16);
const _: () = assert!(core::mem::offset_of!(Oiv1WriteRequest, bytes) == 24);
const _: () = assert!(core::mem::offset_of!(Oiv1WriteRequest, data_offset) == 40);
const _: () = assert!(core::mem::offset_of!(Oiv1WriteRequest, max_bytes) == 48);
const _: () = assert!(core::mem::offset_of!(Oiv1WriteRequest, expected_accepted_total) == 56);
const _: () = assert!(core::mem::offset_of!(Oiv1WriteRequest, deadline) == 64);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1PollRequest {
    pub version: u64,
    pub size: u64,
    pub handle: i64,
    pub deadline: Oiv1Deadline,
    pub wait_ms: u64,
    pub stdout_buffer: Oiv1MutableSpan,
    pub stderr_buffer: Oiv1MutableSpan,
}
const _: () = assert!(core::mem::size_of::<Oiv1PollRequest>() == 96);
const _: () = assert!(core::mem::align_of::<Oiv1PollRequest>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1PollRequest, version) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1PollRequest, size) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1PollRequest, handle) == 16);
const _: () = assert!(core::mem::offset_of!(Oiv1PollRequest, deadline) == 24);
const _: () = assert!(core::mem::offset_of!(Oiv1PollRequest, wait_ms) == 56);
const _: () = assert!(core::mem::offset_of!(Oiv1PollRequest, stdout_buffer) == 64);
const _: () = assert!(core::mem::offset_of!(Oiv1PollRequest, stderr_buffer) == 80);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1ControlRequest {
    pub version: u64,
    pub size: u64,
    pub handle: i64,
    pub deadline: Oiv1Deadline,
    pub flags: u64,
}
const _: () = assert!(core::mem::size_of::<Oiv1ControlRequest>() == 64);
const _: () = assert!(core::mem::align_of::<Oiv1ControlRequest>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1ControlRequest, version) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1ControlRequest, size) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1ControlRequest, handle) == 16);
const _: () = assert!(core::mem::offset_of!(Oiv1ControlRequest, deadline) == 24);
const _: () = assert!(core::mem::offset_of!(Oiv1ControlRequest, flags) == 56);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1ReleaseRequest {
    pub version: u64,
    pub size: u64,
    pub handle: i64,
}
const _: () = assert!(core::mem::size_of::<Oiv1ReleaseRequest>() == 24);
const _: () = assert!(core::mem::align_of::<Oiv1ReleaseRequest>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1ReleaseRequest, version) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1ReleaseRequest, size) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1ReleaseRequest, handle) == 16);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1ResolveRequest {
    pub version: u64,
    pub size: u64,
    pub ticket: Oiv1Ticket,
    pub action: u64,
}
const _: () = assert!(core::mem::size_of::<Oiv1ResolveRequest>() == 56);
const _: () = assert!(core::mem::align_of::<Oiv1ResolveRequest>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1ResolveRequest, version) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1ResolveRequest, size) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1ResolveRequest, ticket) == 16);
const _: () = assert!(core::mem::offset_of!(Oiv1ResolveRequest, action) == 48);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Oiv1DeadlineRequest {
    pub version: u64,
    pub size: u64,
    pub timeout_ms: u64,
}
const _: () = assert!(core::mem::size_of::<Oiv1DeadlineRequest>() == 24);
const _: () = assert!(core::mem::align_of::<Oiv1DeadlineRequest>() == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1DeadlineRequest, version) == 0);
const _: () = assert!(core::mem::offset_of!(Oiv1DeadlineRequest, size) == 8);
const _: () = assert!(core::mem::offset_of!(Oiv1DeadlineRequest, timeout_ms) == 16);
pub const OIV1_STATUS_OK: u64 = 0;
pub const OIV1_STATUS_PENDING: u64 = 1;
pub const OIV1_STATUS_BUSY: u64 = 2;
pub const OIV1_STATUS_DEADLINEREACHED: u64 = 3;
pub const OIV1_STATUS_CONFLICT: u64 = 4;
pub const OIV1_STATUS_REJECTEDBEFORESTART: u64 = 5;
pub const OIV1_STATUS_STALE: u64 = 6;
pub const OIV1_STATUS_UNSUPPORTED: u64 = 7;
pub const OIV1_STATUS_NATIVEFAILURE: u64 = 8;
pub const OIV1_STATUS_NOTREADY: u64 = 9;
pub const OIV1_STATUS_RETAINEDCLEANUP: u64 = 10;
pub const OIV1_STATUS_PROJECTIONFAILURE: u64 = 11;
pub const OIV1_STATUS_INVALIDARGUMENT: u64 = 12;
pub const OIV1_PHASE_NOOWNER: u64 = 0;
pub const OIV1_PHASE_STARTING: u64 = 1;
pub const OIV1_PHASE_RUNNING: u64 = 2;
pub const OIV1_PHASE_STOPPING: u64 = 3;
pub const OIV1_PHASE_TERMINAL: u64 = 4;
pub const OIV1_PHASE_COLLECTING: u64 = 5;
pub const OIV1_PHASE_COLLECTED: u64 = 6;
pub const OIV1_PHASE_RELEASED: u64 = 7;
pub const OIV1_PHASE_FAILEDHELD: u64 = 8;
pub const OIV1_STREAM_PENDINGCREATION: u64 = 0;
pub const OIV1_STREAM_OPEN: u64 = 1;
pub const OIV1_STREAM_EOF: u64 = 2;
pub const OIV1_STREAM_FAILED: u64 = 3;
pub const OIV1_STREAM_NOTCREATED: u64 = 4;
pub const OIV1_STREAM_FINISHREQUESTED: u64 = 5;
pub const OIV1_EXIT_PENDING: u64 = 0;
pub const OIV1_EXIT_EXITED: u64 = 1;
pub const OIV1_EXIT_SIGNALLED: u64 = 2;
pub const OIV1_EXIT_FAILED: u64 = 3;
pub const OIV1_ERROR_NONE: u64 = 0;
pub const OIV1_ERROR_CONTRACT: u64 = 1;
pub const OIV1_ERROR_WIN32: u64 = 2;
pub const OIV1_ERROR_ERRNO: u64 = 3;
pub const OIV1_ERROR_PROJECTION: u64 = 4;
pub const OIV1_ERROR_ABI: u64 = 5;
pub const OIV1_RESOLVE_RECORDED: u64 = 0;
pub const OIV1_RESOLVE_ALREADYSAME: u64 = 1;
pub const OIV1_RESOLVE_CONFLICTING: u64 = 2;
pub const OIV1_RESOLVE_STALE: u64 = 3;
pub const OIV1_RESOLVE_RESOLVINGINPROGRESS: u64 = 4;
pub const OIV1_VALID_OWNER: u64 = 1;
pub const OIV1_VALID_PHASE: u64 = 2;
pub const OIV1_VALID_INPUT: u64 = 4;
pub const OIV1_VALID_STREAMS: u64 = 8;
pub const OIV1_VALID_EXIT: u64 = 16;
pub const OIV1_VALID_OUTPUT: u64 = 32;
pub const OIV1_VALID_COUNTS: u64 = 64;
pub const OIV1_VALID_ERROR: u64 = 128;
pub const OIV1_FLAG_OWNERHELD: u64 = 1;
pub const OIV1_FLAG_STARTPUBLICATIONPENDING: u64 = 2;
pub const OIV1_FLAG_OUTPUTDELIVERYRESERVED: u64 = 4;
pub const OIV1_FLAG_MAINTENANCEDEFERRED: u64 = 8;
pub const OIV1_FLAG_RESOURCESCLOSED: u64 = 16;
pub const OIV1_FLAG_NOCHILDPROVEN: u64 = 32;
pub const OIV1_FLAG_TREEEMPTY: u64 = 64;
pub const OIV1_FLAG_REAPED: u64 = 128;
pub const OIV1_FLAG_STDINFINISHREQUESTED: u64 = 256;
pub const OIV1_FLAG_CANCELREQUESTED: u64 = 512;
pub const OIV1_FLAG_TIMEDOUT: u64 = 1024;
pub const OIV1_FLAG_DISCARDREQUESTED: u64 = 2048;
pub const OIV1_FLAG_LOANPRESENT: u64 = 4096;
pub const OIV1_FLAG_LOCKCONTENDED: u64 = 8192;
pub const OIV1_FLAG_EXPIREDSEGMENT: u64 = 16384;
pub const OIV1_FLAG_OBSERVEDBEFOREWAIT: u64 = 32768;
pub const OIV1_CAP_OPAQUELEASE: u64 = 1;
pub const OIV1_CAP_ARGVMANAGEDABSOLUTE: u64 = 2;
pub const OIV1_CAP_RAWSEPARATE: u64 = 4;
pub const OIV1_CAP_PERSISTENTSTDIN: u64 = 8;
pub const OIV1_CAP_CUMULATIVEPARTIAL: u64 = 16;
pub const OIV1_CAP_PERSTREAMEOF: u64 = 32;
pub const OIV1_CAP_OWNERCLOCKDEADLINE: u64 = 64;
pub const OIV1_CAP_RETAINEDCLEANUP: u64 = 128;
pub const OIV1_CAP_BOUNDEDCROSSMODEADMISSION: u64 = 256;
pub const OIV1_CAP_STARTUPWORKER: u64 = 512;
pub const OIV1_CAP_ATOMICJOBATTACH: u64 = 1024;
pub const OIV1_CAP_TRANSACTIONALDELIVERY: u64 = 2048;
pub const OIV1_VERSION: u64 = 1;
pub const OIV1_ACTION_COMMIT: u64 = 1;
pub const OIV1_ACTION_ABORT: u64 = 2;
pub const OIV1_CLOCK_WINDOWS: u64 = 1;
pub const OIV1_CLOCK_POSIX: u64 = 2;
pub const OIV1_CAP_REQUIRED: u64 = 4095;
pub const OIV1_CAP_SEALED_PIN: u64 = 65536;
pub const OIV1_MAX_LEASES: u64 = 128;
pub const OIV1_STDIN_MAX: u64 = 65536;
pub const OIV1_STDOUT_MAX: u64 = 262144;
pub const OIV1_STDERR_MAX: u64 = 262144;
pub const OIV1_WRITE_QUANTUM: u64 = 4096;
pub const OIV1_OUTPUT_CHUNK_MAX: u64 = 65536;
pub const OIV1_POLL_WAIT_MAX_MS: u64 = 250;
pub const OIV1_SEGMENT_MAX: u64 = 256;
pub const OIV1_DEADLINE_MAX_MS: u64 = 600000;
pub const OIV1_ARG_COUNT_MAX: u64 = 128;
pub const OIV1_ARG_BYTES_MAX: u64 = 32768;
unsafe extern "C" {
    pub fn simple_owned_interactive_v1_capabilities(out: *mut Oiv1Capabilities, out_size: u64) -> i64;
    pub fn simple_owned_interactive_v1_deadline(request: *const Oiv1DeadlineRequest, request_size: u64, deadline: *mut Oiv1Deadline, out: *mut Oiv1Receipt, out_size: u64) -> i64;
    pub fn simple_owned_interactive_v1_start_begin(request: *const Oiv1StartRequest, request_size: u64, out: *mut Oiv1Receipt, out_size: u64) -> i64;
    pub fn simple_owned_interactive_v1_write_some(request: *const Oiv1WriteRequest, request_size: u64, out: *mut Oiv1Receipt, out_size: u64) -> i64;
    pub fn simple_owned_interactive_v1_poll_begin(request: *const Oiv1PollRequest, request_size: u64, out: *mut Oiv1Receipt, out_size: u64) -> i64;
    pub fn simple_owned_interactive_v1_close_stdin(request: *const Oiv1ControlRequest, request_size: u64, out: *mut Oiv1Receipt, out_size: u64) -> i64;
    pub fn simple_owned_interactive_v1_cancel(request: *const Oiv1ControlRequest, request_size: u64, out: *mut Oiv1Receipt, out_size: u64) -> i64;
    pub fn simple_owned_interactive_v1_collect(request: *const Oiv1ControlRequest, request_size: u64, out: *mut Oiv1Receipt, out_size: u64) -> i64;
    pub fn simple_owned_interactive_v1_release(request: *const Oiv1ReleaseRequest, request_size: u64, out: *mut Oiv1Receipt, out_size: u64) -> i64;
    pub fn simple_owned_interactive_v1_resolve(request: *const Oiv1ResolveRequest, request_size: u64) -> i64;
}
