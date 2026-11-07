/* Architecture ABI declarations only; implementation and qualification required. */
#ifndef SIMPLE_OWNED_INTERACTIVE_V1_ABI_H
#define SIMPLE_OWNED_INTERACTIVE_V1_ABI_H
#include <stdint.h>
#include <stddef.h>
_Static_assert(sizeof(void*) == 8, "64-bit ABI required");
typedef struct Oiv1Deadline {
    uint64_t version;
    uint64_t size;
    uint64_t clock_tag;
    int64_t expires_ms;
} Oiv1Deadline;
_Static_assert(sizeof(Oiv1Deadline) == 32, "Deadline size");
_Static_assert(_Alignof(Oiv1Deadline) == 8, "Deadline alignment");
_Static_assert(offsetof(Oiv1Deadline, version) == 0, "Deadline.version");
_Static_assert(offsetof(Oiv1Deadline, size) == 8, "Deadline.size");
_Static_assert(offsetof(Oiv1Deadline, clock_tag) == 16, "Deadline.clock_tag");
_Static_assert(offsetof(Oiv1Deadline, expires_ms) == 24, "Deadline.expires_ms");
typedef struct Oiv1ConstSpan {
    const uint8_t * data;
    uint64_t len;
} Oiv1ConstSpan;
_Static_assert(sizeof(Oiv1ConstSpan) == 16, "ConstSpan size");
_Static_assert(_Alignof(Oiv1ConstSpan) == 8, "ConstSpan alignment");
_Static_assert(offsetof(Oiv1ConstSpan, data) == 0, "ConstSpan.data");
_Static_assert(offsetof(Oiv1ConstSpan, len) == 8, "ConstSpan.len");
typedef struct Oiv1MutableSpan {
    uint8_t * data;
    uint64_t capacity;
} Oiv1MutableSpan;
_Static_assert(sizeof(Oiv1MutableSpan) == 16, "MutableSpan size");
_Static_assert(_Alignof(Oiv1MutableSpan) == 8, "MutableSpan alignment");
_Static_assert(offsetof(Oiv1MutableSpan, data) == 0, "MutableSpan.data");
_Static_assert(offsetof(Oiv1MutableSpan, capacity) == 8, "MutableSpan.capacity");
typedef struct Oiv1Argv {
    const Oiv1ConstSpan * data;
    uint64_t count;
} Oiv1Argv;
_Static_assert(sizeof(Oiv1Argv) == 16, "Argv size");
_Static_assert(_Alignof(Oiv1Argv) == 8, "Argv alignment");
_Static_assert(offsetof(Oiv1Argv, data) == 0, "Argv.data");
_Static_assert(offsetof(Oiv1Argv, count) == 8, "Argv.count");
typedef struct Oiv1Ticket {
    uint64_t word0;
    uint64_t word1;
    uint64_t word2;
    uint64_t word3;
} Oiv1Ticket;
_Static_assert(sizeof(Oiv1Ticket) == 32, "Ticket size");
_Static_assert(_Alignof(Oiv1Ticket) == 8, "Ticket alignment");
_Static_assert(offsetof(Oiv1Ticket, word0) == 0, "Ticket.word0");
_Static_assert(offsetof(Oiv1Ticket, word1) == 8, "Ticket.word1");
_Static_assert(offsetof(Oiv1Ticket, word2) == 16, "Ticket.word2");
_Static_assert(offsetof(Oiv1Ticket, word3) == 24, "Ticket.word3");
typedef struct Oiv1Receipt {
    uint64_t version;
    uint64_t size;
    uint64_t status;
    uint64_t validity_mask;
    int64_t handle_echo;
    uint64_t phase;
    uint64_t stdin_state;
    uint64_t stdout_state;
    uint64_t stderr_state;
    uint64_t exit_kind;
    int64_t exit_value;
    uint64_t error_domain;
    uint64_t error_code;
    uint64_t accepted_delta;
    uint64_t accepted_total;
    uint64_t written_total;
    uint64_t stdin_queued;
    uint64_t stdout_seen_total;
    uint64_t stderr_seen_total;
    uint64_t stdout_delivered_total;
    uint64_t stderr_delivered_total;
    uint64_t stdout_count;
    uint64_t stderr_count;
    uint64_t stdout_discarded_total;
    uint64_t stderr_discarded_total;
    uint64_t flags;
    uint64_t operation_sequence;
    uint64_t reserved0;
    uint64_t ticket0;
    uint64_t ticket1;
    uint64_t ticket2;
    uint64_t ticket3;
} Oiv1Receipt;
_Static_assert(sizeof(Oiv1Receipt) == 256, "Receipt size");
_Static_assert(_Alignof(Oiv1Receipt) == 8, "Receipt alignment");
_Static_assert(offsetof(Oiv1Receipt, version) == 0, "Receipt.version");
_Static_assert(offsetof(Oiv1Receipt, size) == 8, "Receipt.size");
_Static_assert(offsetof(Oiv1Receipt, status) == 16, "Receipt.status");
_Static_assert(offsetof(Oiv1Receipt, validity_mask) == 24, "Receipt.validity_mask");
_Static_assert(offsetof(Oiv1Receipt, handle_echo) == 32, "Receipt.handle_echo");
_Static_assert(offsetof(Oiv1Receipt, phase) == 40, "Receipt.phase");
_Static_assert(offsetof(Oiv1Receipt, stdin_state) == 48, "Receipt.stdin_state");
_Static_assert(offsetof(Oiv1Receipt, stdout_state) == 56, "Receipt.stdout_state");
_Static_assert(offsetof(Oiv1Receipt, stderr_state) == 64, "Receipt.stderr_state");
_Static_assert(offsetof(Oiv1Receipt, exit_kind) == 72, "Receipt.exit_kind");
_Static_assert(offsetof(Oiv1Receipt, exit_value) == 80, "Receipt.exit_value");
_Static_assert(offsetof(Oiv1Receipt, error_domain) == 88, "Receipt.error_domain");
_Static_assert(offsetof(Oiv1Receipt, error_code) == 96, "Receipt.error_code");
_Static_assert(offsetof(Oiv1Receipt, accepted_delta) == 104, "Receipt.accepted_delta");
_Static_assert(offsetof(Oiv1Receipt, accepted_total) == 112, "Receipt.accepted_total");
_Static_assert(offsetof(Oiv1Receipt, written_total) == 120, "Receipt.written_total");
_Static_assert(offsetof(Oiv1Receipt, stdin_queued) == 128, "Receipt.stdin_queued");
_Static_assert(offsetof(Oiv1Receipt, stdout_seen_total) == 136, "Receipt.stdout_seen_total");
_Static_assert(offsetof(Oiv1Receipt, stderr_seen_total) == 144, "Receipt.stderr_seen_total");
_Static_assert(offsetof(Oiv1Receipt, stdout_delivered_total) == 152, "Receipt.stdout_delivered_total");
_Static_assert(offsetof(Oiv1Receipt, stderr_delivered_total) == 160, "Receipt.stderr_delivered_total");
_Static_assert(offsetof(Oiv1Receipt, stdout_count) == 168, "Receipt.stdout_count");
_Static_assert(offsetof(Oiv1Receipt, stderr_count) == 176, "Receipt.stderr_count");
_Static_assert(offsetof(Oiv1Receipt, stdout_discarded_total) == 184, "Receipt.stdout_discarded_total");
_Static_assert(offsetof(Oiv1Receipt, stderr_discarded_total) == 192, "Receipt.stderr_discarded_total");
_Static_assert(offsetof(Oiv1Receipt, flags) == 200, "Receipt.flags");
_Static_assert(offsetof(Oiv1Receipt, operation_sequence) == 208, "Receipt.operation_sequence");
_Static_assert(offsetof(Oiv1Receipt, reserved0) == 216, "Receipt.reserved0");
_Static_assert(offsetof(Oiv1Receipt, ticket0) == 224, "Receipt.ticket0");
_Static_assert(offsetof(Oiv1Receipt, ticket1) == 232, "Receipt.ticket1");
_Static_assert(offsetof(Oiv1Receipt, ticket2) == 240, "Receipt.ticket2");
_Static_assert(offsetof(Oiv1Receipt, ticket3) == 248, "Receipt.ticket3");
typedef struct Oiv1Capabilities {
    uint64_t version;
    uint64_t size;
    uint64_t status;
    uint64_t capability_mask;
    uint64_t max_leases;
    uint64_t stdin_capacity_max;
    uint64_t stdout_capacity_max;
    uint64_t stderr_capacity_max;
    uint64_t write_quantum;
    uint64_t output_chunk_max;
    uint64_t poll_wait_max;
    uint64_t segment_max;
    uint64_t clock_tag;
    uint64_t error_domain;
    uint64_t error_code;
    uint64_t reserved0;
} Oiv1Capabilities;
_Static_assert(sizeof(Oiv1Capabilities) == 128, "Capabilities size");
_Static_assert(_Alignof(Oiv1Capabilities) == 8, "Capabilities alignment");
_Static_assert(offsetof(Oiv1Capabilities, version) == 0, "Capabilities.version");
_Static_assert(offsetof(Oiv1Capabilities, size) == 8, "Capabilities.size");
_Static_assert(offsetof(Oiv1Capabilities, status) == 16, "Capabilities.status");
_Static_assert(offsetof(Oiv1Capabilities, capability_mask) == 24, "Capabilities.capability_mask");
_Static_assert(offsetof(Oiv1Capabilities, max_leases) == 32, "Capabilities.max_leases");
_Static_assert(offsetof(Oiv1Capabilities, stdin_capacity_max) == 40, "Capabilities.stdin_capacity_max");
_Static_assert(offsetof(Oiv1Capabilities, stdout_capacity_max) == 48, "Capabilities.stdout_capacity_max");
_Static_assert(offsetof(Oiv1Capabilities, stderr_capacity_max) == 56, "Capabilities.stderr_capacity_max");
_Static_assert(offsetof(Oiv1Capabilities, write_quantum) == 64, "Capabilities.write_quantum");
_Static_assert(offsetof(Oiv1Capabilities, output_chunk_max) == 72, "Capabilities.output_chunk_max");
_Static_assert(offsetof(Oiv1Capabilities, poll_wait_max) == 80, "Capabilities.poll_wait_max");
_Static_assert(offsetof(Oiv1Capabilities, segment_max) == 88, "Capabilities.segment_max");
_Static_assert(offsetof(Oiv1Capabilities, clock_tag) == 96, "Capabilities.clock_tag");
_Static_assert(offsetof(Oiv1Capabilities, error_domain) == 104, "Capabilities.error_domain");
_Static_assert(offsetof(Oiv1Capabilities, error_code) == 112, "Capabilities.error_code");
_Static_assert(offsetof(Oiv1Capabilities, reserved0) == 120, "Capabilities.reserved0");
typedef struct Oiv1StartRequest {
    uint64_t version;
    uint64_t size;
    Oiv1ConstSpan command;
    Oiv1Argv args;
    Oiv1Deadline deadline;
    uint64_t stdin_capacity;
    uint64_t stdout_capacity;
    uint64_t stderr_capacity;
    uint64_t flags;
} Oiv1StartRequest;
_Static_assert(sizeof(Oiv1StartRequest) == 112, "StartRequest size");
_Static_assert(_Alignof(Oiv1StartRequest) == 8, "StartRequest alignment");
_Static_assert(offsetof(Oiv1StartRequest, version) == 0, "StartRequest.version");
_Static_assert(offsetof(Oiv1StartRequest, size) == 8, "StartRequest.size");
_Static_assert(offsetof(Oiv1StartRequest, command) == 16, "StartRequest.command");
_Static_assert(offsetof(Oiv1StartRequest, args) == 32, "StartRequest.args");
_Static_assert(offsetof(Oiv1StartRequest, deadline) == 48, "StartRequest.deadline");
_Static_assert(offsetof(Oiv1StartRequest, stdin_capacity) == 80, "StartRequest.stdin_capacity");
_Static_assert(offsetof(Oiv1StartRequest, stdout_capacity) == 88, "StartRequest.stdout_capacity");
_Static_assert(offsetof(Oiv1StartRequest, stderr_capacity) == 96, "StartRequest.stderr_capacity");
_Static_assert(offsetof(Oiv1StartRequest, flags) == 104, "StartRequest.flags");
typedef struct Oiv1WriteRequest {
    uint64_t version;
    uint64_t size;
    int64_t handle;
    Oiv1ConstSpan bytes;
    uint64_t data_offset;
    uint64_t max_bytes;
    uint64_t expected_accepted_total;
    Oiv1Deadline deadline;
} Oiv1WriteRequest;
_Static_assert(sizeof(Oiv1WriteRequest) == 96, "WriteRequest size");
_Static_assert(_Alignof(Oiv1WriteRequest) == 8, "WriteRequest alignment");
_Static_assert(offsetof(Oiv1WriteRequest, version) == 0, "WriteRequest.version");
_Static_assert(offsetof(Oiv1WriteRequest, size) == 8, "WriteRequest.size");
_Static_assert(offsetof(Oiv1WriteRequest, handle) == 16, "WriteRequest.handle");
_Static_assert(offsetof(Oiv1WriteRequest, bytes) == 24, "WriteRequest.bytes");
_Static_assert(offsetof(Oiv1WriteRequest, data_offset) == 40, "WriteRequest.data_offset");
_Static_assert(offsetof(Oiv1WriteRequest, max_bytes) == 48, "WriteRequest.max_bytes");
_Static_assert(offsetof(Oiv1WriteRequest, expected_accepted_total) == 56, "WriteRequest.expected_accepted_total");
_Static_assert(offsetof(Oiv1WriteRequest, deadline) == 64, "WriteRequest.deadline");
typedef struct Oiv1PollRequest {
    uint64_t version;
    uint64_t size;
    int64_t handle;
    Oiv1Deadline deadline;
    uint64_t wait_ms;
    Oiv1MutableSpan stdout_buffer;
    Oiv1MutableSpan stderr_buffer;
} Oiv1PollRequest;
_Static_assert(sizeof(Oiv1PollRequest) == 96, "PollRequest size");
_Static_assert(_Alignof(Oiv1PollRequest) == 8, "PollRequest alignment");
_Static_assert(offsetof(Oiv1PollRequest, version) == 0, "PollRequest.version");
_Static_assert(offsetof(Oiv1PollRequest, size) == 8, "PollRequest.size");
_Static_assert(offsetof(Oiv1PollRequest, handle) == 16, "PollRequest.handle");
_Static_assert(offsetof(Oiv1PollRequest, deadline) == 24, "PollRequest.deadline");
_Static_assert(offsetof(Oiv1PollRequest, wait_ms) == 56, "PollRequest.wait_ms");
_Static_assert(offsetof(Oiv1PollRequest, stdout_buffer) == 64, "PollRequest.stdout_buffer");
_Static_assert(offsetof(Oiv1PollRequest, stderr_buffer) == 80, "PollRequest.stderr_buffer");
typedef struct Oiv1ControlRequest {
    uint64_t version;
    uint64_t size;
    int64_t handle;
    Oiv1Deadline deadline;
    uint64_t flags;
} Oiv1ControlRequest;
_Static_assert(sizeof(Oiv1ControlRequest) == 64, "ControlRequest size");
_Static_assert(_Alignof(Oiv1ControlRequest) == 8, "ControlRequest alignment");
_Static_assert(offsetof(Oiv1ControlRequest, version) == 0, "ControlRequest.version");
_Static_assert(offsetof(Oiv1ControlRequest, size) == 8, "ControlRequest.size");
_Static_assert(offsetof(Oiv1ControlRequest, handle) == 16, "ControlRequest.handle");
_Static_assert(offsetof(Oiv1ControlRequest, deadline) == 24, "ControlRequest.deadline");
_Static_assert(offsetof(Oiv1ControlRequest, flags) == 56, "ControlRequest.flags");
typedef struct Oiv1ReleaseRequest {
    uint64_t version;
    uint64_t size;
    int64_t handle;
} Oiv1ReleaseRequest;
_Static_assert(sizeof(Oiv1ReleaseRequest) == 24, "ReleaseRequest size");
_Static_assert(_Alignof(Oiv1ReleaseRequest) == 8, "ReleaseRequest alignment");
_Static_assert(offsetof(Oiv1ReleaseRequest, version) == 0, "ReleaseRequest.version");
_Static_assert(offsetof(Oiv1ReleaseRequest, size) == 8, "ReleaseRequest.size");
_Static_assert(offsetof(Oiv1ReleaseRequest, handle) == 16, "ReleaseRequest.handle");
typedef struct Oiv1ResolveRequest {
    uint64_t version;
    uint64_t size;
    Oiv1Ticket ticket;
    uint64_t action;
} Oiv1ResolveRequest;
_Static_assert(sizeof(Oiv1ResolveRequest) == 56, "ResolveRequest size");
_Static_assert(_Alignof(Oiv1ResolveRequest) == 8, "ResolveRequest alignment");
_Static_assert(offsetof(Oiv1ResolveRequest, version) == 0, "ResolveRequest.version");
_Static_assert(offsetof(Oiv1ResolveRequest, size) == 8, "ResolveRequest.size");
_Static_assert(offsetof(Oiv1ResolveRequest, ticket) == 16, "ResolveRequest.ticket");
_Static_assert(offsetof(Oiv1ResolveRequest, action) == 48, "ResolveRequest.action");
typedef struct Oiv1DeadlineRequest {
    uint64_t version;
    uint64_t size;
    uint64_t timeout_ms;
} Oiv1DeadlineRequest;
_Static_assert(sizeof(Oiv1DeadlineRequest) == 24, "DeadlineRequest size");
_Static_assert(_Alignof(Oiv1DeadlineRequest) == 8, "DeadlineRequest alignment");
_Static_assert(offsetof(Oiv1DeadlineRequest, version) == 0, "DeadlineRequest.version");
_Static_assert(offsetof(Oiv1DeadlineRequest, size) == 8, "DeadlineRequest.size");
_Static_assert(offsetof(Oiv1DeadlineRequest, timeout_ms) == 16, "DeadlineRequest.timeout_ms");
#define OIV1_STATUS_OK UINT64_C(0)
#define OIV1_STATUS_PENDING UINT64_C(1)
#define OIV1_STATUS_BUSY UINT64_C(2)
#define OIV1_STATUS_DEADLINEREACHED UINT64_C(3)
#define OIV1_STATUS_CONFLICT UINT64_C(4)
#define OIV1_STATUS_REJECTEDBEFORESTART UINT64_C(5)
#define OIV1_STATUS_STALE UINT64_C(6)
#define OIV1_STATUS_UNSUPPORTED UINT64_C(7)
#define OIV1_STATUS_NATIVEFAILURE UINT64_C(8)
#define OIV1_STATUS_NOTREADY UINT64_C(9)
#define OIV1_STATUS_RETAINEDCLEANUP UINT64_C(10)
#define OIV1_STATUS_PROJECTIONFAILURE UINT64_C(11)
#define OIV1_STATUS_INVALIDARGUMENT UINT64_C(12)
#define OIV1_PHASE_NOOWNER UINT64_C(0)
#define OIV1_PHASE_STARTING UINT64_C(1)
#define OIV1_PHASE_RUNNING UINT64_C(2)
#define OIV1_PHASE_STOPPING UINT64_C(3)
#define OIV1_PHASE_TERMINAL UINT64_C(4)
#define OIV1_PHASE_COLLECTING UINT64_C(5)
#define OIV1_PHASE_COLLECTED UINT64_C(6)
#define OIV1_PHASE_RELEASED UINT64_C(7)
#define OIV1_PHASE_FAILEDHELD UINT64_C(8)
#define OIV1_STREAM_PENDINGCREATION UINT64_C(0)
#define OIV1_STREAM_OPEN UINT64_C(1)
#define OIV1_STREAM_EOF UINT64_C(2)
#define OIV1_STREAM_FAILED UINT64_C(3)
#define OIV1_STREAM_NOTCREATED UINT64_C(4)
#define OIV1_STREAM_FINISHREQUESTED UINT64_C(5)
#define OIV1_EXIT_PENDING UINT64_C(0)
#define OIV1_EXIT_EXITED UINT64_C(1)
#define OIV1_EXIT_SIGNALLED UINT64_C(2)
#define OIV1_EXIT_FAILED UINT64_C(3)
#define OIV1_ERROR_NONE UINT64_C(0)
#define OIV1_ERROR_CONTRACT UINT64_C(1)
#define OIV1_ERROR_WIN32 UINT64_C(2)
#define OIV1_ERROR_ERRNO UINT64_C(3)
#define OIV1_ERROR_PROJECTION UINT64_C(4)
#define OIV1_ERROR_ABI UINT64_C(5)
#define OIV1_RESOLVE_RECORDED UINT64_C(0)
#define OIV1_RESOLVE_ALREADYSAME UINT64_C(1)
#define OIV1_RESOLVE_CONFLICTING UINT64_C(2)
#define OIV1_RESOLVE_STALE UINT64_C(3)
#define OIV1_RESOLVE_RESOLVINGINPROGRESS UINT64_C(4)
#define OIV1_VALID_OWNER UINT64_C(1)
#define OIV1_VALID_PHASE UINT64_C(2)
#define OIV1_VALID_INPUT UINT64_C(4)
#define OIV1_VALID_STREAMS UINT64_C(8)
#define OIV1_VALID_EXIT UINT64_C(16)
#define OIV1_VALID_OUTPUT UINT64_C(32)
#define OIV1_VALID_COUNTS UINT64_C(64)
#define OIV1_VALID_ERROR UINT64_C(128)
#define OIV1_FLAG_OWNERHELD UINT64_C(1)
#define OIV1_FLAG_STARTPUBLICATIONPENDING UINT64_C(2)
#define OIV1_FLAG_OUTPUTDELIVERYRESERVED UINT64_C(4)
#define OIV1_FLAG_MAINTENANCEDEFERRED UINT64_C(8)
#define OIV1_FLAG_RESOURCESCLOSED UINT64_C(16)
#define OIV1_FLAG_NOCHILDPROVEN UINT64_C(32)
#define OIV1_FLAG_TREEEMPTY UINT64_C(64)
#define OIV1_FLAG_REAPED UINT64_C(128)
#define OIV1_FLAG_STDINFINISHREQUESTED UINT64_C(256)
#define OIV1_FLAG_CANCELREQUESTED UINT64_C(512)
#define OIV1_FLAG_TIMEDOUT UINT64_C(1024)
#define OIV1_FLAG_DISCARDREQUESTED UINT64_C(2048)
#define OIV1_FLAG_LOANPRESENT UINT64_C(4096)
#define OIV1_FLAG_LOCKCONTENDED UINT64_C(8192)
#define OIV1_FLAG_EXPIREDSEGMENT UINT64_C(16384)
#define OIV1_FLAG_OBSERVEDBEFOREWAIT UINT64_C(32768)
#define OIV1_CAP_OPAQUELEASE UINT64_C(1)
#define OIV1_CAP_ARGVMANAGEDABSOLUTE UINT64_C(2)
#define OIV1_CAP_RAWSEPARATE UINT64_C(4)
#define OIV1_CAP_PERSISTENTSTDIN UINT64_C(8)
#define OIV1_CAP_CUMULATIVEPARTIAL UINT64_C(16)
#define OIV1_CAP_PERSTREAMEOF UINT64_C(32)
#define OIV1_CAP_OWNERCLOCKDEADLINE UINT64_C(64)
#define OIV1_CAP_RETAINEDCLEANUP UINT64_C(128)
#define OIV1_CAP_BOUNDEDCROSSMODEADMISSION UINT64_C(256)
#define OIV1_CAP_STARTUPWORKER UINT64_C(512)
#define OIV1_CAP_ATOMICJOBATTACH UINT64_C(1024)
#define OIV1_CAP_TRANSACTIONALDELIVERY UINT64_C(2048)
#define OIV1_VERSION UINT64_C(1)
#define OIV1_ACTION_COMMIT UINT64_C(1)
#define OIV1_ACTION_ABORT UINT64_C(2)
#define OIV1_CLOCK_WINDOWS UINT64_C(1)
#define OIV1_CLOCK_POSIX UINT64_C(2)
#define OIV1_CAP_REQUIRED UINT64_C(4095)
#define OIV1_CAP_SEALED_PIN UINT64_C(65536)
#define OIV1_MAX_LEASES UINT64_C(128)
#define OIV1_STDIN_MAX UINT64_C(65536)
#define OIV1_STDOUT_MAX UINT64_C(262144)
#define OIV1_STDERR_MAX UINT64_C(262144)
#define OIV1_WRITE_QUANTUM UINT64_C(4096)
#define OIV1_OUTPUT_CHUNK_MAX UINT64_C(65536)
#define OIV1_POLL_WAIT_MAX_MS UINT64_C(250)
#define OIV1_SEGMENT_MAX UINT64_C(256)
#define OIV1_DEADLINE_MAX_MS UINT64_C(600000)
#define OIV1_ARG_COUNT_MAX UINT64_C(128)
#define OIV1_ARG_BYTES_MAX UINT64_C(32768)
int64_t simple_owned_interactive_v1_capabilities(Oiv1Capabilities *out, uint64_t out_size);
int64_t simple_owned_interactive_v1_deadline(const Oiv1DeadlineRequest *request, uint64_t request_size, Oiv1Deadline *deadline, Oiv1Receipt *out, uint64_t out_size);
int64_t simple_owned_interactive_v1_start_begin(const Oiv1StartRequest *request, uint64_t request_size, Oiv1Receipt *out, uint64_t out_size);
int64_t simple_owned_interactive_v1_write_some(const Oiv1WriteRequest *request, uint64_t request_size, Oiv1Receipt *out, uint64_t out_size);
int64_t simple_owned_interactive_v1_poll_begin(const Oiv1PollRequest *request, uint64_t request_size, Oiv1Receipt *out, uint64_t out_size);
int64_t simple_owned_interactive_v1_close_stdin(const Oiv1ControlRequest *request, uint64_t request_size, Oiv1Receipt *out, uint64_t out_size);
int64_t simple_owned_interactive_v1_cancel(const Oiv1ControlRequest *request, uint64_t request_size, Oiv1Receipt *out, uint64_t out_size);
int64_t simple_owned_interactive_v1_collect(const Oiv1ControlRequest *request, uint64_t request_size, Oiv1Receipt *out, uint64_t out_size);
int64_t simple_owned_interactive_v1_release(const Oiv1ReleaseRequest *request, uint64_t request_size, Oiv1Receipt *out, uint64_t out_size);
int64_t simple_owned_interactive_v1_resolve(const Oiv1ResolveRequest *request, uint64_t request_size);
#endif
