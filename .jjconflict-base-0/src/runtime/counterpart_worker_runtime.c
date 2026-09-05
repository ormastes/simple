/* simple-counterpart-worker — isolated counterpart provider worker (Wave-1 F3).
 *
 * Design: doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md §3.2, §3.3
 * Frozen ABI: tools/counterpart/sdk/c/simple_counterpart_abi.h
 * Frozen Simple contracts: src/lib/common/spec/evidence/counterpart/model.spl
 *
 * The worker loads exactly ONE adapter shared library, validates its manifest,
 * then reads length-framed requests from stdin and writes one length-framed
 * receipt per request to stdout. Every invocation runs in a FORKED CHILD; the
 * parent side supervises it under CPU / address-space / output-size / wall-time
 * budgets and turns abnormal termination into a TYPED receipt:
 *
 *     provider_status: executed        the adapter ran and returned
 *     provider_status: crashed         the child died on a signal (abort, SEGV)
 *     provider_status: timed_out       wall-clock deadline or output budget kill
 *     provider_status: unavailable     the adapter could not be loaded at all
 *     provider_status: rejected_manifest  manifest failed validation
 *
 * `crashed` is NEVER folded into `unavailable`: an adapter that aborted is a
 * defect, an adapter that is absent is an environment fact, and collapsing the
 * two is exactly how a real crash becomes a green run. The worker itself exits
 * 0 after a crashed invocation — containment is the entire point.
 *
 * Framing (both directions; lengths are ASCII decimal so the frame header is
 * greppable and generatable from a shell, payload bytes stay raw and are never
 * assumed NUL-terminated):
 *
 *   request   "SCFQ1 <component_id_len> <request_len>\n" <component_id> <request>
 *   receipt   "SCFR1 <payload_len>\n" <payload>          payload is SDN text
 *
 * Build (standalone):
 *   cc -std=c99 -Wall -Wextra -Itools/counterpart/sdk/c \
 *      -o build/counterpart/simple-counterpart-worker \
 *      src/runtime/counterpart_worker_runtime.c -ldl
 */

#define _POSIX_C_SOURCE 200809L

#include "simple_counterpart_abi.h"

#include <dlfcn.h>
#include <errno.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

/* ------------------------------------------------------------------------ */
/* Budgets                                                                   */
/* ------------------------------------------------------------------------ */

#define WORKER_DEFAULT_TIMEOUT_MS      5000
#define WORKER_DEFAULT_MAX_OUTPUT      (1024u * 1024u)
#define WORKER_DEFAULT_MAX_INVOCATIONS 64
#define WORKER_DEFAULT_CPU_SECONDS     10
#define WORKER_DEFAULT_MEMORY_BYTES    (512ull * 1024ull * 1024ull)

#define WORKER_MAX_FRAME_BYTES (64ull * 1024ull * 1024ull)

typedef struct {
    const char *adapter_path;
    const char *configuration;
    long timeout_ms;
    unsigned long max_output_bytes;
    long max_invocations;
    long cpu_seconds;
    unsigned long long memory_bytes;
} worker_options;

/* ------------------------------------------------------------------------ */
/* Growable byte buffer                                                      */
/* ------------------------------------------------------------------------ */

typedef struct {
    unsigned char *data;
    size_t size;
    size_t capacity;
    int overflowed;
    size_t limit;
} byte_buffer;

static void buffer_init(byte_buffer *b, size_t limit) {
    b->data = NULL;
    b->size = 0;
    b->capacity = 0;
    b->overflowed = 0;
    b->limit = limit;
}

static void buffer_free(byte_buffer *b) {
    free(b->data);
    b->data = NULL;
    b->size = 0;
    b->capacity = 0;
}

static int buffer_append(byte_buffer *b, const unsigned char *data, size_t size) {
    size_t needed;
    if (size == 0) return 0;
    if (b->limit > 0 && b->size + size > b->limit) {
        b->overflowed = 1;
        size = (b->size >= b->limit) ? 0 : (b->limit - b->size);
        if (size == 0) return -1;
    }
    needed = b->size + size;
    if (needed > b->capacity) {
        size_t capacity = (b->capacity == 0) ? 4096 : b->capacity;
        unsigned char *grown;
        while (capacity < needed) capacity *= 2;
        grown = (unsigned char *)realloc(b->data, capacity);
        if (!grown) return -1;
        b->data = grown;
        b->capacity = capacity;
    }
    memcpy(b->data + b->size, data, size);
    b->size += size;
    return b->overflowed ? -1 : 0;
}

/* Writer sink handed to the adapter — caller-owned, adapter allocates nothing. */
static int32_t buffer_writer_write(void *context, const uint8_t *data, uint64_t size) {
    byte_buffer *b = (byte_buffer *)context;
    if (!b) return SCF_INVALID_ARG;
    if (size == 0) return SCF_OK;
    if (!data) return SCF_INVALID_ARG;
    if (buffer_append(b, (const unsigned char *)data, (size_t)size) != 0) {
        return SCF_INTERNAL; /* budget hit: stop the adapter writing more */
    }
    return SCF_OK;
}

/* ------------------------------------------------------------------------ */
/* Full-write / full-read helpers                                            */
/* ------------------------------------------------------------------------ */

static int write_all(int fd, const void *data, size_t size) {
    const unsigned char *cursor = (const unsigned char *)data;
    while (size > 0) {
        ssize_t written = write(fd, cursor, size);
        if (written < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        cursor += (size_t)written;
        size -= (size_t)written;
    }
    return 0;
}

static int read_all(int fd, void *data, size_t size) {
    unsigned char *cursor = (unsigned char *)data;
    while (size > 0) {
        ssize_t got = read(fd, cursor, size);
        if (got < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        if (got == 0) return -1; /* short frame */
        cursor += (size_t)got;
        size -= (size_t)got;
    }
    return 0;
}

/* ------------------------------------------------------------------------ */
/* Monotonic time                                                            */
/* ------------------------------------------------------------------------ */

static long long monotonic_ms(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return 0;
    return (long long)now.tv_sec * 1000LL + (long long)(now.tv_nsec / 1000000L);
}

/* ------------------------------------------------------------------------ */
/* SDN receipt emission                                                      */
/* ------------------------------------------------------------------------ */

static void sdn_append_escaped(byte_buffer *out,
                               const unsigned char *data,
                               size_t size) {
    static const char hex[] = "0123456789abcdef";
    size_t index;
    for (index = 0; index < size; index++) {
        unsigned char byte = data[index];
        char encoded[4];
        size_t encoded_len;
        if (byte == '"' || byte == '\\') {
            encoded[0] = '\\';
            encoded[1] = (char)byte;
            encoded_len = 2;
        } else if (byte >= 0x20 && byte < 0x7F) {
            encoded[0] = (char)byte;
            encoded_len = 1;
        } else {
            encoded[0] = '\\';
            encoded[1] = 'x';
            encoded[2] = hex[(byte >> 4) & 0xF];
            encoded[3] = hex[byte & 0xF];
            encoded_len = 4;
        }
        (void)buffer_append(out, (const unsigned char *)encoded, encoded_len);
    }
}

static void sdn_append_text(byte_buffer *out, const char *text) {
    (void)buffer_append(out, (const unsigned char *)text, strlen(text));
}

static void sdn_append_field_text(byte_buffer *out, const char *key, const char *value) {
    sdn_append_text(out, key);
    sdn_append_text(out, ": \"");
    sdn_append_escaped(out, (const unsigned char *)value, strlen(value));
    sdn_append_text(out, "\"\n");
}

static void sdn_append_field_long(byte_buffer *out, const char *key, long long value) {
    char digits[32];
    snprintf(digits, sizeof(digits), "%lld", value);
    sdn_append_text(out, key);
    sdn_append_text(out, ": ");
    sdn_append_text(out, digits);
    sdn_append_text(out, "\n");
}

/* One receipt, length-framed, to stdout. Returns 0 on success. */
static int emit_receipt(const char *provider_status,
                        const char *component_id,
                        size_t component_id_size,
                        long long invocation,
                        int32_t call_status,
                        int exit_signal,
                        int exit_code,
                        long long duration_ms,
                        const byte_buffer *response,
                        const byte_buffer *trace,
                        const char *diagnostic) {
    byte_buffer payload;
    char header[64];
    int failed;

    buffer_init(&payload, 0);
    sdn_append_text(&payload, "schema_id: simple.counterpart.worker_receipt.v1\n");
    sdn_append_text(&payload, "schema_version: 1\n");
    sdn_append_text(&payload, "provider_status: ");
    sdn_append_text(&payload, provider_status);
    sdn_append_text(&payload, "\n");

    sdn_append_text(&payload, "component_id: \"");
    sdn_append_escaped(&payload, (const unsigned char *)component_id, component_id_size);
    sdn_append_text(&payload, "\"\n");

    sdn_append_field_long(&payload, "invocation", invocation);
    sdn_append_field_long(&payload, "call_status", (long long)call_status);
    sdn_append_field_long(&payload, "exit_signal", (long long)exit_signal);
    sdn_append_field_long(&payload, "exit_code", (long long)exit_code);
    sdn_append_field_long(&payload, "duration_ms", duration_ms);

    sdn_append_field_long(&payload, "response_bytes",
                          response ? (long long)response->size : 0);
    sdn_append_text(&payload, "response: \"");
    if (response && response->size > 0) {
        sdn_append_escaped(&payload, response->data, response->size);
    }
    sdn_append_text(&payload, "\"\n");

    sdn_append_field_long(&payload, "trace_bytes", trace ? (long long)trace->size : 0);
    sdn_append_text(&payload, "trace: \"");
    if (trace && trace->size > 0) {
        sdn_append_escaped(&payload, trace->data, trace->size);
    }
    sdn_append_text(&payload, "\"\n");

    sdn_append_field_text(&payload, "diagnostic", diagnostic ? diagnostic : "");

    snprintf(header, sizeof(header), "SCFR1 %llu\n", (unsigned long long)payload.size);
    failed = write_all(STDOUT_FILENO, header, strlen(header));
    if (failed == 0 && payload.size > 0) {
        failed = write_all(STDOUT_FILENO, payload.data, payload.size);
    }
    buffer_free(&payload);
    return failed;
}

/* ------------------------------------------------------------------------ */
/* Manifest validation                                                       */
/* ------------------------------------------------------------------------ */

/* Minimal, deliberately strict scan of the manifest SDN text. Full parsing is
 * the Simple side's job; the worker only has to refuse to run a table it must
 * not trust. */
static int manifest_is_acceptable(const byte_buffer *manifest, char *reason, size_t reason_size) {
    char *text;
    const char *found;
    int acceptable = 0;

    if (!manifest || manifest->size == 0) {
        snprintf(reason, reason_size, "manifest is empty");
        return 0;
    }
    text = (char *)malloc(manifest->size + 1);
    if (!text) {
        snprintf(reason, reason_size, "out of memory reading manifest");
        return 0;
    }
    memcpy(text, manifest->data, manifest->size);
    text[manifest->size] = '\0';

    found = strstr(text, "abi_version: 1");
    if (!found) {
        snprintf(reason, reason_size, "manifest does not declare abi_version: 1");
    } else if (!strstr(text, "provider_id: ")) {
        snprintf(reason, reason_size, "manifest does not declare provider_id");
    } else if (!strstr(text, "independence_group: ")) {
        snprintf(reason, reason_size, "manifest does not declare independence_group");
    } else if (!strstr(text, "components:")) {
        snprintf(reason, reason_size, "manifest declares no components");
    } else {
        acceptable = 1;
    }
    free(text);
    return acceptable;
}

/* ------------------------------------------------------------------------ */
/* Request framing (stdin)                                                   */
/* ------------------------------------------------------------------------ */

typedef struct {
    unsigned char *component_id;
    size_t component_id_size;
    unsigned char *request;
    size_t request_size;
} worker_request;

/* Returns 1 on a frame, 0 on clean EOF, -1 on a malformed frame. */
static int read_request_frame(worker_request *out) {
    char header[128];
    size_t filled = 0;
    unsigned long long component_len = 0;
    unsigned long long request_len = 0;

    out->component_id = NULL;
    out->request = NULL;
    out->component_id_size = 0;
    out->request_size = 0;

    for (;;) {
        char c;
        ssize_t got = read(STDIN_FILENO, &c, 1);
        if (got == 0) return (filled == 0) ? 0 : -1;
        if (got < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        if (c == '\n') break;
        if (filled + 1 >= sizeof(header)) return -1;
        header[filled++] = c;
    }
    header[filled] = '\0';

    if (sscanf(header, "SCFQ1 %llu %llu", &component_len, &request_len) != 2) return -1;
    if (component_len > WORKER_MAX_FRAME_BYTES || request_len > WORKER_MAX_FRAME_BYTES) return -1;

    out->component_id = (unsigned char *)malloc((size_t)component_len + 1);
    out->request = (unsigned char *)malloc((size_t)request_len + 1);
    if (!out->component_id || !out->request) {
        free(out->component_id);
        free(out->request);
        out->component_id = NULL;
        out->request = NULL;
        return -1;
    }
    if (component_len > 0 && read_all(STDIN_FILENO, out->component_id, (size_t)component_len) != 0) return -1;
    if (request_len > 0 && read_all(STDIN_FILENO, out->request, (size_t)request_len) != 0) return -1;
    out->component_id[component_len] = '\0';
    out->request[request_len] = '\0';
    out->component_id_size = (size_t)component_len;
    out->request_size = (size_t)request_len;
    return 1;
}

static void request_free(worker_request *request) {
    free(request->component_id);
    free(request->request);
    request->component_id = NULL;
    request->request = NULL;
}

/* ------------------------------------------------------------------------ */
/* Child side: run one invocation under rlimits, stream the result out       */
/* ------------------------------------------------------------------------ */

/* Child wire format on the pipe:
 *   int32 call_status, uint64 response_len, response, uint64 trace_len, trace */
static void child_run(const scf_api_v1 *api,
                      scf_instance_v1 *instance,
                      const worker_request *request,
                      const worker_options *options,
                      int pipe_write) {
    byte_buffer response;
    byte_buffer trace;
    scf_writer_v1 response_writer;
    scf_writer_v1 trace_writer;
    scf_slice_v1 component_slice;
    scf_slice_v1 request_slice;
    struct rlimit limit;
    int32_t status;
    uint64_t length;
    const char *stall;

    if (options->cpu_seconds > 0) {
        limit.rlim_cur = (rlim_t)options->cpu_seconds;
        limit.rlim_max = (rlim_t)options->cpu_seconds;
        (void)setrlimit(RLIMIT_CPU, &limit);
    }
    if (options->memory_bytes > 0) {
        limit.rlim_cur = (rlim_t)options->memory_bytes;
        limit.rlim_max = (rlim_t)options->memory_bytes;
        (void)setrlimit(RLIMIT_AS, &limit);
    }
    /* No core files from a deliberately crashing provider. */
    limit.rlim_cur = 0;
    limit.rlim_max = 0;
    (void)setrlimit(RLIMIT_CORE, &limit);

    /* Test seam: stall the CHILD before the adapter call so the PARENT-side
     * wall-clock deadline can be proven without a hanging component in the
     * adapter under test. Never set in production runs. */
    stall = getenv("SCF_WORKER_TEST_STALL_MS");
    if (stall && stall[0] != '\0') {
        long stall_ms = strtol(stall, NULL, 10);
        while (stall_ms > 0) {
            struct timespec sleep_for;
            long slice = (stall_ms > 100) ? 100 : stall_ms;
            sleep_for.tv_sec = slice / 1000;
            sleep_for.tv_nsec = (slice % 1000) * 1000000L;
            (void)nanosleep(&sleep_for, NULL);
            stall_ms -= slice;
        }
    }

    buffer_init(&response, options->max_output_bytes);
    buffer_init(&trace, options->max_output_bytes);
    response_writer.context = &response;
    response_writer.write = buffer_writer_write;
    trace_writer.context = &trace;
    trace_writer.write = buffer_writer_write;

    component_slice.data = request->component_id;
    component_slice.size = (uint64_t)request->component_id_size;
    request_slice.data = request->request;
    request_slice.size = (uint64_t)request->request_size;

    status = api->invoke(instance, component_slice, request_slice,
                         &response_writer, &trace_writer);

    if (response.overflowed || trace.overflowed) {
        /* Output budget blown: exit on a distinguishable code so the parent
         * reports a budget kill rather than a normal completion. */
        _exit(70);
    }

    if (write_all(pipe_write, &status, sizeof(status)) != 0) _exit(71);
    length = (uint64_t)response.size;
    if (write_all(pipe_write, &length, sizeof(length)) != 0) _exit(71);
    if (response.size > 0 && write_all(pipe_write, response.data, response.size) != 0) _exit(71);
    length = (uint64_t)trace.size;
    if (write_all(pipe_write, &length, sizeof(length)) != 0) _exit(71);
    if (trace.size > 0 && write_all(pipe_write, trace.data, trace.size) != 0) _exit(71);

    _exit(0);
}

/* ------------------------------------------------------------------------ */
/* Parent side: supervise one invocation                                     */
/* ------------------------------------------------------------------------ */

static int parent_supervise(pid_t child,
                            int pipe_read,
                            const worker_options *options,
                            const worker_request *request,
                            long long invocation) {
    byte_buffer raw;
    byte_buffer response;
    byte_buffer trace;
    long long started = monotonic_ms();
    long long deadline = started + options->timeout_ms;
    int timed_out = 0;
    int budget_kill = 0;
    int child_status = 0;
    int exit_signal = 0;
    int exit_code = 0;
    int32_t call_status = SCF_INTERNAL;
    long long duration;
    int result;
    char diagnostic[256];

    buffer_init(&raw, 0);
    buffer_init(&response, 0);
    buffer_init(&trace, 0);
    diagnostic[0] = '\0';

    for (;;) {
        struct pollfd descriptor;
        long long remaining = deadline - monotonic_ms();
        int ready;
        unsigned char chunk[8192];
        ssize_t got;

        if (remaining <= 0) {
            timed_out = 1;
            break;
        }
        descriptor.fd = pipe_read;
        descriptor.events = POLLIN;
        descriptor.revents = 0;
        ready = poll(&descriptor, 1, (int)(remaining > 1000 ? 1000 : remaining));
        if (ready < 0) {
            if (errno == EINTR) continue;
            snprintf(diagnostic, sizeof(diagnostic), "poll failed: %s", strerror(errno));
            break;
        }
        if (ready == 0) continue;

        got = read(pipe_read, chunk, sizeof(chunk));
        if (got < 0) {
            if (errno == EINTR) continue;
            snprintf(diagnostic, sizeof(diagnostic), "read failed: %s", strerror(errno));
            break;
        }
        if (got == 0) break; /* child closed the pipe */
        if (options->max_output_bytes > 0 &&
            raw.size + (size_t)got > options->max_output_bytes) {
            budget_kill = 1;
            break;
        }
        (void)buffer_append(&raw, chunk, (size_t)got);
    }

    if (timed_out || budget_kill) {
        kill(child, SIGKILL);
    }
    while (waitpid(child, &child_status, 0) < 0 && errno == EINTR) { /* retry */ }
    close(pipe_read);
    duration = monotonic_ms() - started;

    if (WIFSIGNALED(child_status)) exit_signal = WTERMSIG(child_status);
    if (WIFEXITED(child_status)) exit_code = WEXITSTATUS(child_status);

    /* Budget-driven kills are classified BEFORE crash, because a SIGKILL we
     * sent ourselves is not the provider crashing. */
    if (timed_out) {
        snprintf(diagnostic, sizeof(diagnostic),
                 "wall-clock budget of %ld ms exceeded; child SIGKILLed",
                 options->timeout_ms);
        result = emit_receipt("timed_out",
                              (const char *)request->component_id,
                              request->component_id_size, invocation,
                              SCF_INTERNAL, exit_signal, exit_code, duration,
                              NULL, NULL, diagnostic);
        buffer_free(&raw);
        return result;
    }
    if (budget_kill || (WIFEXITED(child_status) && exit_code == 70)) {
        snprintf(diagnostic, sizeof(diagnostic),
                 "output budget of %lu bytes exceeded; child SIGKILLed",
                 options->max_output_bytes);
        result = emit_receipt("timed_out",
                              (const char *)request->component_id,
                              request->component_id_size, invocation,
                              SCF_INTERNAL, exit_signal, exit_code, duration,
                              NULL, NULL, diagnostic);
        buffer_free(&raw);
        return result;
    }
    if (exit_signal != 0) {
        snprintf(diagnostic, sizeof(diagnostic),
                 "provider terminated by signal %d", exit_signal);
        result = emit_receipt("crashed",
                              (const char *)request->component_id,
                              request->component_id_size, invocation,
                              SCF_INTERNAL, exit_signal, exit_code, duration,
                              NULL, NULL, diagnostic);
        buffer_free(&raw);
        return result;
    }
    if (exit_code != 0) {
        snprintf(diagnostic, sizeof(diagnostic),
                 "provider child exited %d without a result frame", exit_code);
        result = emit_receipt("crashed",
                              (const char *)request->component_id,
                              request->component_id_size, invocation,
                              SCF_INTERNAL, exit_signal, exit_code, duration,
                              NULL, NULL, diagnostic);
        buffer_free(&raw);
        return result;
    }

    /* Decode the child frame. A truncated frame from a cleanly-exited child is
     * still a defect, reported as crashed rather than silently empty. */
    {
        size_t cursor = 0;
        uint64_t response_len = 0;
        uint64_t trace_len = 0;
        int malformed = 0;

        if (raw.size < sizeof(int32_t) + sizeof(uint64_t)) {
            malformed = 1;
        } else {
            memcpy(&call_status, raw.data, sizeof(call_status));
            cursor = sizeof(call_status);
            memcpy(&response_len, raw.data + cursor, sizeof(response_len));
            cursor += sizeof(response_len);
            if (cursor + response_len + sizeof(uint64_t) > raw.size) {
                malformed = 1;
            } else {
                (void)buffer_append(&response, raw.data + cursor, (size_t)response_len);
                cursor += (size_t)response_len;
                memcpy(&trace_len, raw.data + cursor, sizeof(trace_len));
                cursor += sizeof(trace_len);
                if (cursor + trace_len > raw.size) {
                    malformed = 1;
                } else {
                    (void)buffer_append(&trace, raw.data + cursor, (size_t)trace_len);
                }
            }
        }
        if (malformed) {
            snprintf(diagnostic, sizeof(diagnostic),
                     "child produced a truncated result frame (%lu bytes)",
                     (unsigned long)raw.size);
            result = emit_receipt("crashed",
                                  (const char *)request->component_id,
                                  request->component_id_size, invocation,
                                  SCF_INTERNAL, exit_signal, exit_code, duration,
                                  NULL, NULL, diagnostic);
            buffer_free(&raw);
            buffer_free(&response);
            buffer_free(&trace);
            return result;
        }
    }

    result = emit_receipt("executed",
                          (const char *)request->component_id,
                          request->component_id_size, invocation,
                          call_status, exit_signal, exit_code, duration,
                          &response, &trace, "");
    buffer_free(&raw);
    buffer_free(&response);
    buffer_free(&trace);
    return result;
}

/* ------------------------------------------------------------------------ */
/* Option parsing                                                            */
/* ------------------------------------------------------------------------ */

static void options_defaults(worker_options *options) {
    options->adapter_path = NULL;
    options->configuration = "";
    options->timeout_ms = WORKER_DEFAULT_TIMEOUT_MS;
    options->max_output_bytes = WORKER_DEFAULT_MAX_OUTPUT;
    options->max_invocations = WORKER_DEFAULT_MAX_INVOCATIONS;
    options->cpu_seconds = WORKER_DEFAULT_CPU_SECONDS;
    options->memory_bytes = WORKER_DEFAULT_MEMORY_BYTES;
}

static void print_usage(void) {
    fprintf(stderr,
        "usage: simple-counterpart-worker --adapter <library> [options]\n"
        "  --config <sdn>            adapter open() configuration text\n"
        "  --timeout-ms <n>          per-invocation wall-clock budget\n"
        "  --max-output-bytes <n>    per-invocation response+trace budget\n"
        "  --max-invocations <n>     exit after this many requests\n"
        "  --cpu-seconds <n>         per-invocation RLIMIT_CPU\n"
        "  --memory-bytes <n>        per-invocation RLIMIT_AS\n");
}

static int parse_options(int argc, char **argv, worker_options *options) {
    int index;
    options_defaults(options);
    for (index = 1; index < argc; index++) {
        const char *flag = argv[index];
        const char *value = (index + 1 < argc) ? argv[index + 1] : NULL;
        if (strcmp(flag, "--help") == 0) {
            print_usage();
            return -2;
        }
        if (!value) {
            fprintf(stderr, "simple-counterpart-worker: %s needs a value\n", flag);
            return -1;
        }
        if (strcmp(flag, "--adapter") == 0) options->adapter_path = value;
        else if (strcmp(flag, "--config") == 0) options->configuration = value;
        else if (strcmp(flag, "--timeout-ms") == 0) options->timeout_ms = strtol(value, NULL, 10);
        else if (strcmp(flag, "--max-output-bytes") == 0) options->max_output_bytes = strtoul(value, NULL, 10);
        else if (strcmp(flag, "--max-invocations") == 0) options->max_invocations = strtol(value, NULL, 10);
        else if (strcmp(flag, "--cpu-seconds") == 0) options->cpu_seconds = strtol(value, NULL, 10);
        else if (strcmp(flag, "--memory-bytes") == 0) options->memory_bytes = strtoull(value, NULL, 10);
        else {
            fprintf(stderr, "simple-counterpart-worker: unknown flag %s\n", flag);
            return -1;
        }
        index++;
    }
    if (!options->adapter_path) {
        fprintf(stderr, "simple-counterpart-worker: --adapter is required\n");
        return -1;
    }
    if (options->timeout_ms <= 0) options->timeout_ms = WORKER_DEFAULT_TIMEOUT_MS;
    return 0;
}

/* ------------------------------------------------------------------------ */
/* Startup failure receipts                                                  */
/* ------------------------------------------------------------------------ */

static int emit_startup_failure(const char *provider_status, const char *diagnostic) {
    return emit_receipt(provider_status, "", 0, 0, SCF_INTERNAL, 0, 0, 0,
                        NULL, NULL, diagnostic);
}

/* ------------------------------------------------------------------------ */
/* main                                                                      */
/* ------------------------------------------------------------------------ */

int main(int argc, char **argv) {
    worker_options options;
    void *library;
    scf_get_api_fn get_api;
    const scf_api_v1 *api;
    scf_instance_v1 *instance = NULL;
    scf_slice_v1 configuration;
    byte_buffer manifest;
    scf_writer_v1 manifest_writer;
    char reason[256];
    char diagnostic[512];
    long long invocation = 0;
    int32_t status;
    int parsed = parse_options(argc, argv, &options);

    if (parsed == -2) return 0;
    if (parsed != 0) return 2;

    /* A crashing provider must never take the worker's own reporting path with
     * it, and a broken pipe on stdout must not raise SIGPIPE mid-receipt. */
    signal(SIGPIPE, SIG_IGN);

    library = dlopen(options.adapter_path, RTLD_NOW | RTLD_LOCAL);
    if (!library) {
        snprintf(diagnostic, sizeof(diagnostic), "dlopen failed: %s", dlerror());
        emit_startup_failure("unavailable", diagnostic);
        return 3;
    }

    *(void **)(&get_api) = dlsym(library, SCF_GET_API_SYMBOL);
    if (!get_api) {
        snprintf(diagnostic, sizeof(diagnostic),
                 "adapter exports no %s", SCF_GET_API_SYMBOL);
        emit_startup_failure("unavailable", diagnostic);
        return 3;
    }

    api = get_api(SCF_ABI_V1);
    if (!api) {
        emit_startup_failure("rejected_manifest",
                             "adapter does not support requested abi version 1");
        return 4;
    }
    if (api->struct_size < (uint32_t)sizeof(scf_api_v1) ||
        api->abi_version != SCF_ABI_V1) {
        snprintf(diagnostic, sizeof(diagnostic),
                 "adapter table struct_size=%u abi_version=%u; expected >=%u / %u",
                 api->struct_size, api->abi_version,
                 (unsigned)sizeof(scf_api_v1), (unsigned)SCF_ABI_V1);
        emit_startup_failure("rejected_manifest", diagnostic);
        return 4;
    }
    if (!api->manifest || !api->open || !api->invoke || !api->close) {
        emit_startup_failure("rejected_manifest", "adapter table has null entry points");
        return 4;
    }

    buffer_init(&manifest, WORKER_DEFAULT_MAX_OUTPUT);
    manifest_writer.context = &manifest;
    manifest_writer.write = buffer_writer_write;
    status = api->manifest(&manifest_writer);
    if (status != SCF_OK) {
        snprintf(diagnostic, sizeof(diagnostic), "manifest() returned %d", (int)status);
        emit_startup_failure("rejected_manifest", diagnostic);
        buffer_free(&manifest);
        return 4;
    }
    if (!manifest_is_acceptable(&manifest, reason, sizeof(reason))) {
        emit_startup_failure("rejected_manifest", reason);
        buffer_free(&manifest);
        return 4;
    }
    buffer_free(&manifest);

    configuration.data = (const uint8_t *)options.configuration;
    configuration.size = (uint64_t)strlen(options.configuration);
    status = api->open(configuration, &instance);
    if (status != SCF_OK || !instance) {
        snprintf(diagnostic, sizeof(diagnostic), "open() returned %d", (int)status);
        emit_startup_failure("unavailable", diagnostic);
        return 3;
    }

    for (;;) {
        worker_request request;
        int framed;
        int pipes[2];
        pid_t child;

        if (options.max_invocations > 0 && invocation >= options.max_invocations) break;

        framed = read_request_frame(&request);
        if (framed == 0) break;
        if (framed < 0) {
            request_free(&request);
            emit_startup_failure("rejected_manifest", "malformed request frame on stdin");
            break;
        }
        invocation++;

        if (pipe(pipes) != 0) {
            snprintf(diagnostic, sizeof(diagnostic), "pipe failed: %s", strerror(errno));
            (void)emit_receipt("unavailable", (const char *)request.component_id,
                               request.component_id_size, invocation,
                               SCF_INTERNAL, 0, 0, 0, NULL, NULL, diagnostic);
            request_free(&request);
            continue;
        }

        child = fork();
        if (child < 0) {
            close(pipes[0]);
            close(pipes[1]);
            snprintf(diagnostic, sizeof(diagnostic), "fork failed: %s", strerror(errno));
            (void)emit_receipt("unavailable", (const char *)request.component_id,
                               request.component_id_size, invocation,
                               SCF_INTERNAL, 0, 0, 0, NULL, NULL, diagnostic);
            request_free(&request);
            continue;
        }
        if (child == 0) {
            close(pipes[0]);
            child_run(api, instance, &request, &options, pipes[1]);
            _exit(72); /* unreachable */
        }
        close(pipes[1]);
        if (parent_supervise(child, pipes[0], &options, &request, invocation) != 0) {
            request_free(&request);
            break; /* stdout is gone; nothing further can be reported */
        }
        request_free(&request);
    }

    if (api->close) api->close(instance);
    dlclose(library);
    /* Containment: a crashed or timed-out PROVIDER is reported in the receipt
     * and does not make the worker itself fail. */
    return 0;
}
