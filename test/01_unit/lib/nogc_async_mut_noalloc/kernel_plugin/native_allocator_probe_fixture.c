#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void kpf_noalloc_probe_activate(void);
uint64_t kpf_noalloc_probe_post_activation_allocations(void);

static volatile unsigned char kpf_sink;

typedef struct {
    unsigned char session_slots[4];
    unsigned char request_slots[8];
    size_t open_sessions;
    size_t inflight_requests;
} strict_kpf_runtime;

static int strict_kpf_open_session(strict_kpf_runtime *runtime, size_t slot) {
    if (slot >= sizeof(runtime->session_slots) || runtime->session_slots[slot] != 0) {
        return 0;
    }
    runtime->session_slots[slot] = 1;
    runtime->open_sessions += 1;
    return 1;
}

static int strict_kpf_submit(strict_kpf_runtime *runtime, size_t slot) {
    if (slot >= sizeof(runtime->request_slots) || runtime->request_slots[slot] != 0) {
        return 0;
    }
    runtime->request_slots[slot] = 1;
    runtime->inflight_requests += 1;
    return 1;
}

static void strict_kpf_complete_and_close(strict_kpf_runtime *runtime) {
    runtime->request_slots[0] = 0;
    runtime->session_slots[0] = 0;
    runtime->inflight_requests -= 1;
    runtime->open_sessions -= 1;
    kpf_sink = (unsigned char)(runtime->open_sessions + runtime->inflight_requests);
}

static int strict_kpf_stack_only_work(void) {
    strict_kpf_runtime runtime = {0};
    if (!strict_kpf_open_session(&runtime, 0) || !strict_kpf_submit(&runtime, 0)) {
        return 0;
    }
    strict_kpf_complete_and_close(&runtime);
    return runtime.open_sessions == 0 && runtime.inflight_requests == 0;
}

static void mutation_allocate_after_activation(void) {
    void *memory = malloc(32);
    if (memory != NULL) {
        memset(memory, 0x5a, 32);
        kpf_sink = ((unsigned char *)memory)[0];
    }
    free(memory);
}

int main(int argc, char **argv) {
    int mutate = argc == 2 && strcmp(argv[1], "--mutate") == 0;
    kpf_noalloc_probe_activate();
    if (!strict_kpf_stack_only_work()) {
        return 24;
    }
    if (mutate) {
        mutation_allocate_after_activation();
    }
    return kpf_noalloc_probe_post_activation_allocations() == 0 ? 0 : 23;
}
