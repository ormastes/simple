/* Fresh-process resident-mode scenario. Real compiler-rt patches and invokes
 * the actual resident dispatcher; only the Simple cold owner is represented
 * by fixture allocations. This is not Simple-produced metadata or public API
 * qualification. Include after the common ABI helpers in the harness. */
#include "../../../src/runtime/xray/xray_resident_descriptor_v1.h"

int64_t simple_xray_resident_control_enter_v1(void);
void simple_xray_resident_control_leave_v1(void);
void simple_xray_resident_runtime_ready_v1(void);
int64_t simple_xray_llvm_resident_publish_v1(int64_t descriptor);
int64_t simple_xray_llvm_resident_close_v1(void);
int64_t simple_xray_llvm_resident_drained_v1(void);
int64_t simple_xray_thread_task_root_v1(void);
void simple_xray_thread_detach_v1(void);

typedef struct {
    int entry[3], exit[3], transitions, bad;
} resident_counts;

static resident_counts resident_read(int64_t *arena,
        const SimpleXrayResidentBindingV1 *map, int64_t context) {
    resident_counts result = {{0}, {0}, 0, 0};
    int64_t write = __atomic_load_n(&arena[5], __ATOMIC_ACQUIRE);
    for (int64_t at = 0; at < write; ++at) {
        const int64_t *record = arena + 16 + (at % CAPACITY) * 12;
        uint64_t kind = ((uint64_t)record[0] >> 32) & 65535;
        if (((uint64_t)record[0] & UINT32_MAX) != 6291457 ||
            ((uint64_t)record[0] >> 48) != 0 ||
            record[1] != 7 || record[2] != 42 || record[4] != context ||
            record[5] != at + 1 || record[7] != 0 || record[8] != 0 ||
            record[9] != 0 || record[10] != 0 || record[11] != 0) {
            result.bad++;
            continue;
        }
        if (kind == 4) {
            if (at != 0 || record[3] != 0) result.bad++;
            result.transitions++;
            continue;
        }
        int found = -1;
        for (int i = 0; i < 3; ++i)
            if ((uint64_t)record[3] == map[i].function_site) found = i;
        if (found < 0) result.bad++;
        else if (kind == 1) result.entry[found]++;
        else if (kind == 2 || kind == 3) result.exit[found]++;
        else result.bad++;
    }
    return result;
}

static void *resident_patched_worker(void *argument) {
    int *ok = argument;
    *ok = simple_xray_thread_task_root_v1() == 1;
    if (*ok) {
        for (int i = 0; i < 8; ++i)
            if (xray_target_a(i) != i + 1) *ok = 0;
        simple_xray_thread_detach_v1();
    }
    return NULL;
}

static int resident_case(void) {
    int64_t max_id = simple_xray_llvm_max_function_id();
    int32_t ids[3] = {id_of((void *)xray_target_a, max_id),
        id_of((void *)xray_abi_mix, max_id), id_of((void *)xray_abi_sret, max_id)};
    check(max_id == 4 && ids[0] > 0 && ids[1] > 0 && ids[2] > 0,
          "resident: actual emitted function addresses resolve to LLVM IDs");
    if (g_fail) return 1;
    const double expected_mix = mix_call();
    SimpleXrayResidentBindingV1 *map = calloc(3, sizeof(*map));
    SimpleXrayThreadContextHeaderV1 *pool = calloc(1, 128);
    SimpleXrayResidentDescriptorV1 *descriptor = calloc(1, sizeof(*descriptor));
    check(map != NULL && pool != NULL && descriptor != NULL,
          "resident: cold owner allocates retained descriptor and map");
    if (g_fail) return 1;
    for (int i = 0; i < 3; ++i) {
        map[i].llvm_id = (uint64_t)ids[i];
        map[i].function_site = (1000u + (uint64_t)ids[i]) |
            ((2000u + (uint64_t)ids[i]) << 32);
    }
    for (int i = 1; i < 3; ++i) {
        SimpleXrayResidentBindingV1 value = map[i];
        int j = i;
        while (j > 0 && map[j - 1].llvm_id > value.llvm_id) {
            map[j] = map[j - 1]; --j;
        }
        map[j] = value;
    }
    pool->magic = SIMPLE_XRAY_THREAD_CONTEXT_MAGIC_V1;
    pool->schema = 1; pool->actual_bytes = 128; pool->max_slots = 2;
    pool->generation = 7; pool->slots_offset = 64;
    SimpleXrayThreadContextSlotV1 *slots = (void *)((uint8_t *)pool + 64);
    int64_t *arenas[2] = {arena_new(7, 101), arena_new(7, 102)};
    for (int i = 0; i < 2; ++i) {
        slots[i].arena = (uintptr_t)arenas[i];
        slots[i].bytes = 128 + CAPACITY * 96;
        slots[i].context_id = (uint64_t)(101 + i);
    }
    *descriptor = (SimpleXrayResidentDescriptorV1){1, 80, 7, 42,
        (uintptr_t)pool, 128, (uintptr_t)map, 3, 7, 0};
    simple_xray_resident_runtime_ready_v1();
    check(simple_xray_resident_control_enter_v1() == 1, "resident: acquire process control");
    check(simple_xray_llvm_resident_publish_v1((intptr_t)descriptor) == 1,
          "resident: publish real compiler-rt handler with nonidentity canonical IDs");
    check(simple_xray_thread_task_root_v1() == 1, "resident: attach owner TLS context");
    if (g_fail) return 1;
    xray_target_a(5);
    check(arenas[0][5] == 1, "resident: mandatory transition only before patching");
    for (int i = 0; i < 3; ++i)
        check(simple_xray_llvm_patch_function(ids[i]) == 1,
              "resident: real compiler-rt selected-function patch succeeds");
    simple_xray_resident_control_leave_v1();
    if (g_fail) return 1;
    int64_t before = arenas[0][5];
    check(xray_target_b(9) == 27 && arenas[0][5] == before,
          "resident: unselected prepared function computes without events");
    int values_ok = 1;
    for (int i = 0; i < 5; ++i) if (xray_target_a(i) != i + 1) values_ok = 0;
    check(values_ok, "resident: actual patched scalar function results preserved");
    check(mix_call() == expected_mix, "resident ABI-01: eight integer/FP arguments and FP result preserved");
    check(sret_ok(), "resident ABI-01: aggregate result preserved");
    int worker_ok = 0;
    pthread_t worker;
    int created = pthread_create(&worker, NULL, resident_patched_worker, &worker_ok);
    check(created == 0, "resident: create explicitly attached worker after quiescent patch");
    if (created != 0) return 1;
    int joined = pthread_join(worker, NULL);
    check(joined == 0, "resident: join patched worker");
    /* Never inspect worker-owned state or unpatch if termination is unknown. */
    if (joined != 0) return 1;
    check(worker_ok, "resident: real patched calls use worker TLS context");
    resident_counts main_counts = resident_read(arenas[0], map, 101);
    resident_counts worker_counts = resident_read(arenas[1], map, 102);
    int counts_ok = main_counts.bad == 0 && worker_counts.bad == 0 &&
        main_counts.transitions == 1 && worker_counts.transitions == 1;
    for (int i = 0; i < 3; ++i) {
        int is_a = map[i].llvm_id == (uint64_t)ids[0];
        counts_ok &= main_counts.entry[i] == (is_a ? 5 : 1) &&
            main_counts.exit[i] == (is_a ? 5 : 1) &&
            worker_counts.entry[i] == (is_a ? 8 : 0) &&
            worker_counts.exit[i] == (is_a ? 8 : 0);
    }
    check(counts_ok, "resident: exact canonical function/site IDs, per-context sequences and raw edges");
    check(arenas[0][7] == 0 && arenas[1][7] == 0 && pool->unattached_lost == 0,
          "resident: bounded workload has no event loss");
    check(slots[1].state == 2, "resident: worker detach retires its retained slot");
    check(simple_xray_resident_control_enter_v1() == 1, "resident: acquire shutdown control after worker join");
    check(simple_xray_llvm_resident_close_v1() == 1 && simple_xray_llvm_resident_drained_v1() == 1,
          "resident: admission closes and callback reservations drain");
    for (int i = 0; i < 3; ++i)
        check(simple_xray_llvm_unpatch_function(ids[i]) == 1,
              "resident: real unpatch succeeds after all selected calls returned");
    simple_xray_resident_control_leave_v1();
    before = arenas[0][5];
    check(xray_target_a(20) == 21 && mix_call() == expected_mix && sret_ok() && arenas[0][5] == before,
          "resident: closed unpatched targets preserve results without more records");
    simple_xray_thread_detach_v1();
    check(slots[0].state == 2, "resident: owner slot retires without reclaiming storage");
    if (g_fail) printf("FAIL — %d of %d resident check(s) failed\n", g_fail, g_pass + g_fail);
    else printf("PASS — %d check(s), resident compiler-rt path; not Simple facade qualification\n", g_pass);
    return g_fail ? 1 : 0;
}
