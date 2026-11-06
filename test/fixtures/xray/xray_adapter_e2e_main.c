/*
 * XRay PR4 end-to-end harness (test-only). Drives the C boundary
 * src/runtime/xray/xray_llvm_adapter_linux.c in the order the Simple control
 * plane (xray_llvm_adapter_v1.spl) uses: max id -> install -> patch selected
 * -> ... -> unpatch. It stands in for the Simple caller only because no
 * pure-Simple compiler that can emit `--xray` binaries is deployed.
 *
 * The arena initialization and the reader below mirror
 * trace_native_channel_initialize_v1 / trace_native_channel_poll_into_v1
 * (observer_native_channel_v1.spl) so the C producer is checked against the
 * channel layout the Simple consumer reads.
 *
 * Build: harness and adapter WITHOUT -fxray-instrument; the targets object
 * from xray_adapter_targets.ll; link with -fxray-instrument (pulls
 * libclang_rt.xray) and -Wl,--wrap=mprotect (failure injection).
 * Output: one "PASS <name>" / "FAIL <name>" per check, then a verdict line.
 */
#include <errno.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <xray/xray_interface.h>

int64_t simple_xray_llvm_max_function_id(void);
int64_t simple_xray_llvm_install(int64_t arena, int64_t generation, int64_t context,
                                 int64_t module_instance);
int64_t simple_xray_llvm_patch_function(int64_t id);
int64_t simple_xray_llvm_unpatch_function(int64_t id);

typedef struct {
    int64_t w[4];
} xray_quad;
int64_t xray_target_a(int64_t x);
int64_t xray_target_b(int64_t x);
double xray_abi_mix(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t,
                    double, double, double, double, double, double, double, double);
xray_quad xray_abi_sret(int64_t x);
int64_t xray_never_fn(int64_t x);

/* ---- mprotect failure injection (wraps compiler-rt's libc mprotect call) */
int __real_mprotect(void *addr, size_t len, int prot);
static int g_fail_mprotect;
static int g_mprotect_calls;
int __wrap_mprotect(void *addr, size_t len, int prot) {
    g_mprotect_calls++;
    if (g_fail_mprotect) {
        errno = EACCES;
        return -1;
    }
    return __real_mprotect(addr, len, prot);
}

/* ---- checks */
static int g_pass, g_fail;
static void check(int ok, const char *name) {
    printf("%s %s\n", ok ? "PASS" : "FAIL", name);
    if (ok) g_pass++;
    else g_fail++;
}

/* ---- observer_native_channel_v1 arena (header 16 words, 12-word records) */
#define CAPACITY 256
static int64_t *arena_new(int64_t generation, int64_t context) {
    size_t bytes = (size_t)(128 + CAPACITY * 96);
    int64_t *base = aligned_alloc(64, bytes); /* resident until exit, by contract */
    memset(base, 0, bytes);
    base[1] = generation;
    base[2] = context;
    base[3] = CAPACITY;
    base[9] = (int64_t)bytes;
    return base;
}

typedef struct {
    int64_t entry, exit, other, bad;
} counts_t;

/* Drain all published records; count per function id. */
static counts_t drain(int64_t *base, int32_t want_id, int64_t generation) {
    counts_t c = {0, 0, 0, 0};
    for (;;) {
        int64_t read = __atomic_load_n(&base[6], __ATOMIC_SEQ_CST);
        int64_t write = __atomic_load_n(&base[5], __ATOMIC_SEQ_CST);
        if (read == write) break;
        int64_t *slot = base + 16 + (read % CAPACITY) * 12;
        uint64_t header = (uint64_t)slot[0];
        uint64_t kind = (header >> 32) & 0xffff;
        uint64_t fn = (uint64_t)slot[3] & 0xffffffffu;
        uint64_t site = (uint64_t)slot[3] >> 32;
        if ((header & 0xffffffffu) != 6291457u || slot[1] != generation || slot[2] != 1 ||
            slot[4] != 1 || fn != site || slot[7] != 0 || slot[11] != 0)
            c.bad++;
        else if ((int32_t)fn == want_id && kind == 1)
            c.entry++;
        else if ((int32_t)fn == want_id && (kind == 2 || kind == 3))
            c.exit++;
        else
            c.other++;
        __atomic_store_n(&base[6], read + 1, __ATOMIC_SEQ_CST);
    }
    return c;
}

static int32_t id_of(void *fn, int64_t max_id) {
    for (int32_t id = 1; id <= max_id; id++)
        if (__xray_function_address(id) == (uintptr_t)fn) return id;
    return 0;
}

/* ---- ABI-02 adversarial (conforming) handler: clobbers every register the
 * ABI lets a callee clobber, then returns. Test-only inline asm. */
__attribute__((xray_never_instrument, noinline)) static void adversarial_handler(
    int32_t fid, enum XRayEntryType type) {
    (void)fid;
    (void)type;
#if defined(__aarch64__)
    __asm__ volatile(
        "movi v0.2d, #0xffffffffffffffff\n movi v1.2d, #0xffffffffffffffff\n"
        "movi v2.2d, #0xffffffffffffffff\n movi v3.2d, #0xffffffffffffffff\n"
        "movi v4.2d, #0xffffffffffffffff\n movi v5.2d, #0xffffffffffffffff\n"
        "movi v6.2d, #0xffffffffffffffff\n movi v7.2d, #0xffffffffffffffff\n"
        "movi v16.2d, #0xffffffffffffffff\n movi v31.2d, #0xffffffffffffffff\n"
        "mov x0, #-1\n mov x1, #-1\n mov x2, #-1\n mov x3, #-1\n mov x4, #-1\n"
        "mov x5, #-1\n mov x6, #-1\n mov x7, #-1\n mov x8, #-1\n mov x9, #-1\n"
        "mov x10, #-1\n mov x11, #-1\n mov x12, #-1\n mov x13, #-1\n mov x14, #-1\n"
        "mov x15, #-1\n mov x16, #-1\n mov x17, #-1\n"
        "cmn x9, #1\n" /* clobber NZCV */
        ::: "v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v16", "v31", "x0", "x1", "x2",
        "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15",
        "x16", "x17", "cc", "memory");
#elif defined(__x86_64__)
    __asm__ volatile(
        "pcmpeqd %%xmm0, %%xmm0\n pcmpeqd %%xmm1, %%xmm1\n pcmpeqd %%xmm2, %%xmm2\n"
        "pcmpeqd %%xmm3, %%xmm3\n pcmpeqd %%xmm4, %%xmm4\n pcmpeqd %%xmm5, %%xmm5\n"
        "pcmpeqd %%xmm6, %%xmm6\n pcmpeqd %%xmm7, %%xmm7\n pcmpeqd %%xmm8, %%xmm8\n"
        "pcmpeqd %%xmm15, %%xmm15\n"
        "mov $-1, %%rax\n mov $-1, %%rcx\n mov $-1, %%rdx\n mov $-1, %%rsi\n"
        "mov $-1, %%rdi\n mov $-1, %%r8\n mov $-1, %%r9\n mov $-1, %%r10\n mov $-1, %%r11\n"
        "cmp $0, %%rax\n"
        ::: "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm15",
        "rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "cc", "memory");
#endif
}

#define HAMMER_CALLS 20000
static void *hammer(void *arg) {
    (void)arg;
    for (int i = 0; i < HAMMER_CALLS; i++) xray_target_a(i);
    return NULL;
}

static double mix_call(void) {
    return xray_abi_mix(1, 2, 3, 4, 5, 6, 7, 8, 0.5, 1.5, 2.5, 3.5, 4.5, 5.5, 6.5, 7.5);
}
static int sret_ok(void) {
    xray_quad q = xray_abi_sret(40);
    return q.w[0] == 40 && q.w[1] == 41 && q.w[2] == 42 && q.w[3] == 43;
}

int main(void) {
    int64_t max_id = simple_xray_llvm_max_function_id();
    int32_t id_a = id_of((void *)xray_target_a, max_id);
    int32_t id_b = id_of((void *)xray_target_b, max_id);
    int32_t id_mix = id_of((void *)xray_abi_mix, max_id);
    int32_t id_sret = id_of((void *)xray_abi_sret, max_id);
    int32_t id_never = id_of((void *)xray_never_fn, max_id);
    printf("INFO max_function_id=%lld a=%d b=%d mix=%d sret=%d never=%d\n", (long long)max_id,
           id_a, id_b, id_mix, id_sret, id_never);
    check(max_id == 4, "map holds exactly the four xray-always functions");
    check(id_a > 0 && id_b > 0 && id_mix > 0 && id_sret > 0 && id_never == 0,
          "never-listed function has no id; sled functions resolve");

    const double mix_expect = mix_call();
    int64_t *gen1 = arena_new(1, 1);

    /* Fail closed on bad arenas, unknown ids. */
    int64_t *wrong = arena_new(9, 1);
    check(simple_xray_llvm_install((int64_t)(intptr_t)wrong, 1, 1, 1) == 0,
          "install refuses an arena of another generation");
    check(simple_xray_llvm_patch_function(0) == -1, "patch id 0 rejected");
    check(simple_xray_llvm_patch_function(max_id + 1) == -1, "patch id max+1 rejected");
    check(simple_xray_llvm_unpatch_function(max_id + 1) == -1, "unpatch id max+1 rejected");

    check(simple_xray_llvm_install((int64_t)(intptr_t)gen1, 1, 1, 1) == 1, "install generation 1");
    /* Quiescent start: handler and arena published, nothing patched yet
     * (XRAY_OPTIONS=patch_premain=false) -> every sled is a taken branch. */
    xray_target_a(1);
    xray_target_b(1);
    counts_t cq = drain(gen1, id_a, 1);
    check(cq.entry == 0 && cq.exit == 0 && cq.other == 0,
          "installed but unpatched: nothing fires");
    check(simple_xray_llvm_patch_function(id_a) == 1, "patch A only (aspect-selected)");
    for (int i = 0; i < 3; i++) {
        xray_target_a(i);
        xray_target_b(i);
    }
    counts_t ca = drain(gen1, id_a, 1);
    printf("INFO patched-A: entry=%lld exit=%lld other=%lld bad=%lld\n", (long long)ca.entry,
           (long long)ca.exit, (long long)ca.other, (long long)ca.bad);
    check(ca.entry == 3 && ca.exit == 3 && ca.other == 0 && ca.bad == 0,
          "A fires entry+exit 3x; unselected B is silent");

    check(simple_xray_llvm_unpatch_function(id_a) == 1, "unpatch A");
    xray_target_a(7);
    counts_t cu = drain(gen1, id_a, 1);
    check(cu.entry == 0 && cu.exit == 0 && cu.other == 0, "after unpatch nothing fires");

    check(simple_xray_llvm_patch_function(id_a) == 1, "re-patch A");
    xray_target_a(8);
    counts_t cr = drain(gen1, id_a, 1);
    check(cr.entry == 1 && cr.exit == 1 && cr.bad == 0, "re-patched A fires again");
    simple_xray_llvm_unpatch_function(id_a);

    /* mprotect failure: compiler-rt reports FAILED, no crash, A stays off. */
    g_fail_mprotect = 1;
    int before = g_mprotect_calls;
    int64_t st = simple_xray_llvm_patch_function(id_b);
    g_fail_mprotect = 0;
    printf("INFO injected-mprotect-failure status=%lld mprotect_calls=%d\n", (long long)st,
           g_mprotect_calls - before);
    check(st == 3 && g_mprotect_calls > before, "failed mprotect -> FAILED status, no crash");
    xray_target_b(2);
    check(drain(gen1, id_b, 1).entry == 0, "function whose patch failed does not fire");
    check(xray_target_b(5) == 15, "function whose patch failed still computes correctly");
    check(simple_xray_llvm_patch_function(id_b) == 1, "patch succeeds once mprotect recovers");
    check(simple_xray_llvm_unpatch_function(id_b) == 1, "unpatch B");

    /* ABI-01 through the product handler. */
    check(simple_xray_llvm_patch_function(id_mix) == 1 &&
              simple_xray_llvm_patch_function(id_sret) == 1,
          "patch ABI functions");
    double got = mix_call();
    check(got == mix_expect, "ABI-01: 8 int + 8 FP args and FP return preserved");
    check(sret_ok(), "ABI-01: sret aggregate preserved");
    counts_t cm = drain(gen1, id_mix, 1);
    check(cm.entry == 1 && cm.exit == 1, "ABI function events recorded");

    /* ABI-02: adversarial conforming handler on the same sleds. */
    check(__xray_set_handler(adversarial_handler) == 1, "install adversarial handler");
    got = mix_call();
    printf("INFO abi02 mix got=%.17g expect=%.17g\n", got, mix_expect);
    check(got == mix_expect, "ABI-02: args/return survive an adversarial handler");
    check(sret_ok(), "ABI-02: sret survives an adversarial handler");
    simple_xray_llvm_unpatch_function(id_mix);
    simple_xray_llvm_unpatch_function(id_sret);

    /* New generation re-install (per-function toggle = new selection). */
    int64_t *gen2 = arena_new(2, 1);
    check(simple_xray_llvm_install((int64_t)(intptr_t)gen2, 2, 1, 1) == 1, "install generation 2");
    check(simple_xray_llvm_patch_function(id_b) == 1, "patch B in generation 2");
    xray_target_a(1);
    xray_target_b(1);
    counts_t g2 = drain(gen2, id_b, 2);
    check(g2.entry == 1 && g2.exit == 1 && g2.other == 0 && g2.bad == 0,
          "generation 2 selection: B fires, A silent");
    check(simple_xray_llvm_unpatch_function(id_b) == 1, "unpatch B");

    /* Closed channel: a late callback after close is not recorded. */
    check(simple_xray_llvm_patch_function(id_a) == 1, "patch A for close test");
    xray_target_a(1);
    counts_t co = drain(gen2, id_a, 2);
    check(co.entry == 1 && co.exit == 1, "patched A records while the channel is open");
    __atomic_store_n(&gen2[0], 2, __ATOMIC_SEQ_CST);
    xray_target_a(1);
    counts_t cc = drain(gen2, id_a, 2);
    check(cc.entry == 0 && cc.exit == 0 && gen2[7] == 0, "closed channel admits nothing, no loss");
    simple_xray_llvm_unpatch_function(id_a);

    /* Full ring: bounded, counts loss, never overwrites unread records. */
    int64_t *gen3 = arena_new(3, 1);
    check(simple_xray_llvm_install((int64_t)(intptr_t)gen3, 3, 1, 1) == 1, "install generation 3");
    check(simple_xray_llvm_patch_function(id_a) == 1, "patch A for ring-full test");
    for (int i = 0; i < 200; i++) xray_target_a(i);
    counts_t cf = drain(gen3, id_a, 3);
    printf("INFO ring-full: recorded=%lld lost=%lld inexact=%lld\n", (long long)(cf.entry + cf.exit),
           (long long)gen3[7], (long long)gen3[8]);
    check(cf.entry + cf.exit == CAPACITY && gen3[7] == 400 - CAPACITY && gen3[8] == 0,
          "ring full: capacity records kept, exact loss for the rest");
    simple_xray_llvm_unpatch_function(id_a);

    /* Two producers on one channel: the gate CAS admits one at a time; a
     * contended producer counts loss. Every edge is recorded or counted. */
    int64_t *gen4 = arena_new(4, 1);
    check(simple_xray_llvm_install((int64_t)(intptr_t)gen4, 4, 1, 1) == 1, "install generation 4");
    check(simple_xray_llvm_patch_function(id_a) == 1, "patch A for contention test");
    pthread_t t1, t2;
    pthread_create(&t1, NULL, hammer, NULL);
    pthread_create(&t2, NULL, hammer, NULL);
    pthread_join(t1, NULL);
    pthread_join(t2, NULL);
    counts_t ct = drain(gen4, id_a, 4);
    long long edges = 2LL * 2 * HAMMER_CALLS;
    printf("INFO contention: recorded=%lld lost=%lld inexact=%lld edges=%lld\n",
           (long long)(ct.entry + ct.exit), (long long)gen4[7], (long long)gen4[8], edges);
    check(ct.bad == 0 && ct.other == 0 &&
              (gen4[8] != 0 ? ct.entry + ct.exit + gen4[7] <= edges
                            : ct.entry + ct.exit + gen4[7] == edges),
          "contention: every edge recorded or counted lost, no torn record");
    check(gen4[0] == 0, "contention: gate released (no producer left holding it)");
    simple_xray_llvm_unpatch_function(id_a);

    if (g_fail == 0)
        printf("PASS — %d check(s), handler fires for patched functions only\n", g_pass);
    else
        printf("FAIL — %d of %d check(s) failed\n", g_fail, g_pass + g_fail);
    return g_fail == 0 ? 0 : 1;
}
