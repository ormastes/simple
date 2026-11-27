/* XRay PR5 native AArch64 e2e harness.
 *
 * Replays, on a REAL mmap'd code page of this host, the exact patch operations
 * the pure-Simple patcher (XrayNativeSledLeafV1 under XrayLlvmAdapterV1)
 * decided in test/fixtures/xray/xray_native_e2e_driver.spl, and executes the
 * emitter-produced function between them. It makes no patch decision itself.
 *
 * Ops (one per line, offsets relative to the image base):
 *   func <off> | tramp_lit <off> | sites <n> | site <id> <off> <kind>
 *   protect                     page 0 RX + I-cache sync, page 1 R
 *   begin <off> <len>           RX -> RW            (mirrors rt_mprotect)
 *   store <off> <word>          aligned 32-bit single-copy-atomic store
 *   end <off> <len>             RW -> RX + __builtin___clear_cache
 *                               (DC CVAU/DSB/IC IVAU/DSB/ISB on AArch64)
 *   word <off> <expected>       current instruction word must equal
 *   call <arg> <ret> <count> <last>
 *                               call the function; check its result, the
 *                               trampoline hit counter and last site id
 * Verdict (last line): PASS — <n> check(s) | FAIL — <reason>.
 * Usage: harness <image.hex> <ops.txt>
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#define PAGE 4096

static volatile uint64_t counters[2]; /* [0] hits, [1] last site id */
static unsigned char *base;
static int checks;

static int fail(const char *what, long a, long b) {
    printf("FAIL — %s (got %ld, want %ld)\n", what, a, b);
    return 1;
}

static int load_image(const char *path, size_t *size) {
    FILE *f = fopen(path, "r");
    if (!f) return -1;
    size_t n = 0;
    int hi, lo;
    while ((hi = fgetc(f)) != EOF && (lo = fgetc(f)) != EOF) {
        if (hi == '\n') break;
        char pair[3] = {(char)hi, (char)lo, 0};
        if (n >= 2 * PAGE) { fclose(f); return -1; }
        base[n++] = (unsigned char)strtoul(pair, NULL, 16);
    }
    fclose(f);
    *size = n;
    return 0;
}

static int sync_rx(unsigned char *page, long len) {
    if (mprotect(page, (size_t)len, PROT_READ | PROT_EXEC) != 0) return -1;
    __builtin___clear_cache((char *)page, (char *)page + len);
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 3) { printf("FAIL — usage\n"); return 1; }
    base = mmap(NULL, 2 * PAGE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (base == MAP_FAILED) { printf("FAIL — mmap\n"); return 1; }
    size_t size = 0;
    if (load_image(argv[1], &size) != 0 || size <= PAGE) { printf("FAIL — image\n"); return 1; }
    FILE *ops = fopen(argv[2], "r");
    if (!ops) { printf("FAIL — ops\n"); return 1; }
    long func_off = -1;
    char line[256];
    while (fgets(line, sizeof line, ops)) {
        char op[32];
        long a = 0, b = 0, c = 0, d = 0;
        int n = sscanf(line, "%31s %ld %ld %ld %ld", op, &a, &b, &c, &d);
        if (n < 1) continue;
        if (!strcmp(op, "func")) {
            func_off = a;
        } else if (!strcmp(op, "tramp_lit")) {
            uint64_t addr = (uint64_t)(uintptr_t)counters;
            memcpy(base + a, &addr, sizeof addr);
        } else if (!strcmp(op, "sites") || !strcmp(op, "site")) {
            /* informational */
        } else if (!strcmp(op, "protect")) {
            if (sync_rx(base, PAGE) != 0 || mprotect(base + PAGE, PAGE, PROT_READ) != 0)
                return fail("initial RX/R protection", -1, 0);
        } else if (!strcmp(op, "begin")) {
            if (mprotect(base + a, (size_t)b, PROT_READ | PROT_WRITE) != 0) return fail("begin mprotect RW", -1, 0);
        } else if (!strcmp(op, "store")) {
            if (a % 4 != 0) return fail("misaligned store", a, 0);
            __atomic_store_n((uint32_t *)(base + a), (uint32_t)b, __ATOMIC_RELAXED);
        } else if (!strcmp(op, "end")) {
            if (sync_rx(base + a, b) != 0) return fail("end mprotect RX + cache sync", -1, 0);
        } else if (!strcmp(op, "word")) {
            uint32_t w = *(volatile uint32_t *)(base + a);
            printf("word +%ld = 0x%08x\n", a, w);
            if ((long)w != b) return fail("sled word", (long)w, b);
            checks++;
        } else if (!strcmp(op, "call")) {
            if (func_off < 0) return fail("call before func", 0, 0);
            int64_t (*fn)(int64_t) = (int64_t (*)(int64_t))(uintptr_t)(base + func_off);
            int64_t r = fn(a);
            printf("call(%ld) = %ld, hits = %lu, last site = %lu\n", a, (long)r,
                   (unsigned long)counters[0], (unsigned long)counters[1]);
            if (r != b) return fail("return value", (long)r, b);
            if ((long)counters[0] != c) return fail("trampoline hits", (long)counters[0], c);
            if ((long)counters[1] != d) return fail("last site id", (long)counters[1], d);
            checks += 3;
        } else {
            return fail("unknown op", 0, 0);
        }
    }
    fclose(ops);
    if (checks == 0) { printf("FAIL — no checks ran\n"); return 1; }
    printf("PASS — %d check(s)\n", checks);
    return 0;
}
