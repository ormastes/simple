// Executes the pure-Simple x86 backend output written by
// x86_avx512_exec_dump_spec.spl (SIMPLE_AVX512_EXEC_DUMP): each group is
// built once with AVX-512 admitted ("avx") and once with the scalar
// fallback ("scalar"). Every run is checked byte for byte against the
// independent C reference below, and every avx/scalar pair against each
// other. On a host without AVX-512 only the scalar builds run.
// Driven by run_x86_avx512_exec.shs; exit 0 only when nothing differs.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <limits.h>
#ifdef _WIN32
#include <windows.h>
static unsigned char* exec_alloc(size_t n) { return VirtualAlloc(NULL, n, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE); }
static void exec_free(unsigned char* p, size_t n) { (void)n; VirtualFree(p, 0, MEM_RELEASE); }
#else
#include <sys/mman.h>
static unsigned char* exec_alloc(size_t n) {
    void* p = mmap(NULL, n, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    return p == MAP_FAILED ? NULL : p;
}
static void exec_free(unsigned char* p, size_t n) { munmap(p, n); }
#endif

// The native backend uses the SysV integer argument registers on every host.
typedef void (__attribute__((sysv_abi)) *fn3)(void*, void*, void*);

static unsigned char A[128], B[128];
static unsigned char OUTBUF[256];
static int refchecked = 0, refbad = 0;

static void fill(unsigned char* dst, const char* tag) {
    memset(dst, 0, 128);
    if (!strcmp(tag, "f32")) {
        float v[16] = {1.5f, -2.0f, 0.0f, -0.0f, 3.25f, NAN, INFINITY, -INFINITY, 1e-3f, 100.0f, -7.5f, 2.0f, 0.5f, 1e30f, -1e-30f, 42.0f};
        memcpy(dst, v, 64);
    } else if (!strcmp(tag, "f32b")) {
        float v[16] = {2.0f, -2.0f, -0.0f, 0.0f, 3.25f, 1.0f, -INFINITY, -INFINITY, NAN, 0.25f, 8.0f, -3.0f, 0.5f, 1e-30f, 5.0f, 41.0f};
        memcpy(dst, v, 64);
    } else if (!strcmp(tag, "f64")) {
        double v[8] = {1.5, -2.0, -0.0, NAN, INFINITY, 1e-300, 7.25, 3.0};
        memcpy(dst, v, 64);
    } else if (!strcmp(tag, "f64b")) {
        double v[8] = {2.0, -2.0, 0.0, 1.0, INFINITY, 1e300, NAN, 3.0};
        memcpy(dst, v, 64);
    } else if (!strcmp(tag, "i32")) {
        int32_t v[16] = {5, -3, 0, INT_MIN, INT_MAX, 7, -7, 100, 1, -1, 12345, -98765, 3, 3, 0x0F0F0F0F, -2};
        memcpy(dst, v, 64);
    } else if (!strcmp(tag, "i32b")) {
        int32_t v[16] = {5, 3, -1, 1, INT_MAX, -7, -7, 99, 2, -2, 54321, 98765, 4, 3, 0x00FF00FF, 2};
        memcpy(dst, v, 64);
    } else if (!strcmp(tag, "shift")) {
        int32_t v[16] = {0, 1, 2, 3, 4, 5, 7, 8, 15, 16, 17, 24, 30, 31, 1, 9};
        memcpy(dst, v, 64);
    } else if (!strcmp(tag, "perm_f32") || !strcmp(tag, "perm_i32")) {
        int32_t v[16] = {3, 0, 15, 7, 7, 1, 2, 14, 8, 9, 10, 11, 4, 5, 6, 13};
        memcpy(dst, v, 64);
    } else if (!strcmp(tag, "perm_f64")) {
        int32_t v[8] = {7, 0, 3, 3, 1, 6, 2, 5};
        memcpy(dst, v, 32);
    } else {
        fprintf(stderr, "unknown tag %s\n", tag);
        exit(2);
    }
}

// Independent C reference for each group: fills exp[0..192) (out buffer)
// and expb[0..8) (b buffer); returns 0 when the group has no reference.
static int sse_lt_f(float a, float b) { return a < b; }
static float smin_f(float a, float b) { return sse_lt_f(a, b) ? a : b; }
static float smax_f(float a, float b) { return (a > b) ? a : b; }
static double smin_d(double a, double b) { return (a < b) ? a : b; }
static double smax_d(double a, double b) { return (a > b) ? a : b; }

static int pred_f(const char* op, double a, double b) {
    if (!strcmp(op, "Eq")) return a == b;
    if (!strcmp(op, "Ne")) return !(a == b);
    if (!strcmp(op, "Lt")) return a < b;
    if (!strcmp(op, "Le")) return a <= b;
    if (!strcmp(op, "Gt")) return a > b;
    return a >= b;
}
static int pred_i(const char* op, int32_t a, int32_t b) {
    if (!strcmp(op, "Eq")) return a == b;
    if (!strcmp(op, "Ne")) return a != b;
    if (!strcmp(op, "Lt")) return a < b;
    if (!strcmp(op, "Le")) return a <= b;
    if (!strcmp(op, "Gt")) return a > b;
    return a >= b;
}

static int reference(const char* group, const unsigned char* A0, const unsigned char* B0, unsigned char* exp, unsigned char* expb) {
    char kind[32] = "", op[32] = "", shape[16] = "";
    char tmp[128]; strcpy(tmp, group);
    char* parts[4]; int np = 0;
    for (char* t = strtok(tmp, "_"); t && np < 4; t = strtok(NULL, "_")) parts[np++] = t;
    strcpy(kind, parts[0]);
    if (np == 3) { strcpy(op, parts[1]); strcpy(shape, parts[2]); } else { strcpy(shape, parts[1]); }
    memset(exp, 0xCC, 192); memcpy(expb, B0, 8);
    int n = !strcmp(shape, "f64") ? 8 : 16;
    const float* af = (const float*)A0; const float* bf = (const float*)B0;
    const double* ad = (const double*)A0; const double* bd = (const double*)B0;
    const int32_t* ai = (const int32_t*)A0; const int32_t* bi = (const int32_t*)B0;
    float* of = (float*)exp; double* od = (double*)exp; int32_t* oi = (int32_t*)exp;
    volatile float vf; volatile double vd;
    if (!strcmp(kind, "bin")) {
        for (int i = 0; i < n; i++) {
            if (!strcmp(shape, "f32")) {
                float x = af[i], y = bf[i];
                if (!strcmp(op, "Add")) vf = x + y; else if (!strcmp(op, "Sub")) vf = x - y; else if (!strcmp(op, "Mul")) vf = x * y;
                else if (!strcmp(op, "Div")) vf = x / y; else if (!strcmp(op, "Min")) vf = smin_f(x, y); else vf = smax_f(x, y);
                of[i] = vf;
            } else if (!strcmp(shape, "f64")) {
                double x = ad[i], y = bd[i];
                if (!strcmp(op, "Add")) vd = x + y; else if (!strcmp(op, "Sub")) vd = x - y; else if (!strcmp(op, "Mul")) vd = x * y;
                else if (!strcmp(op, "Div")) vd = x / y; else if (!strcmp(op, "Min")) vd = smin_d(x, y); else vd = smax_d(x, y);
                od[i] = vd;
            } else {
                uint32_t x = ai[i], y = bi[i];
                int32_t sx = ai[i], sy = bi[i];
                uint32_t r;
                if (!strcmp(op, "Add")) r = x + y; else if (!strcmp(op, "Sub")) r = x - y; else if (!strcmp(op, "Mul")) r = x * y;
                else if (!strcmp(op, "Min")) r = sx < sy ? x : y; else if (!strcmp(op, "Max")) r = sx > sy ? x : y;
                else if (!strcmp(op, "And")) r = x & y; else if (!strcmp(op, "Or")) r = x | y; else if (!strcmp(op, "Xor")) r = x ^ y;
                else if (!strcmp(op, "Andnot")) r = ~x & y; else if (!strcmp(op, "Shl")) r = x << y;
                else if (!strcmp(op, "ShrLogical")) r = x >> y; else r = (uint32_t)(sx >> sy);
                oi[i] = (int32_t)r;
            }
        }
        return 1;
    }
    if (!strcmp(kind, "un")) {
        for (int i = 0; i < n; i++) {
            if (!strcmp(shape, "i32")) { oi[i] = !strcmp(op, "Neg") ? (int32_t)(0u - (uint32_t)ai[i]) : ~ai[i]; continue; }
            if (!strcmp(shape, "f32")) {
                uint32_t bits; memcpy(&bits, &af[i], 4);
                if (!strcmp(op, "Neg")) { bits ^= 0x80000000u; memcpy(&of[i], &bits, 4); }
                else if (!strcmp(op, "Abs")) { bits &= 0x7FFFFFFFu; memcpy(&of[i], &bits, 4); }
                else if (!strcmp(op, "Sqrt")) { vf = sqrtf(af[i]); of[i] = vf; }
                else if (!strcmp(op, "Recip")) { vf = 1.0f / af[i]; of[i] = vf; }
                else { vf = sqrtf(af[i]); vf = 1.0f / vf; of[i] = vf; }
            } else {
                uint64_t bits; memcpy(&bits, &ad[i], 8);
                if (!strcmp(op, "Neg")) { bits ^= 0x8000000000000000ull; memcpy(&od[i], &bits, 8); }
                else if (!strcmp(op, "Abs")) { bits &= 0x7FFFFFFFFFFFFFFFull; memcpy(&od[i], &bits, 8); }
                else if (!strcmp(op, "Sqrt")) { vd = sqrt(ad[i]); od[i] = vd; }
                else if (!strcmp(op, "Recip")) { vd = 1.0 / ad[i]; od[i] = vd; }
                else { vd = sqrt(ad[i]); vd = 1.0 / vd; od[i] = vd; }
            }
        }
        return 1;
    }
    if (!strcmp(kind, "red")) {
        uint64_t result = 0;
        if (!strcmp(shape, "f32")) {
            float acc = af[0];
            for (int i = 1; i < 16; i++) { if (!strcmp(op, "Sum")) { vf = acc + af[i]; acc = vf; } else if (!strcmp(op, "Min")) acc = smin_f(acc, af[i]); else acc = smax_f(acc, af[i]); }
            uint32_t bits; memcpy(&bits, &acc, 4); result = bits;
        } else if (!strcmp(shape, "f64")) {
            double acc = ad[0];
            for (int i = 1; i < 8; i++) { if (!strcmp(op, "Sum")) { vd = acc + ad[i]; acc = vd; } else if (!strcmp(op, "Min")) acc = smin_d(acc, ad[i]); else acc = smax_d(acc, ad[i]); }
            memcpy(&result, &acc, 8);
        } else {
            int32_t acc = ai[0];
            for (int i = 1; i < 16; i++) {
                if (!strcmp(op, "Sum")) acc = (int32_t)((uint32_t)acc + (uint32_t)ai[i]);
                else if (!strcmp(op, "Min")) acc = ai[i] < acc ? ai[i] : acc; else if (!strcmp(op, "Max")) acc = ai[i] > acc ? ai[i] : acc;
                else if (!strcmp(op, "And")) acc &= ai[i]; else if (!strcmp(op, "Or")) acc |= ai[i]; else acc ^= ai[i];
            }
            result = (uint64_t)(int64_t)acc;
        }
        memcpy(exp, &result, 8);
        return 1;
    }
    if (!strcmp(kind, "cmp") || !strcmp(kind, "mask")) {
        for (int i = 0; i < n; i++) {
            int m;
            if (!strcmp(kind, "cmp")) {
                m = !strcmp(shape, "f32") ? pred_f(op, af[i], bf[i]) : !strcmp(shape, "f64") ? pred_f(op, ad[i], bd[i]) : pred_i(op, ai[i], bi[i]);
            } else {
                int m1 = !strcmp(shape, "f32") ? pred_f("Lt", af[i], bf[i]) : !strcmp(shape, "f64") ? pred_f("Lt", ad[i], bd[i]) : pred_i("Lt", ai[i], bi[i]);
                int m2 = !strcmp(shape, "f32") ? pred_f("Le", af[i], bf[i]) : !strcmp(shape, "f64") ? pred_f("Le", ad[i], bd[i]) : pred_i("Le", ai[i], bi[i]);
                if (!strcmp(op, "And")) m = m1 & m2; else if (!strcmp(op, "Or")) m = m1 | m2; else if (!strcmp(op, "Xor")) m = m1 ^ m2;
                else if (!strcmp(op, "Andnot")) m = (!m1) & m2; else m = !m1;
            }
            if (!strcmp(shape, "f64")) od[i] = m ? ad[i] : bd[i];
            else if (!strcmp(shape, "f32")) memcpy(&of[i], m ? &af[i] : &bf[i], 4);
            else oi[i] = m ? ai[i] : bi[i];
        }
        return 1;
    }
    int w = !strcmp(shape, "f64") ? 8 : 4;
    if (!strcmp(kind, "perm") || !strcmp(kind, "gather")) {
        for (int i = 0; i < n; i++) memcpy(exp + i * w, A0 + bi[i] * w, w);
        return 1;
    }
    if (!strcmp(kind, "scatter")) {
        for (int i = 0; i < n; i++) memcpy(exp + bi[i] * w, A0 + i * w, w);
        return 1;
    }
    if (!strcmp(kind, "shuf")) {
        for (int i = 0; i < n; i++) {
            const unsigned char* src; int lane;
            if (!strcmp(op, "Reverse")) { src = A0; lane = n - 1 - i; }
            else if (!strcmp(op, "BroadcastLane")) { src = A0; lane = 3; }
            else { int start = !strcmp(op, "InterleaveHi") ? n / 2 : 0; src = (i % 2) ? B0 : A0; lane = start + i / 2; }
            memcpy(exp + i * w, src + lane * w, w);
        }
        return 1;
    }
    if (!strcmp(kind, "splatcopy")) {
        for (int i = 0; i < n; i++) {
            if (!strcmp(shape, "f32")) { vf = -2.5f + af[i]; of[i] = vf; }
            else if (!strcmp(shape, "f64")) { vd = -2.5 + ad[i]; od[i] = vd; }
            else oi[i] = -7 ^ ai[i];
        }
        return 1;
    }
    if (!strcmp(kind, "abi")) {
        for (int i = 0; i < n; i++) {
            if (!strcmp(shape, "f32")) { vf = af[i] * bf[i]; vf = vf - af[i]; of[i] = vf; }
            else if (!strcmp(shape, "f64")) { vd = ad[i] * bd[i]; vd = vd - ad[i]; od[i] = vd; }
            else oi[i] = (int32_t)((uint32_t)ai[i] * (uint32_t)bi[i] - (uint32_t)ai[i]);
        }
        return 1;
    }
    if (!strcmp(kind, "fma")) {
        for (int i = 0; i < n; i++) {
            int neg = !strcmp(op, "Fnmadd");
            // Hardware propagates an input NaN unchanged; negating it first in C
            // would flip the NaN sign, so NaN lanes keep the NaN operand.
            if (!strcmp(shape, "f32")) of[i] = isnan(af[i]) ? af[i] : fmaf(neg ? -af[i] : af[i], bf[i], af[i]);
            else od[i] = isnan(ad[i]) ? ad[i] : fma(neg ? -ad[i] : ad[i], bd[i], ad[i]);
        }
        return 1;
    }
    if (!strcmp(kind, "spill")) {
        for (int i = 0; i < 16; i++) oi[i] = (int32_t)((uint32_t)ai[i] * 2u + 1133u);
        int64_t sum = 0; for (int k = 0; k < 20; k++) sum += 1000 + k * 7;
        memcpy(expb, &sum, 8);
        return 1;
    }
    return 0;
}

#define MAXF 4
typedef struct { char name[128]; unsigned char* code; size_t len; } Func;
typedef struct { char fn[128]; long off; char sym[128]; long addend; } Reloc;

static int hexval(char c) { return c <= '9' ? c - '0' : c - 'a' + 10; }

typedef struct { char group[128]; char mode[16]; unsigned char out[192]; unsigned char b8[8]; } Result;
static Result results[1024];
static int nresults = 0;

int main(int argc, char** argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    if (argc < 2) { fprintf(stderr, "usage: %s <dump>\n", argv[0]); return 2; }
    __builtin_cpu_init();
    int have_avx512 = __builtin_cpu_supports("avx512f");
    if (!have_avx512) printf("NOTE host has no usable AVX-512: running scalar-fallback builds only\n");
    FILE* f = fopen(argv[1], "r");
    if (!f) { perror("open"); return 2; }
    static char line[1 << 20];
    Func funcs[MAXF]; int nf = 0;
    Reloc relocs[16]; int nr = 0;
    char group[128], mode[16], atag[32], btag[32];
    while (fgets(line, sizeof line, f)) {
        line[strcspn(line, "\r\n")] = 0;
        if (line[0] == 'G') {
            sscanf(line, "G %127s %15s %31s %31s", group, mode, atag, btag);
            nf = 0; nr = 0;
        } else if (line[0] == 'F') {
            char name[128]; char* hex = malloc(strlen(line));
            sscanf(line, "F %127s %s", name, hex);
            size_t n = strlen(hex) / 2;
            unsigned char* code = malloc(n + 1);
            for (size_t i = 0; i < n; i++) code[i] = hexval(hex[2*i]) * 16 + hexval(hex[2*i+1]);
            strcpy(funcs[nf].name, name); funcs[nf].code = code; funcs[nf].len = n; nf++;
            free(hex);
        } else if (line[0] == 'R') {
            sscanf(line, "R %127s %ld %127s %ld", relocs[nr].fn, &relocs[nr].off, relocs[nr].sym, &relocs[nr].addend); nr++;
        } else if (line[0] == 'E') {
            size_t total = 0, offs[MAXF];
            for (int i = 0; i < nf; i++) { offs[i] = total; total += (funcs[i].len + 15) & ~15; }
            unsigned char* mem = exec_alloc(total + 64);
            if (!mem) { perror("exec_alloc"); return 2; }
            for (int i = 0; i < nf; i++) memcpy(mem + offs[i], funcs[i].code, funcs[i].len);
            for (int r = 0; r < nr; r++) {
                long site = -1, target = -1;
                for (int i = 0; i < nf; i++) {
                    if (!strcmp(funcs[i].name, relocs[r].fn)) site = offs[i] + relocs[r].off;
                    if (!strcmp(funcs[i].name, relocs[r].sym)) target = offs[i];
                }
                if (site < 0 || target < 0) { printf("UNRESOLVED %s %s\n", group, relocs[r].sym); goto next; }
                int32_t rel = (int32_t)(target + relocs[r].addend - site);
                memcpy(mem + site, &rel, 4);
            }
            {
                long entry = -1;
                for (int i = 0; i < nf; i++) if (!strcmp(funcs[i].name, group)) entry = offs[i];
                char at[40], bt[40];
                snprintf(at, sizeof at, "%s", atag);
                if (!strcmp(btag, atag)) snprintf(bt, sizeof bt, "%sb", btag); else snprintf(bt, sizeof bt, "%s", btag);
                if (!strcmp(mode, "avx") && !have_avx512) goto next;
                fill(A, at); fill(B, bt);
                memset(OUTBUF, 0xCC, sizeof OUTBUF);
                ((fn3)(mem + entry))(A, B, OUTBUF);
                {
                    unsigned char A2[128], B2[128], ex[192], exb[8];
                    fill(A2, at); fill(B2, bt);
                    if (reference(group, A2, B2, ex, exb)) {
                        refchecked++;
                        if (memcmp(ex, OUTBUF, 192) || memcmp(exb, B, 8)) {
                            refbad++;
                            printf("REFDIFF %s %s|exp ", group, mode);
                            for (int q = 0; q < 72; q++) printf("%02x", ex[q]);
                            printf("|got ");
                            for (int q = 0; q < 72; q++) printf("%02x", OUTBUF[q]);
                            printf("|\n");
                        }
                    }
                }
                Result* res = &results[nresults++];
                strcpy(res->group, group); strcpy(res->mode, mode);
                memcpy(res->out, OUTBUF, 192); memcpy(res->b8, B, 8);
            }
        next:
            exec_free(mem, total + 64);
            for (int i = 0; i < nf; i++) free(funcs[i].code);
            nf = 0; nr = 0;
        }
    }
    int compared = 0, mismatched = 0;
    for (int i = 0; i < nresults; i++) {
        if (strcmp(results[i].mode, "avx")) continue;
        for (int j = 0; j < nresults; j++) {
            if (strcmp(results[j].mode, "scalar") || strcmp(results[j].group, results[i].group)) continue;
            compared++;
            if (memcmp(results[i].out, results[j].out, 192) || memcmp(results[i].b8, results[j].b8, 8)) {
                mismatched++;
                printf("MISMATCH %s\n", results[i].group);
            }
        }
    }
    printf("SUMMARY executed=%d compared=%d mismatched=%d refchecked=%d refbad=%d\n", nresults, compared, mismatched, refchecked, refbad);
    if (nresults == 0 || refchecked != nresults) return 2;
    return (mismatched || refbad) ? 1 : 0;
}
