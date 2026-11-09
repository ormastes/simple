// Deterministic ABI-state regression. Link the existing 13-byte-sled x64
// trampoline unmodified as the baseline. No executable-memory writes required.
#include <cstdint>
#include <cstdio>
#include <cstring>
#if defined(_MSC_VER)
#include <intrin.h>
#define XRAY_MS_ABI
#else
#include <cpuid.h>
#define XRAY_MS_ABI __attribute__((ms_abi))
#endif

struct alignas(32) Snapshot {
    unsigned char ymm[16][32];
    std::uint32_t mxcsr;
    std::uint32_t reserved;
    std::uint64_t flags_before;
    std::uint64_t flags_after;
};
static_assert(sizeof(Snapshot) == 544, "assembly layout");
extern "C" XRAY_MS_ABI void xray_probe_baseline_entry(Snapshot*);
extern "C" XRAY_MS_ABI void xray_probe_bounded_entry(Snapshot*);
extern "C" XRAY_MS_ABI void xray_probe_baseline_exit(Snapshot*);
extern "C" XRAY_MS_ABI void xray_probe_bounded_exit(Snapshot*);
extern "C" XRAY_MS_ABI std::uint64_t xray_read_xcr0();
extern "C" unsigned xray_dispatch_errors;
extern "C" unsigned xray_seen_entries;
extern "C" unsigned xray_seen_exits;

static bool avx_state_enabled(bool* avx2) {
    unsigned a, b, c, d;
#if defined(_MSC_VER)
    int regs[4];
    __cpuidex(regs, 1, 0);
    c = static_cast<unsigned>(regs[2]);
#else
    if (!__get_cpuid(1, &a, &b, &c, &d)) return false;
#endif
    constexpr unsigned required = (1U << 27) | (1U << 28);
    if ((c & required) != required) return false;
    if ((xray_read_xcr0() & 6U) != 6U) return false;
#if defined(_MSC_VER)
    __cpuidex(regs, 7, 0);
    *avx2 = (static_cast<unsigned>(regs[1]) & (1U << 5)) != 0;
#else
    __cpuid_count(7, 0, a, b, c, d);
    *avx2 = (b & (1U << 5)) != 0;
#endif
    return true;
}

static bool inspect(const char* label, const Snapshot& s, bool bounded) {
    const unsigned char pattern[32] = {
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32
    };
    unsigned lower_bad = 0, upper_bad = 0, upper_zero = 0;
    const unsigned char zeros[16] = {};
    for (unsigned r = 0; r != 16; ++r) {
        lower_bad += std::memcmp(s.ymm[r], pattern, 16) != 0;
        upper_bad += std::memcmp(s.ymm[r] + 16, pattern + 16, 16) != 0;
        upper_zero += std::memcmp(s.ymm[r] + 16, zeros, 16) == 0;
    }
    // Arithmetic flags, DF, and IF are compared. Neither the callback nor test
    // changes privileged state. Ignore reserved/debug-specific bits.
    constexpr std::uint64_t flags_mask = 0xED5;
    const bool flags_ok = ((s.flags_before ^ s.flags_after) & flags_mask) == 0;
    const bool ok = bounded
        ? lower_bad == 0 && upper_bad == 0 && s.mxcsr == 0x1F80 && flags_ok
        : lower_bad == 0 && upper_bad == 16 && upper_zero == 16 &&
          s.mxcsr == 0x1FA0 && flags_ok;
    std::printf("XRAY_ABI %s lower_bad=%u upper_bad=%u upper_zero=%u "
                "mxcsr=0x%x flags=%s result=%s\n", label, lower_bad, upper_bad,
                upper_zero, s.mxcsr, flags_ok ? "preserved" : "BAD",
                ok ? "PASS" : "FAIL");
    return ok;
}

int main() {
    bool avx2 = false;
    if (!avx_state_enabled(&avx2)) {
        std::puts("XRAY_ABI SKIP: AVX with OS-enabled XMM/YMM state unavailable");
        return 0;
    }
    std::printf("XRAY_ABI feature=AVX_OS_ENABLED avx2=%s "
                "scope=YMM0-15_MXCSR_RFLAGS no_avx512_claim\n",
                avx2 ? "yes" : "no");
    Snapshot baseline_entry{}, bounded_entry{}, baseline_exit{}, bounded_exit{};
    xray_probe_baseline_entry(&baseline_entry);
    xray_probe_bounded_entry(&bounded_entry);
    xray_probe_baseline_exit(&baseline_exit);
    xray_probe_bounded_exit(&bounded_exit);
    const bool ok1 = inspect("baseline-entry-EXPECTED-GAP", baseline_entry, false);
    const bool ok2 = inspect("bounded-entry-preservation", bounded_entry, true);
    const bool ok3 = inspect("baseline-exit-EXPECTED-GAP", baseline_exit, false);
    const bool ok4 = inspect("bounded-exit-preservation", bounded_exit, true);
    const bool dispatch_ok = xray_dispatch_errors == 0 &&
                             xray_seen_entries == 2 && xray_seen_exits == 2;
    std::printf("XRAY_ABI dispatch entries=%u exits=%u bad_id_or_kind=%u result=%s\n",
                xray_seen_entries, xray_seen_exits, xray_dispatch_errors,
                dispatch_ok ? "PASS" : "FAIL");
    if (!(ok1 && ok2 && ok3 && ok4 && dispatch_ok)) return 1;
    std::puts("XRAY_ABI PASS: baseline defect reproduced; bounded YMM/MXCSR remedy verified");
    return 0;
}
