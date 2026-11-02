#define _WIN32_WINNT 0x0A00
#include <windows.h>
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <thread>
#include <vector>

extern "C" unsigned long long simple_probe(unsigned long long, unsigned long long);
extern "C" unsigned char simple_entry_sled;
extern "C" unsigned char simple_exit_sled;

static std::atomic<unsigned long long> g_entries{0}, g_exits{0};
static std::atomic<unsigned long long> g_bad_ids{0}, g_bad_results{0};

static void record_event(unsigned kind) noexcept {
    if (kind == 0) g_entries.fetch_add(1, std::memory_order_relaxed);
    else if (kind == 1) g_exits.fetch_add(1, std::memory_order_relaxed);
    else g_bad_ids.fetch_add(1, std::memory_order_relaxed);
}

using Sink = void (*)(unsigned) noexcept;
static std::atomic<Sink> g_sink{&record_event};

extern "C" __declspec(noinline) void simple_trace_dispatch(
    unsigned id, unsigned kind) noexcept {
    if (id != 0x1234) {
        g_bad_ids.fetch_add(1, std::memory_order_relaxed);
        return;
    }
    // This is an actual indirect C++ callback with /guard:cf instrumentation.
    Sink sink = g_sink.load(std::memory_order_acquire);
    if (sink) sink(kind);
}

static unsigned char* const kEntry = &simple_entry_sled;
static unsigned char* const kExit = &simple_exit_sled;

static void patch(unsigned char* site, bool enable) {
#if defined(_M_X64)
    // Disabled: EB 0B (JMP +11). Enabled: 66 90 (2-byte NOP).
    // Both values are 2-byte aligned and exchanged in one atomic operation.
    const SHORT word = static_cast<SHORT>(enable ? 0x9066 : 0x0BEB);
    InterlockedExchange16(reinterpret_cast<volatile SHORT*>(site), word);
#elif defined(_M_ARM64)
    // Disabled: B +32. Enabled: NOP. Both are a single ARM64 instruction.
    const LONG word = static_cast<LONG>(enable ? 0xd503201fU : 0x14000008U);
    InterlockedExchange(reinterpret_cast<volatile LONG*>(site), word);
#else
#error Unsupported Windows native architecture
#endif
    if (!FlushInstructionCache(GetCurrentProcess(), site, 16)) {
        std::printf("XRAY_INTEGRATION flush failed: %lu\n", GetLastError());
        std::abort();
    }
}

static bool verify_disabled_sleds() {
#if defined(_M_X64)
    const bool aligned = ((reinterpret_cast<uintptr_t>(kEntry) |
                           reinterpret_cast<uintptr_t>(kExit)) & 1) == 0;
    return aligned && kEntry[0] == 0xeb && kEntry[1] == 0x0b &&
                      kExit[0] == 0xeb && kExit[1] == 0x0b;
#else
    const bool aligned = ((reinterpret_cast<uintptr_t>(kEntry) |
                           reinterpret_cast<uintptr_t>(kExit)) & 3) == 0;
    if (!aligned) return false;
    return *reinterpret_cast<const uint32_t*>(kEntry) == 0x14000008U &&
           *reinterpret_cast<const uint32_t*>(kExit) == 0x14000008U;
#endif
}

static void run_calls(unsigned count, unsigned seed) {
    for (unsigned i = 0; i < count; ++i) {
        const unsigned long long a = 0x123456789ULL + i + seed;
        const unsigned long long b = 0xFEDCBA987ULL - i + seed;
        if (simple_probe(a, b) != a + b)
            g_bad_results.fetch_add(1, std::memory_order_relaxed);
    }
}

int main() {
#if defined(_M_X64)
    const char* arch = "x64";
#else
    const char* arch = "arm64";
#endif
    std::printf("XRAY_INTEGRATION arch=%s entry=%p exit=%p\n",
                arch, static_cast<void*>(kEntry), static_cast<void*>(kExit));

    PROCESS_MITIGATION_CONTROL_FLOW_GUARD_POLICY cfg = {};
    BOOL cfg_ok = GetProcessMitigationPolicy(GetCurrentProcess(),
        ProcessControlFlowGuardPolicy, &cfg, sizeof(cfg));
    PROCESS_MITIGATION_USER_SHADOW_STACK_POLICY cet = {};
    BOOL cet_ok = GetProcessMitigationPolicy(GetCurrentProcess(),
        ProcessUserShadowStackPolicy, &cet, sizeof(cet));
    std::printf("XRAY_INTEGRATION cfg=%s cet_shstk=%s\n",
        cfg_ok ? (cfg.EnableControlFlowGuard ? "ON" : "OFF") : "UNKNOWN",
        cet_ok ? (cet.EnableUserShadowStack ? "ON" : "OFF") : "UNKNOWN");

    if (!verify_disabled_sleds()) {
        std::puts("XRAY_INTEGRATION FAIL: disabled sled encoding/alignment");
        return 2;
    }

    SYSTEM_INFO info = {};
    GetSystemInfo(&info);
    const uintptr_t page_size = info.dwPageSize;
    const uintptr_t first = std::min(reinterpret_cast<uintptr_t>(kEntry),
                                     reinterpret_cast<uintptr_t>(kExit));
    const uintptr_t last = std::max(reinterpret_cast<uintptr_t>(kEntry),
                                    reinterpret_cast<uintptr_t>(kExit));
    const uintptr_t region = first & ~(page_size - 1);
    const uintptr_t region_end = (last + 64 + page_size - 1) & ~(page_size - 1);
    DWORD original_protection = 0;
    if (!VirtualProtect(reinterpret_cast<void*>(region),
                        region_end - region, PAGE_EXECUTE_READWRITE,
                        &original_protection)) {
        std::printf("XRAY_INTEGRATION FAIL: VirtualProtect error=%lu\n", GetLastError());
        return 3;
    }

    run_calls(30000, 0);
    if (g_entries.load() != 0 || g_exits.load() != 0 || g_bad_results.load()) {
        std::puts("XRAY_INTEGRATION FAIL: disabled mode");
        return 4;
    }
    patch(kEntry, true);
    patch(kExit, true);
    run_calls(50000, 9);
    const auto entries = g_entries.load(), exits = g_exits.load();
    if (entries != 50000 || exits != 50000 || g_bad_ids.load() ||
        g_bad_results.load()) {
        std::printf("XRAY_INTEGRATION FAIL: static enabled entry=%llu exit=%llu id=%llu bad=%llu\n",
                    entries, exits, g_bad_ids.load(), g_bad_results.load());
        return 5;
    }
    std::printf("XRAY_INTEGRATION static-enabled PASS entry=%llu exit=%llu\n",
                entries, exits);

    constexpr unsigned workers = 4, calls_per_worker = 90000;
    std::atomic<bool> start{false};
    std::vector<std::thread> threads;
    for (unsigned t = 0; t < workers; ++t) {
        threads.emplace_back([&, t] {
            while (!start.load(std::memory_order_acquire)) std::this_thread::yield();
            run_calls(calls_per_worker, t * 10000);
        });
    }
    start.store(true, std::memory_order_release);
    for (unsigned i = 0; i < 15000; ++i) {
        const bool enabled = (i & 1) != 0;
        patch(kEntry, enabled);
        patch(kExit, enabled);
    }
    for (auto& thread : threads) thread.join();
    patch(kEntry, false);
    patch(kExit, false);
    DWORD ignored = 0;
    VirtualProtect(reinterpret_cast<void*>(region), region_end - region,
                   original_protection, &ignored);

    const auto bad_ids = g_bad_ids.load(), bad_results = g_bad_results.load();
    std::printf("XRAY_INTEGRATION concurrent entry=%llu exit=%llu transitions=15000 id_errors=%llu corruptions=%llu\n",
                g_entries.load(), g_exits.load(), bad_ids, bad_results);
    if (bad_ids || bad_results) return 6;
    std::puts("XRAY_INTEGRATION PASS native entry/exit and concurrent patching");
    return 0;
}
