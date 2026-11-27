// Native, process-isolated mitigation checks for Simple XRay CI fixtures.
// This is test code, not a runtime implementation or a host-policy changer.
#define _WIN32_WINNT 0x0A00
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#define WIN32_NO_STATUS
#include <windows.h>
#include <winternl.h>
#undef WIN32_NO_STATUS
#include <ntstatus.h>
#include <cstdio>
#include <cstdint>
#include <cstring>
#include <cwchar>

// Documented import library for SetProcessValidCallTargets.
#pragma comment(lib, "WindowsApp.lib")

// SDK 26100 or later is recommended. Use the SDK enum/type, not an invented
// feature-number or a silent fallback for ProcessUserPointerAuthPolicy.
extern "C" int security_return_control();
#if defined(_M_X64)
extern "C" void security_cet_bad_return();
#elif defined(_M_ARM64)
extern "C" int security_pac_sign_active();
extern "C" void security_pac_bad_return();
#else
#error Native x64 or ARM64 required
#endif

static constexpr DWORD kUnavailable = 77;
static constexpr DWORD kBadReached = 78;
static constexpr DWORD kSetupFailure = 79;
static constexpr DWORD kTimeout = 80;
static constexpr int kMagic = 0x5678;

extern "C" __declspec(noreturn) void security_unchecked_landing() {
    // A valid executable destination distinguishes an unenforced RET from a
    // generic jump to unmapped memory. Called only by the negative CET fixture.
    ExitProcess(kBadReached);
}

static void print_policies(const char* where) {
    PROCESS_MITIGATION_CONTROL_FLOW_GUARD_POLICY cfg = {};
    SetLastError(0);
    const BOOL c = GetProcessMitigationPolicy(GetCurrentProcess(),
        ProcessControlFlowGuardPolicy, &cfg, sizeof(cfg));
    const DWORD ce = c ? 0 : GetLastError();
    PROCESS_MITIGATION_USER_SHADOW_STACK_POLICY cet = {};
    SetLastError(0);
    const BOOL h = GetProcessMitigationPolicy(GetCurrentProcess(),
        ProcessUserShadowStackPolicy, &cet, sizeof(cet));
    const DWORD he = h ? 0 : GetLastError();
    PROCESS_MITIGATION_USER_POINTER_AUTH_POLICY pac = {};
    SetLastError(0);
    const BOOL p = GetProcessMitigationPolicy(GetCurrentProcess(),
        ProcessUserPointerAuthPolicy, &pac, sizeof(pac));
    const DWORD pe = p ? 0 : GetLastError();
    std::printf("SECURITY_POLICY scope=%s cfg_query=%u cfg_error=%lu cfg=%u "
                "cet_query=%u cet_error=%lu cet=%u cet_audit=%u cet_strict=%u "
                "pac_query=%u pac_error=%lu pac=%u\n", where,
        !!c, ce, cfg.EnableControlFlowGuard, !!h, he,
        cet.EnableUserShadowStack, cet.AuditUserShadowStack,
        cet.EnableUserShadowStackStrictMode, !!p, pe,
        pac.EnablePointerAuthUserIp);
    std::fflush(stdout);
}

using GeneratedFn = int (*)();
// /guard:cf must be present at compile AND link time. This noinline indirect
// call is deliberately outside the allocation function to prevent folding.
__declspec(noinline) static int guarded_call(GeneratedFn volatile target) {
    return target();
}

static int cfg_child(bool valid) {
    PROCESS_MITIGATION_CONTROL_FLOW_GUARD_POLICY cfg = {};
    if (!GetProcessMitigationPolicy(GetCurrentProcess(),
        ProcessControlFlowGuardPolicy, &cfg, sizeof(cfg)) ||
        !cfg.EnableControlFlowGuard) return kUnavailable;
    SYSTEM_INFO si = {};
    GetSystemInfo(&si);
    // Allocate our own private test page, initially an INVALID CFG target set.
    // Keeping this tiny page RWX avoids VirtualProtect accidentally making all
    // targets valid. This executable-only child exits immediately afterwards.
    auto* page = static_cast<unsigned char*>(VirtualAlloc(nullptr,
        si.dwPageSize, MEM_RESERVE | MEM_COMMIT,
        PAGE_EXECUTE_READWRITE | PAGE_TARGETS_INVALID));
    if (!page) {
        std::printf("SECURITY_SETUP VirtualAlloc error=%lu\n", GetLastError());
        return kSetupFailure;
    }
#if defined(_M_X64)
    // ENDBR64; mov eax,0x5678; ret. Harmless even if CFG is not enforced.
    const unsigned char body[] =
        {0xf3,0x0f,0x1e,0xfa,0xb8,0x78,0x56,0x00,0x00,0xc3};
#else
    // BTI c; mov w0,#0x5678; ret. BTI presence is NOT a BTI-enforcement claim.
    const uint32_t body[] = {0xd503245fU,0x528acf00U,0xd65f03c0U};
#endif
    std::memcpy(page, body, sizeof(body));
    if (!FlushInstructionCache(GetCurrentProcess(), page, sizeof(body)))
        return kSetupFailure;
    if (valid) {
        CFG_CALL_TARGET_INFO target = {};
        target.Offset = 0; // Page base is 16-byte aligned.
        target.Flags = CFG_CALL_TARGET_VALID;
        if (!SetProcessValidCallTargets(GetCurrentProcess(), page,
                si.dwPageSize, 1, &target)) {
            std::printf("SECURITY_SETUP SetProcessValidCallTargets error=%lu\n",
                GetLastError());
            return kSetupFailure;
        }
    }
    const int result = guarded_call(reinterpret_cast<GeneratedFn>(page));
    VirtualFree(page, 0, MEM_RELEASE);
    return result == kMagic ? (valid ? 0 : kBadReached) : kSetupFailure;
}

static int child(const char* mode) {
    SetErrorMode(SEM_FAILCRITICALERRORS | SEM_NOGPFAULTERRORBOX);
    print_policies(mode);
    if (!std::strcmp(mode, "cfg-positive")) return cfg_child(true);
    if (!std::strcmp(mode, "cfg-negative")) return cfg_child(false);
#if defined(_M_X64)
    PROCESS_MITIGATION_USER_SHADOW_STACK_POLICY policy = {};
    if (!GetProcessMitigationPolicy(GetCurrentProcess(),
        ProcessUserShadowStackPolicy, &policy, sizeof(policy)) ||
        !policy.EnableUserShadowStack || policy.AuditUserShadowStack)
        return kUnavailable;
    if (!std::strcmp(mode, "cet-positive"))
        return security_return_control() == kMagic ? 0 : kSetupFailure;
    if (!std::strcmp(mode, "cet-negative")) {
        security_cet_bad_return();
        return kBadReached;
    }
#else
    PROCESS_MITIGATION_USER_POINTER_AUTH_POLICY policy = {};
    if (!GetProcessMitigationPolicy(GetCurrentProcess(),
        ProcessUserPointerAuthPolicy, &policy, sizeof(policy)) ||
        !policy.EnablePointerAuthUserIp) return kUnavailable;
    if (!std::strcmp(mode, "pac-positive")) {
        const int active = security_pac_sign_active();
        std::printf("SECURITY_PAC signed_lr_changed=%d "
                    "note=activity_observation_not_enforcement_proof\n", active);
        return security_return_control() == kMagic ? 0 : kSetupFailure;
    }
    if (!std::strcmp(mode, "pac-negative")) {
        security_pac_bad_return();
        return kBadReached;
    }
#endif
    return kSetupFailure;
}

struct ChildResult {
    bool launched = false;
    bool timed_out = false;
    DWORD create_error = 0;
    DWORD exit_code = kSetupFailure;
    bool cfg_rejection = false;
    bool cet_rejection = false;
    bool pac_rejection = false;
};

static ChildResult run_child(const wchar_t* executable, const char* mode,
                             bool request_native) {
    ChildResult result;
    wchar_t wide_mode[64] = {};
    for (size_t i = 0; mode[i] && i + 1 < 64; ++i) wide_mode[i] = mode[i];
    wchar_t cmd[32768] = {};
    if (_snwprintf_s(cmd, sizeof(cmd) / sizeof(cmd[0]), _TRUNCATE, L"\"%ls\" --child %ls",
                     executable, wide_mode) < 0) return result;
    STARTUPINFOEXW sx = {};
    sx.StartupInfo.cb = sizeof(sx);
    sx.StartupInfo.dwFlags = STARTF_USESTDHANDLES;
    sx.StartupInfo.hStdInput = GetStdHandle(STD_INPUT_HANDLE);
    sx.StartupInfo.hStdOutput = GetStdHandle(STD_OUTPUT_HANDLE);
    sx.StartupInfo.hStdError = GetStdHandle(STD_ERROR_HANDLE);
    DWORD64 mitigations[2] = {};
    SIZE_T attr_size = 0;
    if (request_native) {
        // Only the child process is configured. Nothing persists on the host.
        mitigations[0] = PROCESS_CREATION_MITIGATION_POLICY_CONTROL_FLOW_GUARD_ALWAYS_ON;
#if defined(_M_X64)
        mitigations[1] = PROCESS_CREATION_MITIGATION_POLICY2_CET_USER_SHADOW_STACKS_ALWAYS_ON;
#else
        mitigations[1] = PROCESS_CREATION_MITIGATION_POLICY2_POINTER_AUTH_USER_IP_ALWAYS_ON;
#endif
        InitializeProcThreadAttributeList(nullptr, 1, 0, &attr_size);
        sx.lpAttributeList = static_cast<LPPROC_THREAD_ATTRIBUTE_LIST>(
            HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, attr_size));
        if (!sx.lpAttributeList ||
            !InitializeProcThreadAttributeList(sx.lpAttributeList, 1, 0, &attr_size) ||
            !UpdateProcThreadAttribute(sx.lpAttributeList, 0,
                PROC_THREAD_ATTRIBUTE_MITIGATION_POLICY, mitigations,
                sizeof(mitigations), nullptr, nullptr)) {
            result.create_error = GetLastError();
            if (sx.lpAttributeList) HeapFree(GetProcessHeap(), 0, sx.lpAttributeList);
            return result;
        }
    }
    PROCESS_INFORMATION pi = {};
    const DWORD flags = DEBUG_ONLY_THIS_PROCESS |
        (request_native ? EXTENDED_STARTUPINFO_PRESENT : 0);
    if (!request_native) sx.StartupInfo.cb = sizeof(STARTUPINFOW);
    result.launched = !!CreateProcessW(executable, cmd, nullptr, nullptr, TRUE,
        flags, nullptr, nullptr, &sx.StartupInfo, &pi);
    result.create_error = result.launched ? 0 : GetLastError();
    if (sx.lpAttributeList) {
        DeleteProcThreadAttributeList(sx.lpAttributeList);
        HeapFree(GetProcessHeap(), 0, sx.lpAttributeList);
    }
    if (!result.launched) return result;
    bool loader_break_seen = false;
    bool done = false;
    const ULONGLONG deadline = GetTickCount64() + 20000;
    while (!done) {
        if (GetTickCount64() >= deadline) {
            TerminateProcess(pi.hProcess, kTimeout);
            result.timed_out = true;
            result.exit_code = kTimeout;
            break;
        }
        DEBUG_EVENT ev = {};
        if (!WaitForDebugEvent(&ev, 250)) continue;
        DWORD disposition = DBG_CONTINUE;
        if (ev.dwDebugEventCode == CREATE_PROCESS_DEBUG_EVENT) {
            if (ev.u.CreateProcessInfo.hFile) CloseHandle(ev.u.CreateProcessInfo.hFile);
        } else if (ev.dwDebugEventCode == LOAD_DLL_DEBUG_EVENT) {
            if (ev.u.LoadDll.hFile) CloseHandle(ev.u.LoadDll.hFile);
        } else if (ev.dwDebugEventCode == EXCEPTION_DEBUG_EVENT) {
            const auto& e = ev.u.Exception.ExceptionRecord;
            if (e.ExceptionCode == EXCEPTION_BREAKPOINT && !loader_break_seen) {
                loader_break_seen = true;
            } else {
                disposition = DBG_EXCEPTION_NOT_HANDLED;
                std::printf("SECURITY_EXCEPTION case=%s first=%lu code=0x%08lx "
                            "address=%p count=%lu", mode, ev.u.Exception.dwFirstChance,
                            e.ExceptionCode, e.ExceptionAddress, e.NumberParameters);
                for (DWORD n = 0; n < e.NumberParameters && n < 4; ++n)
                    std::printf(" p%lu=0x%llx", n,
                        static_cast<unsigned long long>(e.ExceptionInformation[n]));
                std::putchar('\n');
                const bool fast = e.ExceptionCode == static_cast<DWORD>(STATUS_STACK_BUFFER_OVERRUN);
                const ULONG_PTR subcode = e.NumberParameters ? e.ExceptionInformation[0] : ~ULONG_PTR(0);
                if (fast && subcode == FAST_FAIL_GUARD_ICALL_CHECK_FAILURE)
                    result.cfg_rejection = true;
                if ((fast && (subcode == FAST_FAIL_GUARD_SS_FAILURE ||
                              subcode == FAST_FAIL_CONTROL_INVALID_RETURN_ADDRESS)) ||
                    e.ExceptionCode == static_cast<DWORD>(STATUS_CONTROL_STACK_VIOLATION) ||
                    e.ExceptionCode == static_cast<DWORD>(STATUS_RETURN_ADDRESS_HIJACK_ATTEMPT))
                    result.cet_rejection = true;
                // PAC can be reported with its specific fast-fail subcode.
                // On non-FPAC implementations it poisons LR; RET then causes
                // an instruction-fetch fault. Never accept an arbitrary crash.
                if ((fast && subcode == FAST_FAIL_POINTER_AUTH_INVALID_RETURN_ADDRESS) ||
                    (e.ExceptionCode == EXCEPTION_ACCESS_VIOLATION &&
                     e.NumberParameters >= 2 && e.ExceptionInformation[0] == 8))
                    result.pac_rejection = true;
            }
        } else if (ev.dwDebugEventCode == EXIT_PROCESS_DEBUG_EVENT) {
            result.exit_code = ev.u.ExitProcess.dwExitCode;
            done = true;
        }
        ContinueDebugEvent(ev.dwProcessId, ev.dwThreadId, disposition);
    }
    CloseHandle(pi.hThread);
    CloseHandle(pi.hProcess);
    std::printf("SECURITY_CHILD case=%s launched=%u create_error=%lu "
                "exit=0x%08lx timeout=%u cfg_reject=%u cet_reject=%u pac_reject=%u\n",
                mode, result.launched, result.create_error, result.exit_code,
                result.timed_out, result.cfg_rejection, result.cet_rejection,
                result.pac_rejection);
    return result;
}

int main(int argc, char** argv) {
    if (argc == 3 && !std::strcmp(argv[1], "--child")) return child(argv[2]);
    bool require_native = false, request_native = false;
    for (int n = 1; n < argc; ++n) {
        if (!std::strcmp(argv[n], "--require-native")) require_native = true;
        else if (!std::strcmp(argv[n], "--request-native")) request_native = true;
        else return kSetupFailure;
    }
    print_policies("parent");
    wchar_t executable[32768] = {};
    const DWORD capacity = sizeof(executable) / sizeof(executable[0]);
    const DWORD length = GetModuleFileNameW(nullptr, executable, capacity);
    if (!length || length >= capacity) return kSetupFailure;
    const auto cp = run_child(executable, "cfg-positive", request_native);
    const auto cn = run_child(executable, "cfg-negative", request_native);
    const bool cfg_pass = cp.launched && cn.launched && cp.exit_code == 0 &&
        cn.cfg_rejection && cn.exit_code != 0 && cn.exit_code != kBadReached &&
        !cp.timed_out && !cn.timed_out;
    std::printf("SECURITY_RESULT cfg=%s\n", cfg_pass ? "ENFORCEMENT_PASS" : "FAIL");
#if defined(_M_X64)
    const char* name = "cet";
    const auto np = run_child(executable, "cet-positive", request_native);
    const auto nn = run_child(executable, "cet-negative", request_native);
    const bool native_rejected = nn.cet_rejection;
#else
    const char* name = "pac";
    const auto np = run_child(executable, "pac-positive", request_native);
    const auto nn = run_child(executable, "pac-negative", request_native);
    const bool native_rejected = nn.pac_rejection;
#endif
    const bool unavailable = np.launched && nn.launched &&
        np.exit_code == kUnavailable && nn.exit_code == kUnavailable;
    const bool native_pass = np.launched && nn.launched && np.exit_code == 0 &&
        native_rejected && nn.exit_code != 0 && nn.exit_code != kBadReached &&
        !np.timed_out && !nn.timed_out;
    std::printf("SECURITY_RESULT %s=%s require_native=%u\n", name,
        native_pass ? "ENFORCEMENT_PASS" :
        (unavailable ? "UNAVAILABLE_NOT_PROVEN" : "FAIL_OR_UNCLASSIFIED"), require_native);
    std::puts("SECURITY_SCOPE compile/policy/positive/negative are distinct; "
              "BTI enforcement is not asserted; no system-wide policy changes");
    return cfg_pass && (native_pass || (unavailable && !require_native)) ? 0 : 1;
}
