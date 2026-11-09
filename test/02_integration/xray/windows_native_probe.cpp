#define _WIN32_WINNT 0x0A00
#include <windows.h>
#include <stdio.h>

int main() {
#if defined(_M_ARM64)
    const char* arch = "arm64";
#elif defined(_M_X64)
    const char* arch = "x64";
#else
    const char* arch = "unexpected";
#endif
    SYSTEM_INFO info = {};
    GetNativeSystemInfo(&info);
    printf("XRAY_PROBE architecture=%s native_processor_arch=%u\n",
           arch, unsigned(info.wProcessorArchitecture));

    PROCESS_MITIGATION_CONTROL_FLOW_GUARD_POLICY cfg = {};
    const BOOL cfg_ok = GetProcessMitigationPolicy(
        GetCurrentProcess(), ProcessControlFlowGuardPolicy, &cfg, sizeof(cfg));
    printf("XRAY_PROBE cfg_query=%s enabled=%u error=%lu\n",
           cfg_ok ? "ok" : "failed",
           cfg_ok ? unsigned(cfg.EnableControlFlowGuard) : 0u,
           cfg_ok ? 0ul : GetLastError());

    PROCESS_MITIGATION_USER_SHADOW_STACK_POLICY cet = {};
    const BOOL cet_ok = GetProcessMitigationPolicy(
        GetCurrentProcess(), ProcessUserShadowStackPolicy, &cet, sizeof(cet));
    printf("XRAY_PROBE cet_query=%s enabled=%u strict=%u error=%lu\n",
           cet_ok ? "ok" : "failed",
           cet_ok ? unsigned(cet.EnableUserShadowStack) : 0u,
           cet_ok ? unsigned(cet.EnableUserShadowStackStrictMode) : 0u,
           cet_ok ? 0ul : GetLastError());
    printf("XRAY_PROBE runtime_probe_only; no XRay patch/unpatch performed\n");
    return 0;
}
