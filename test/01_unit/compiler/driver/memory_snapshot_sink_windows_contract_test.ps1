param([string]$Compiler = "gcc.exe")

$ErrorActionPreference = "Stop"
$repoRoot = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot "../../../.."))
$testRoot = [System.IO.Path]::GetFullPath((Join-Path $repoRoot ("build/test/windows-mem-snapshot-" + [guid]::NewGuid().ToString("N"))))
if (-not $testRoot.StartsWith($repoRoot + [System.IO.Path]::DirectorySeparatorChar,
        [System.StringComparison]::OrdinalIgnoreCase)) { throw "test root escaped repository" }
New-Item -ItemType Directory -Path (Join-Path $testRoot "safe/nested") -Force | Out-Null
try {
    $source = Join-Path $testRoot "harness.c"
    @'
#include "runtime.h"
#include <string.h>
/* The isolated core-C TU has unrelated legacy bridge references. The test
 * never calls those paths; stubs let the linker exercise the real sink. */
int64_t rt_string_new(const uint8_t* p, uint64_t n) { (void)p; (void)n; return 0; }
SplArray* rt_array_new(int64_t n) { (void)n; return 0; }
int8_t rt_array_push(SplArray* a, int64_t n) { (void)a; (void)n; return 0; }
int64_t rt_text_slice_audit_level(void) { return 0; }
int64_t rt_text_slice_audit_note(int s, const char* name, int64_t a, int64_t b,
        const uint8_t* p, uint64_t n, const uint8_t* q, uint64_t m) {
    (void)s; (void)name; (void)a; (void)b; (void)p; (void)n; (void)q; (void)m; return 0;
}
int64_t rt_heap_live_bytes(void) { return 0; }
int64_t rt_heap_peak_bytes(void) { return 0; }
int64_t rt_time_now_monotonic_ms(void) { return 1; }
int64_t rt_value_bool(int64_t n) { return n; }
int main(int argc, char** argv) {
    if (argc != 3) return 90;
    int64_t fd = rt_mem_snapshot_open(argv[2], (int64_t)strlen(argv[2]));
    if (!strcmp(argv[1], "reject")) return fd < 0 ? 0 : 91;
    if (fd < 0) return 92;
    if (rt_process_rss_kib() <= 0 || rt_process_hwm_kib() < rt_process_rss_kib()) return 96;
    if (!rt_mem_snapshot_record(fd, 0, "open", 4, "codegen", 7, -1, "", 0,
            0,0,0,0,0,0,0,0,0,0,0)) return 93;
    if (!rt_mem_snapshot_append_flush(fd, "seq=1 event=done\n", 17)) return 94;
    return rt_mem_snapshot_close(fd) ? 0 : 95;
}
'@ | Set-Content -LiteralPath $source -Encoding ascii
    $exe = Join-Path $testRoot "harness.exe"
    $compileArgs = @("-std=gnu11", "-O0", "-ffunction-sections", "-fdata-sections",
        "-I", (Join-Path $repoRoot "src/runtime"), $source,
        (Join-Path $repoRoot "src/runtime/runtime_legacy_core.c"),
        "-Wl,--gc-sections", "-o", $exe)
    & $Compiler @compileArgs
    if ($LASTEXITCODE -ne 0) { throw "Windows harness compile failed" }
    $sink = Join-Path $testRoot "safe/nested/complete.log"
    & $exe complete $sink
    if ($LASTEXITCODE -ne 0) { throw "Windows sink write failed: $LASTEXITCODE" }
    $lines = Get-Content -LiteralPath $sink
    if ($lines.Count -ne 2 -or $lines[0] -notmatch "^schema=simple.compiler.mem_snapshot.v1 .*seq=0 .*rss_kib=[1-9][0-9]* hwm_kib=[1-9][0-9]* group_charge_metric=unavailable group_charge_current_bytes=-1 group_charge_peak_bytes=-1$" -or
            $lines[1] -ne "seq=1 event=done") { throw "flushed sink records differ" }
    & $exe reject $sink
    if ($LASTEXITCODE -ne 0) { throw "existing sink was accepted" }
    $junction = Join-Path $testRoot "junction"
    $junctionCreated = $false
    try {
        New-Item -ItemType Junction -Path $junction -Target (Join-Path $testRoot "safe") -ErrorAction Stop | Out-Null
        $junctionCreated = $true
    } catch [System.UnauthorizedAccessException] {
        Write-Host "junction check unavailable without privilege"
    }
    if ($junctionCreated) {
        & $exe reject (Join-Path $junction "rejected.log")
        if ($LASTEXITCODE -ne 0) { throw "reparse-point parent was accepted" }
    }
    Write-Host "Windows memory snapshot sink contract: PASS"
} finally {
    if ($testRoot.StartsWith($repoRoot + [System.IO.Path]::DirectorySeparatorChar,
            [System.StringComparison]::OrdinalIgnoreCase)) {
        Remove-Item -LiteralPath $testRoot -Recurse -Force -ErrorAction SilentlyContinue
    }
}
