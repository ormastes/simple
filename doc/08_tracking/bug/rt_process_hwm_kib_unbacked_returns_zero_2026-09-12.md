# `process_peak_rss_kb()` silently returns 0: `rt_process_hwm_kib` has no runtime backing

- Status: OPEN (2026-09-12)
- Area: lib / nogc_sync_mut / io / sysinfo_ops
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 prefix `3d120a6f` (`Simple Language v1.0.0-rc.1`, Rust bootstrap seed)
- Found while implementing todo row 232 ("Add memory profiling")

## Symptom

`src/lib/nogc_sync_mut/io/sysinfo_ops.spl:62`

```
fn process_peak_rss_kb() -> i64:
    rt_process_hwm_kib()
```

always answers `0`, whatever the process is actually using. This is the
unbacked-extern silent-nil class recorded in
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`: a caller
that trusts the number reads "this process used no memory" rather than "no
measurement was taken".

## Repro

```
use std.nogc_sync_mut.io.sysinfo_ops.{process_peak_rss_kb}

fn main():
    print "rss_kb_1={process_peak_rss_kb()}"
    var big: [text] = []
    var i = 0
    while i < 200000:
        big.push("filler-line-number-{i}")
        i = i + 1
    print "rss_kb_2={process_peak_rss_kb()} held={big.len()}"
```

```
$ bin/simple run probe.spl
ERROR ... rt_interp_call error: ... "unknown extern function: rt_process_hwm_kib"
   code: Some("E-SFFI-001")
rss_kb_1=0
ERROR ... "unknown extern function: rt_process_hwm_kib"
rss_kb_2=0 grew=false held=200000
```

200,000 retained strings move VmHWM by tens of megabytes on this host (measured
124,532 kB -> 166,756 kB for a comparable workload through `/proc/self/status`),
so `0` is not a rounding artifact — the call never reaches a runtime.

## Expected

Either back `rt_process_hwm_kib` in the runtime, or have `process_peak_rss_kb`
return a `Result`/negative sentinel so a caller can tell "no measurement" from
"zero bytes". A measurement API that reports 0 on failure cannot be used in any
fail-closed assertion, which is precisely what a memory-profiling spec needs.

## Workaround in use

`test/01_unit/app/tooling/test_db_performance_spec.spl` reads `VmHWM:` out of
`/proc/self/status` itself and returns `-1` when `/proc` is unreadable, so the
scenario fails rather than passes when it cannot measure. That is a Linux-only
workaround living in a spec, not a fix.
