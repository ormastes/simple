# Phase1 process memory externs missing

The original Linux seed sweep failed provider_wire_dispatch_spec.spl with unknown extern function rt_process_hwm_kib. A registration-level probe also reproduced a missing rt_process_rss_kib provider. Both functions exist in the native runtime.

Register the interpreter providers using its existing process_status_kib reader, which already supplies RSS and peak memory to memory-snapshot records. Values are measured in KiB from /proc/self/status; unavailable host status returns -1. Linux behavior is verified here; native Windows runtime support is not represented by this Linux bootstrap check.

The regression commits 64 MiB of pages, calls both externs through actual parsed Simple code, and requires RSS >= 65536 KiB and peak >= RSS. It failed before the repair with unknown extern rt_process_rss_kib and passed afterward. Enforcing watchdog evidence records exit 0, quiescent 1, peak 4677272 KiB, and maximum sample gap 3035 ms. Logs and receipts are retained under /tmp/simple-process-metrics-repair.

The original provider spec still requires verification on a rebuilt seed. This focused test is not whole-suite or Phase2 admission evidence.
