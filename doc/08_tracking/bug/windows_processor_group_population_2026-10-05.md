# Windows active processor population was limited to one group

`runtime_core_host_services.c::rt_cpu_count` used `GetSystemInfo`, reporting the
calling thread's primary processor group. On the measured Windows 11 host this
was 16 or 64, although all 80 logical processors were active across two groups.
The system-population provider now uses `GetActiveProcessorCount` with
`ALL_PROCESSOR_GROUPS`. It retains -1 on an API failure.

This is not an admission or speedup claim. `rt_thread_available_parallelism` is a
separate capacity contract and remains unchanged in this checkpoint. A draft
group-aware implementation was withheld: `GetThreadGroupAffinity` and
`GetProcessGroupAffinity` return identical data before and after explicit
full-primary-group thread restriction on Windows 11. Treating that mask as the
unrestricted default would over-admit. CPU-set subset checks do not resolve
that ambiguity. No process affinity or BIOS setting was changed globally.

The native regression compares the system provider with the OS all-group
population and confirms that restricting only the fixture thread to one CPU
does not change the system population. Actual native evidence is retained in
`runtime/windows-restart-20261004/windows-processor-capacity`; no bootstrap
qualification or throughput improvement is asserted.

Frontend parallelism is independently constrained by memory admission. The
current 3,000,000 KiB per-worker estimate and 3,000,000 KiB frontend tree budget
admit one worker even when code generation requests 80. A larger frontend share
requires measured worker peaks and a correspondingly larger real reservation
and enforced tree limit; merely changing worker count would be unsafe.

Primary contracts:
- https://learn.microsoft.com/en-us/windows/win32/procthread/processor-groups
- https://learn.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-getactiveprocessorcount
- https://learn.microsoft.com/en-us/windows/win32/api/processtopologyapi/nf-processtopologyapi-getthreadgroupaffinity
