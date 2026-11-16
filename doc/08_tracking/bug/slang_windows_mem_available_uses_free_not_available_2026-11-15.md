# slang Windows fit check used FreePhysicalMemory (excludes standby cache)

Date: 2026-11-15. Status: fixed in `model_loader/memory_budget.spl`.

## Symptom
After reading multi-GB model files, slang refused a 256M-parameter model with
"needs 10 GiB (0 GiB weights + 6 GiB runtime + 3 GiB headroom) but only 6 GiB is
available" for 30+ minutes while the OS reported ~38 GiB available.

## Cause
Windows lane of `mem_available_bytes()` returned `Win32_OperatingSystem.FreePhysicalMemory`,
which excludes the standby (file cache) list. Linux uses MemAvailable (reclaimable cache counts).

## Measurements (2026-11-15, host heavily loaded, 7B GGUF already cached; `build/probe/mem_probe.shs`)
| probe | before | after re-read | wall (s) |
|---|---|---|---|
| FreePhysicalMemory | 26.56 GB | 26.25 GB | 54 / 105 |
| PerfOS_Memory AvailableBytes | 27.05 GB | 27.05 GB | 135 / 79 |
| Get-Counter Available Bytes | 26.29 GB | 27.58 GB | 92 / 67 |

The collapse itself was not reproduced here (file was already cached, so standby was small);
wall times are load noise. Fix rests on the documented definition: AvailableBytes = free + zero + standby.

## Fix
Windows lane uses `Win32_PerfFormattedData_PerfOS_Memory.AvailableBytes` (CIM, not localised
like Get-Counter paths); -1 on probe failure still refuses. Verified: `mem_available_bytes()` = 29.3 GB.

## Related, unchanged
`_runtime_overhead_bytes()` in `engine/llm_engine.spl:219` is a flat 6 GiB regardless of model
size or context (documented as a deliberately conservative admission figure).
