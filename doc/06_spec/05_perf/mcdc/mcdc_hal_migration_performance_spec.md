# MC/DC + HAL migration-checker performance evidence

`scripts/check/mcdc_hal_migration_performance.spl` runs the Pure Simple checker
exactly once through `/usr/bin/time`. Evidence is rejected unless it includes
whole-process wall seconds and peak RSS KiB. The checker itself reports scan
microseconds, files, source bytes, files/second, exact file-read count, and one
inventory process. No portable threshold is asserted until an admitted
self-hosted binary can measure the current repository; missing measurements are
not a PASS.
