# Phase1 Unix millisecond clock extern missing

The original Linux seed sweep failed the JavaScript compatibility spec with unknown extern rt_time_now_unix_millis. Its Date.now example explicitly requires registering the existing native clock rather than changing the assertion.

Register an interpreter provider using the existing native Unix-microsecond bridge. Convert nonnegative microseconds to integer milliseconds and preserve the native -1 failure sentinel. Avoid floating-point conversion and introduce no clock substitute.

A parsed-Simple registration regression failed before the repair and passed afterward. It requires the timestamp to fall within the actual host Unix-epoch millisecond interval, so a positive monotonic or incorrectly scaled value cannot pass. One namespace compile error was corrected to use the public value::sffi bridge. Enforcing watchdog evidence records exit 0, quiescent 1, peak 4807140 KiB, and maximum sample gap 3069 ms. Evidence is retained under /tmp/simple-unix-millis-repair.

The original Date.now example still needs verification on a newly built seed. Whole seed and subsequent phase qualification remain pending.
