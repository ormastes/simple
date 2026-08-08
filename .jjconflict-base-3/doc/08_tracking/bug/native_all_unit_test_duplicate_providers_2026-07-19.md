# Native-all unit tests linked duplicate runtime providers

- **Status:** provider ownership fixed; focused regressions passed
- **Observed:** the focused atomic-write unit test failed to link because native-all and its simple-runtime dependency both exported `rt_process_exists` and `print_raw`.
- **Cause:** native-all duplicated canonical simple-runtime providers. Its `rt_process_exists` also checked Linux `/proc`, while simple-runtime only checked its spawned-child registry; neither matched the public arbitrary-PID contract portably.
- **Fix:** remove both native-all duplicates. Simple-runtime remains the sole `print_raw` owner and now implements OS-wide positive-PID existence checks on Unix and Windows.
- **Regression:** simple-runtime tests require the current PID to exist and zero/negative PIDs not to exist; `cargo test -p simple-native-all --lib atomic_write_file_replaces_complete_content_and_fails_closed -- --exact` linked and passed.
