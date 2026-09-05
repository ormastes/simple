# Missing FFI Wrappers

Found 100 FFI functions without wrappers.

## Wrappers to Add

Add these to `src/app/io/mod.spl`:

```simple
# TODO: Add wrapper for rt_cargo_build
fn cargo_build(...) -> ...:
    rt_cargo_build(...)

# TODO: Add wrapper for rt_cargo_check
fn cargo_check(...) -> ...:
    rt_cargo_check(...)

# TODO: Add wrapper for rt_cargo_clean
fn cargo_clean(...) -> ...:
    rt_cargo_clean(...)

# TODO: Add wrapper for rt_cargo_fmt
fn cargo_fmt(...) -> ...:
    rt_cargo_fmt(...)

# TODO: Add wrapper for rt_cargo_lint
fn cargo_lint(...) -> ...:
    rt_cargo_lint(...)

# TODO: Add wrapper for rt_cargo_test
fn cargo_test(...) -> ...:
    rt_cargo_test(...)

# TODO: Add wrapper for rt_cargo_test_doc
fn cargo_test_doc(...) -> ...:
    rt_cargo_test_doc(...)

# TODO: Add wrapper for rt_cli_exit
fn cli_exit(...) -> ...:
    rt_cli_exit(...)

# TODO: Add wrapper for rt_cli_file_exists
fn cli_file_exists(...) -> ...:
    rt_cli_file_exists(...)

# TODO: Add wrapper for rt_cli_get_args
fn cli_get_args(...) -> ...:
    rt_cli_get_args(...)

# TODO: Add wrapper for rt_cli_handle_compile
fn cli_handle_compile(...) -> ...:
    rt_cli_handle_compile(...)

# TODO: Add wrapper for rt_cli_handle_diagram
fn cli_handle_diagram(...) -> ...:
    rt_cli_handle_diagram(...)

# TODO: Add wrapper for rt_cli_handle_linkers
fn cli_handle_linkers(...) -> ...:
    rt_cli_handle_linkers(...)

# TODO: Add wrapper for rt_cli_handle_run
fn cli_handle_run(...) -> ...:
    rt_cli_handle_run(...)

# TODO: Add wrapper for rt_cli_handle_web
fn cli_handle_web(...) -> ...:
    rt_cli_handle_web(...)

# TODO: Add wrapper for rt_cli_read_file
fn cli_read_file(...) -> ...:
    rt_cli_read_file(...)

# TODO: Add wrapper for rt_cli_run_brief
fn cli_run_brief(...) -> ...:
    rt_cli_run_brief(...)

# TODO: Add wrapper for rt_cli_run_check
fn cli_run_check(...) -> ...:
    rt_cli_run_check(...)

# TODO: Add wrapper for rt_cli_run_code
fn cli_run_code(...) -> ...:
    rt_cli_run_code(...)

# TODO: Add wrapper for rt_cli_run_constr
fn cli_run_constr(...) -> ...:
    rt_cli_run_constr(...)

# TODO: Add wrapper for rt_cli_run_diff
fn cli_run_diff(...) -> ...:
    rt_cli_run_diff(...)

# TODO: Add wrapper for rt_cli_run_feature_gen
fn cli_run_feature_gen(...) -> ...:
    rt_cli_run_feature_gen(...)

# TODO: Add wrapper for rt_cli_run_ffi_gen
fn cli_run_ffi_gen(...) -> ...:
    rt_cli_run_ffi_gen(...)

# TODO: Add wrapper for rt_cli_run_file
fn cli_run_file(...) -> ...:
    rt_cli_run_file(...)

# TODO: Add wrapper for rt_cli_run_fix
fn cli_run_fix(...) -> ...:
    rt_cli_run_fix(...)

# TODO: Add wrapper for rt_cli_run_fmt
fn cli_run_fmt(...) -> ...:
    rt_cli_run_fmt(...)

# TODO: Add wrapper for rt_cli_run_gen_lean
fn cli_run_gen_lean(...) -> ...:
    rt_cli_run_gen_lean(...)

# TODO: Add wrapper for rt_cli_run_info
fn cli_run_info(...) -> ...:
    rt_cli_run_info(...)

# TODO: Add wrapper for rt_cli_run_lex
fn cli_run_lex(...) -> ...:
    rt_cli_run_lex(...)

# TODO: Add wrapper for rt_cli_run_lint
fn cli_run_lint(...) -> ...:
    rt_cli_run_lint(...)

# TODO: Add wrapper for rt_cli_run_mcp
fn cli_run_mcp(...) -> ...:
    rt_cli_run_mcp(...)

# TODO: Add wrapper for rt_cli_run_migrate
fn cli_run_migrate(...) -> ...:
    rt_cli_run_migrate(...)

# TODO: Add wrapper for rt_cli_run_query
fn cli_run_query(...) -> ...:
    rt_cli_run_query(...)

# TODO: Add wrapper for rt_cli_run_repl
fn cli_run_repl(...) -> ...:
    rt_cli_run_repl(...)

# TODO: Add wrapper for rt_cli_run_replay
fn cli_run_replay(...) -> ...:
    rt_cli_run_replay(...)

# TODO: Add wrapper for rt_cli_run_spec_coverage
fn cli_run_spec_coverage(...) -> ...:
    rt_cli_run_spec_coverage(...)

# TODO: Add wrapper for rt_cli_run_spec_gen
fn cli_run_spec_gen(...) -> ...:
    rt_cli_run_spec_gen(...)

# TODO: Add wrapper for rt_cli_run_sspec_docgen
fn cli_run_sspec_docgen(...) -> ...:
    rt_cli_run_sspec_docgen(...)

# TODO: Add wrapper for rt_cli_run_task_gen
fn cli_run_task_gen(...) -> ...:
    rt_cli_run_task_gen(...)

# TODO: Add wrapper for rt_cli_run_tests
fn cli_run_tests(...) -> ...:
    rt_cli_run_tests(...)

# TODO: Add wrapper for rt_cli_run_todo_gen
fn cli_run_todo_gen(...) -> ...:
    rt_cli_run_todo_gen(...)

# TODO: Add wrapper for rt_cli_run_todo_scan
fn cli_run_todo_scan(...) -> ...:
    rt_cli_run_todo_scan(...)

# TODO: Add wrapper for rt_cli_run_verify
fn cli_run_verify(...) -> ...:
    rt_cli_run_verify(...)

# TODO: Add wrapper for rt_cli_watch_file
fn cli_watch_file(...) -> ...:
    rt_cli_watch_file(...)

# TODO: Add wrapper for rt_context_generate
fn context_generate(...) -> ...:
    rt_context_generate(...)

# TODO: Add wrapper for rt_context_stats
fn context_stats(...) -> ...:
    rt_context_stats(...)

# TODO: Add wrapper for rt_coverage_clear
fn coverage_clear(...) -> ...:
    rt_coverage_clear(...)

# TODO: Add wrapper for rt_coverage_dump_sdn
fn coverage_dump_sdn(...) -> ...:
    rt_coverage_dump_sdn(...)

# TODO: Add wrapper for rt_coverage_enabled
fn coverage_enabled(...) -> ...:
    rt_coverage_enabled(...)

# TODO: Add wrapper for rt_current_time_ms
fn current_time_ms(...) -> ...:
    rt_current_time_ms(...)

# TODO: Add wrapper for rt_dir_create
fn dir_create(...) -> ...:
    rt_dir_create(...)

# TODO: Add wrapper for rt_dir_create_all
fn dir_create_all(...) -> ...:
    rt_dir_create_all(...)

# TODO: Add wrapper for rt_dir_list
fn dir_list(...) -> ...:
    rt_dir_list(...)

# TODO: Add wrapper for rt_dir_remove
fn dir_remove(...) -> ...:
    rt_dir_remove(...)

# TODO: Add wrapper for rt_dir_walk
fn dir_walk(...) -> ...:
    rt_dir_walk(...)

# TODO: Add wrapper for rt_env_cwd
fn env_cwd(...) -> ...:
    rt_env_cwd(...)

# TODO: Add wrapper for rt_env_get
fn env_get(...) -> ...:
    rt_env_get(...)

# TODO: Add wrapper for rt_env_home
fn env_home(...) -> ...:
    rt_env_home(...)

# TODO: Add wrapper for rt_env_set
fn env_set(...) -> ...:
    rt_env_set(...)

# TODO: Add wrapper for rt_eprintln
fn eprintln(...) -> ...:
    rt_eprintln(...)

# TODO: Add wrapper for rt_fault_set_execution_limit
fn fault_set_execution_limit(...) -> ...:
    rt_fault_set_execution_limit(...)

# TODO: Add wrapper for rt_fault_set_max_recursion_depth
fn fault_set_max_recursion_depth(...) -> ...:
    rt_fault_set_max_recursion_depth(...)

# TODO: Add wrapper for rt_fault_set_stack_overflow_detection
fn fault_set_stack_overflow_detection(...) -> ...:
    rt_fault_set_stack_overflow_detection(...)

# TODO: Add wrapper for rt_fault_set_timeout
fn fault_set_timeout(...) -> ...:
    rt_fault_set_timeout(...)

# TODO: Add wrapper for rt_file_append_text
fn file_append_text(...) -> ...:
    rt_file_append_text(...)

# TODO: Add wrapper for rt_file_atomic_write
fn file_atomic_write(...) -> ...:
    rt_file_atomic_write(...)

# TODO: Add wrapper for rt_file_copy
fn file_copy(...) -> ...:
    rt_file_copy(...)

# TODO: Add wrapper for rt_file_delete
fn file_delete(...) -> ...:
    rt_file_delete(...)

# TODO: Add wrapper for rt_file_exists
fn file_exists(...) -> ...:
    rt_file_exists(...)

# TODO: Add wrapper for rt_file_lock
fn file_lock(...) -> ...:
    rt_file_lock(...)

# TODO: Add wrapper for rt_file_modified_time
fn file_modified_time(...) -> ...:
    rt_file_modified_time(...)

# TODO: Add wrapper for rt_file_read_lines
fn file_read_lines(...) -> ...:
    rt_file_read_lines(...)

# TODO: Add wrapper for rt_file_read_text
fn file_read_text(...) -> ...:
    rt_file_read_text(...)

# TODO: Add wrapper for rt_file_remove
fn file_remove(...) -> ...:
    rt_file_remove(...)

# TODO: Add wrapper for rt_file_size
fn file_size(...) -> ...:
    rt_file_size(...)

# TODO: Add wrapper for rt_file_unlock
fn file_unlock(...) -> ...:
    rt_file_unlock(...)

# TODO: Add wrapper for rt_file_write_text
fn file_write_text(...) -> ...:
    rt_file_write_text(...)

# TODO: Add wrapper for rt_getpid
fn getpid(...) -> ...:
    rt_getpid(...)

# TODO: Add wrapper for rt_glob
fn glob(...) -> ...:
    rt_glob(...)

# TODO: Add wrapper for rt_hostname
fn hostname(...) -> ...:
    rt_hostname(...)

# TODO: Add wrapper for rt_package_file_size
fn package_file_size(...) -> ...:
    rt_package_file_size(...)

# TODO: Add wrapper for rt_package_is_dir
fn package_is_dir(...) -> ...:
    rt_package_is_dir(...)

# TODO: Add wrapper for rt_package_remove_dir_all
fn package_remove_dir_all(...) -> ...:
    rt_package_remove_dir_all(...)

# TODO: Add wrapper for rt_path_basename
fn path_basename(...) -> ...:
    rt_path_basename(...)

# TODO: Add wrapper for rt_process_output
fn process_output(...) -> ...:
    rt_process_output(...)

# TODO: Add wrapper for rt_process_run
fn process_run(...) -> ...:
    rt_process_run(...)

# TODO: Add wrapper for rt_process_run_timeout
fn process_run_timeout(...) -> ...:
    rt_process_run_timeout(...)

# TODO: Add wrapper for rt_process_run_with_limits
fn process_run_with_limits(...) -> ...:
    rt_process_run_with_limits(...)

# TODO: Add wrapper for rt_read_file
fn read_file(...) -> ...:
    rt_read_file(...)

# TODO: Add wrapper for rt_settlement_main
fn settlement_main(...) -> ...:
    rt_settlement_main(...)

# TODO: Add wrapper for rt_shell
fn shell(...) -> ...:
    rt_shell(...)

# TODO: Add wrapper for rt_shell_exec
fn shell_exec(...) -> ...:
    rt_shell_exec(...)

# TODO: Add wrapper for rt_system_cpu_count
fn system_cpu_count(...) -> ...:
    rt_system_cpu_count(...)

# TODO: Add wrapper for rt_time_now_unix_micros
fn time_now_unix_micros(...) -> ...:
    rt_time_now_unix_micros(...)

# TODO: Add wrapper for rt_timestamp_get_day
fn timestamp_get_day(...) -> ...:
    rt_timestamp_get_day(...)

# TODO: Add wrapper for rt_timestamp_get_hour
fn timestamp_get_hour(...) -> ...:
    rt_timestamp_get_hour(...)

# TODO: Add wrapper for rt_timestamp_get_minute
fn timestamp_get_minute(...) -> ...:
    rt_timestamp_get_minute(...)

# TODO: Add wrapper for rt_timestamp_get_month
fn timestamp_get_month(...) -> ...:
    rt_timestamp_get_month(...)

# TODO: Add wrapper for rt_timestamp_get_second
fn timestamp_get_second(...) -> ...:
    rt_timestamp_get_second(...)

# TODO: Add wrapper for rt_timestamp_get_year
fn timestamp_get_year(...) -> ...:
    rt_timestamp_get_year(...)

```
