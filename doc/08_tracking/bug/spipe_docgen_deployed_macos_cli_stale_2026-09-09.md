# Deployed macOS CLI cannot regenerate the rendering knowledge manual

Date: 2026-09-09

Status: blocked on a current admitted pure-Simple CLI; generated manual remains stale.

## Affected output

- Source: `test/02_integration/app/llm_process/knowledge_routing_process_spec.spl`
- Manual: `doc/06_spec/02_integration/app/llm_process/knowledge_routing_process_spec.md`
- Source SHA-256: `5e966b4510149fa83da24e4d1b846082085f06786b6969226c010d2f0e8de3e5`
- Existing manual SHA-256: `d113f027f1d77f5aee0405436ff768cf0591008717a58cd6d38077fda578d490`

The source includes the new exact-feature/longest-prefix selection and sibling
prefix-boundary steps. Both steps are absent from the existing manual. Three
scenario headings and folded executable blocks alone do not establish freshness.

## Executable identity

`bin/release/macos-arm64/simple` is an arm64 Mach-O with modification date
April 11 and SHA-256
`277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767`.
The deployed binary contains native Simple CLI symbols. Its observed command
dispatch and source-run behavior differ from the current source tree.

## Failure before docgen dispatch

Sol's command exited 133 without generator output:

```sh
SIMPLE_NO_STUB_FALLBACK=1 bin/release/macos-arm64/simple spipe-docgen \
  test/02_integration/app/llm_process/knowledge_routing_process_spec.spl \
  --output doc/06_spec --no-index
```

A bounded LLDB run set a breakpoint on
`cli__main__print_error_with_help`. The breakpoint fired directly from
`spl_main + 9928`; the string argument contains `File not found: spipe-docgen`.
The installed CLI treats the unsupported subcommand as a filename. The current
source already routes it through `cli_run_spipe_docgen` in
`src/app/cli/_CliMain/main_and_help.spl` and
`src/app/io/_CliCommands/run_commands.spl`.

The corresponding macOS crash report,
`/Users/ormastes/Library/Logs/DiagnosticReports/simple-2026-09-09-015249.ips`,
records `EXC_BREAKPOINT`/`SIGTRAP` and
`BUG IN CLIENT OF LIBMALLOC: memory corruption of free block`. Its stack enters
`rt_string_new`, `_cli_shell`, file-existence checks, `get_version`,
`print_cli_help`, and `print_error_with_help`. This is a secondary help-path
allocator failure; the allocation that corrupted memory has not been isolated.

Debugger evidence: `build/spipe-docgen-ui-20260909/dispatch-lldb.log`.

## Source-entry attempt also cannot execute the generator

One bounded alternative used the same deployed runtime and canonical source:

```sh
timeout 60s env SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_LIB=src \
  bin/release/macos-arm64/simple run src/app/spipe_docgen/main.spl \
  test/02_integration/app/llm_process/knowledge_routing_process_spec.spl \
  --output doc/06_spec --no-index
```

Result: exit 1 immediately, only
`[STDERR] Error running src/app/spipe_docgen/main.spl`.
The generator prints no processing or completion output.

LLDB resolved the call from `io__cli_commands__cli_run_file` to
`driver__driver_api_interpret__interpret_file`. A breakpoint at
`io__cli_commands__cli_run_file + 32`, immediately after that call, observed
`x0 = 0x3` (tagged nil). The caller then tests an expected result discriminant
and takes its error path. The precise origin of this invalid return inside the
obsolete compiler remains unproven; it is not evidence of a source-spec error.

Evidence:

- `build/spipe-docgen-ui-20260909/canonical-source-run.log`
- `build/spipe-docgen-ui-20260909/run-result-lldb.log`
- `build/spipe-docgen-ui-20260909/interpret-value-lldb.log`
- `build/spipe-docgen-ui-20260909/run-disassembly.log`
- `build/spipe-docgen-ui-20260909/interpret-disassembly.log`

No docgen or executable-spec source was changed. No generated Markdown was
hand-edited. No Rust seed or broad bootstrap was used for regeneration.

## Required closure

After the existing bootstrap lane supplies a current admitted pure-Simple CLI,
run the canonical `spipe-docgen` command above once with that executable. Require
exit 0, `1 complete, 0 stubs`, both new visible steps, and current folded
scenario source. Preserve that run's executable/source/output identities.

The focused source whitespace check passed. The executable-spec layout scan
returned zero `*_spec.spl` files under `doc/06_spec`. These checks do not close
the missing regeneration evidence or establish a generator PASS.
