# Generic counted-stdin command admission values

Source: [stdin_command_contract_v1_spec.spl](../../../../../test/01_unit/lib/io/stdin_command_contract_v1_spec.spl).
Manually authored companion; **NOT_RUN**. These source cases check pure
admission values and claim no process, file, environment or platform effects.

## Manual flow represented by the assertions

1. Validate executable identity as exactly 64 lowercase hexadecimal SHA-256
   characters. Reject missing, short/long, uppercase, nonhex and prefixed forms.
2. Validate safe absolute POSIX paths and forward-slash drive paths through the
   same generic contract, including protected-store journal paths.
3. Reject relative/drive-relative and root-only paths, UNC, ADS, traversal,
   empty path segments, backslash-drive spelling, command options, shell syntax,
   NUL and newline before effects.

The facade `std.nogc_sync_mut.io.stdin_command_v1` selects POSIX or Windows
owners below the application boundary. These assertions cover its path/digest
grammar only. They do not hash an executable, establish file identity or ACLs,
launch a counted-stdin process, bound a native job, cancel it or collect its
handles. Windows launch additionally depends on the retained Windows stdin
command owner and protected credential-store admission; source path acceptance
does not prove those providers are admitted.

Requirements: REQ-002/003 and NFR-002/003 for the admission boundary. See the
[SSH manual](../../app/orchestrator/server_ssh_v1_spec.md) and
[verification plan](../../../../03_plan/sys_test/server_contexts.md) for the
pending runtime/lifecycle gates.

Prevention cases additionally retain ASCII path acceptance, reject multibyte executable suffixes, accept allowed Unicode private-root components and reject controls/forbidden punctuation following multibyte root components. These authored cases are NOT_RUN; no truncation failure was experimentally reproduced.
