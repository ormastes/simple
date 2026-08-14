# `@export("C", name: ...)` ignored under `--no-mangle`

Status: provider workaround applied; compiler export-name fix remains open.

The admitted Stage 2 compiler successfully built the Pure Simple provider
archive, but `nm -D` on the linked shared object exposed
`pure_simple_provider_query_v1` and `pure_simple_cli_command_invoke_v1` instead
of the requested `simple_provider_query_v1` and
`simple_cli_command_invoke_v1` names.

Provider fix: declare the two functions with their exact ABI symbol names and
retain `@export("C")` plus `--no-mangle`. This is deterministic and avoids a
linker alias shim. The compiler should separately make the `name:` attribute
authoritative under no-mangle builds.
