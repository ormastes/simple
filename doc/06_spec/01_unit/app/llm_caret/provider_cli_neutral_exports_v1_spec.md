# Provider CLI neutral compatibility exports

Source: `test/01_unit/app/llm_caret/provider_cli_neutral_exports_v1_spec.spl`.
Status: authored source, **NOT_RUN**. This manual is maintained alongside the
specification; it is not generated execution evidence.

Caret's existing adapter imports now reexport the same definitions from neutral
library modules. A value decoded through the old application import must pass
directly into the neutral probe planner and produce `--version`. A version value
returned by the neutral decoder must pass to a function typed through the old
application import. A Claude-shaped version string must still be rejected for
Codex. These three cases check compatibility and a negative boundary.

The source move preserves the opaque contained-probe implementation, including
private fields, capture cleanup and diagnostic copies. These pure compatibility
cases do not exercise real containers or prove native capture, selection lifetime,
Host execution, interactive TTY or terminal adoption. Existing contained-probe
specifications remain the qualification requirements for those owners.
