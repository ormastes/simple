# ITF color output through a real subprocess pipe

This executable scenario runs the ITF output owner in a bounded child Simple
process. The process facade captures stdout through a real pipe while
preserving the child exit code; no shell pipeline can mask a failing child.

1. With no color environment override, output contains `ITF_COLOR_PROBE` and
   no ANSI control sequence.
2. With `ITF_FORCE_COLOR=1`, redirected output contains an ANSI sequence.
3. With both `NO_COLOR=1` and force enabled, `NO_COLOR` wins and output remains
   plain.

Executable source:
`test/02_integration/app/itf_color_pipe_spec.spl`.
