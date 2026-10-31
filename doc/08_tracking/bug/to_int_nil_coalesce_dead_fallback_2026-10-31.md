# `text.to_int() ?? default` never takes the default

Status: OPEN
Date: 2026-10-31

`to_int()` is typed `i64` and returns 0 when text has no leading digits, in the seed
(`interpreter_method/string.rs`) and in native (`rt_string_to_int_lenient`). So `??` on it is dead
code and non-numeric input silently reads as 0. A seed survey found the pattern on 313 of 441
`.to_int()` lines in `src/app` and `src/lib`; that is a line count, not a bug count, and sites were
not reviewed one by one.

Real instance fixed: `src/os/apps/smux/server.spl` (nonnumeric declared body length).

Unblock: migrate call sites that must distinguish bad input to the optional `parse_int()`, site by
site, and add a lint for `?? ` on a non-optional. Same class as
`env_get_nil_coalesce_dead_fallback_2026-07-25.md`.

## Update 2026-10-31 (relfix-tooling)

`parse_int()` verified on the seed: nil for `""`, `"abc"`, `"12x"`; value for `"42"`, `"-5"`, `" 7"`.
Seed `to_int()` returns 0 for ANY non-clean text (`"12x"` -> 0), so on the seed these migrations are
behaviour-neutral: every migrated site has a `<= 0 -> default` guard or defaults to 0. They matter
under native `rt_string_to_int_lenient` (leading digits parsed: `"12x"` -> 12, now the default).
No spec can be red on the seed for that reason; specs pin the contract only.

Migrated to `parse_int()` (untrusted/external input), 19 sites: llm_caret/cs_main (COLUMNS/LINES env),
smux client_view (frame dims), interactive_protocol (4), smux_remote (6 parse calls on 4 lines),
mcp main_lazy_ctx_tools (2), main_lazy_node_tools, cli_passthrough, bootstrap main_lazy/_v2/_optimized
(Content-Length). Specs: client_view_spec, mcp_untrusted_int_parse_spec.

Remaining `to_int() ??` lines: smux 11 (client_leases, server:37,82 [digit-gated], smux_remote:341,
vt_screen x8 [terminal escape params; 0 is the VT default, intended]), mcp 10 (ctx_tools 189/210/215/351
and telemetry rows read from own stored data, not external input). llm_caret 0.
