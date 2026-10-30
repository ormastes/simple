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
