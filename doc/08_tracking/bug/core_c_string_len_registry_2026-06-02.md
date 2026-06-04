# core-c `.len()` returns garbage — rt_string_len registry check rejects compiler literals (2026-06-02)

## Summary

On the macOS ARM64 **core-c** native lane, `text.len()` returns garbage for
**every** string — even a literal: `"abc".len() == 3` is **false**. This
silently breaks all string-length-dependent code (substring/slice, line
stripping, JSON parsing), so the native MCP server compiles and links but
cannot process any request.

The bug does **not** reproduce in the interpreter (`bin/simple run`), where
`"...".len()` is correct.

## Root cause

`.len()` lowers to `rt_string_len`, which in the C runtime
(`src/runtime/runtime_native.c`) is:

```c
int64_t rt_string_len(int64_t string) {
    RtCoreString* s = rt_core_as_string(string);
    return s ? (int64_t)s->len : -1;
}
```

`rt_core_as_string` requires the string to be present in a runtime registry:

```c
static int rt_core_is_registered_string(RtCoreString* s) {
    for (size_t i = 0; i < rt_core_string_registry_len; i++)
        if (rt_core_string_registry[i] == s) return 1;
    return 0;
}
```

Compiler-emitted string literals (and concatenation results) are **never
registered**, so `rt_core_as_string` returns NULL and `rt_string_len` returns
`-1`. The caller unboxes `-1` to `0x1FFFFFFFFFFFFFFF` (= `-1 >> 3`), the garbage
length observed. `print_raw` / `starts_with` / `+` concatenation all work
because they read the string `kind`/`data` directly and do **not** go through
the registry check — only the `rt_core_as_string` path is stricter.

## Repro

```
# core-c native binary, even on a literal:
cat > /tmp/len_probe.spl <<'EOF'
extern fn print_raw(s: text)
fn main() -> i64:
    if "abc".len() == 3: print_raw("OK\n") else: print_raw("BAD\n")
    0
EOF
SIMPLE_LIB=src <driver> native-build --runtime-bundle core-c --source src/app \
  --entry-closure --entry /tmp/len_probe.spl --output /tmp/len_bin
/tmp/len_bin </dev/null     # prints BAD
```

## Impact

- The native MCP server (`bin/simple_mcp_server`) cannot parse requests on the
  core-c lane: `read_stdin_message` → `_strip_line_end` uses `.len()`.
- Any string-heavy program built on the core-c lane is affected.

## Fix options

1. **Preferred (pure Simple):** migrate the core-c lane's runtime to the
   pure-Simple `simple_core` (`src/runtime/simple_core/core_string.spl:77`),
   whose `rt_string_len` checks the tag and reads `len` with **no registry**.
   This fixes the bug by construction. See feature request
   `simple_core_runtime_completeness_2026-06-02.md` and plan
   `mcp_simple_core_runtime_migration_2026-06-02.md`.
2. **C runtime fix (if pure-Simple migration is deferred):** drop the
   `rt_core_is_registered_string` gate from `rt_core_as_string` (read `kind`
   directly, like the other accessors), or register literal strings. NOTE:
   direct edits to `src/runtime/*.c` are currently reverted by policy — the
   project wants the pure-Simple path.

## Related

- `core_c_stdin_fgetc_hang_2026-06-02.md` (fixed) — sibling core-c stdin bug.
- `mcp_redeploy_smoke_failures_2026-06-01.md` — original redeploy failures
  (`.weak` + duplicate symbols), now fixed in the seed.
