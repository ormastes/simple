# core-c `.len()` returns garbage — rt_string_len registry check rejects compiler literals (2026-06-02)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

## 2026-08-17 verification — runtime lane (classified by CONTENT, not SHA)

**Verdict: ALREADY-FIXED in source; execution proof NOT obtained.**

The defect this doc describes is `rt_string_len` returning `-1` for a
compiler-emitted literal that the string registry does not know. Current source
(`src/runtime/runtime_native.c:2525-2529`, note: the doc header's `:2509` is
stale, the function moved) no longer has that shape:

```c
int64_t rt_string_len(int64_t string) {
    RtCoreString* s = rt_core_as_string(string);
    if (s) return (int64_t)s->len;
    return string >= 0x10000 ? (int64_t)strlen((const char*)(uintptr_t)string) : -1;
}
```

The registry-miss branch now falls back to `strlen` on the raw pointer instead of
returning `-1`, which is exactly the unregistered-literal case the repro
exercises. `-1` now survives only for values below `0x10000`, i.e. not a
pointer at all. Additionally literals are now interned and registered through
`rt_string_new_uncached_persistent` (`:2507-2521`), so the registry miss is
itself much rarer than when this was filed.

**What was NOT proven.** `rt_string_len` is C-runtime code reached only by a
NATIVE-compiled binary. The deployed `bin/simple` is the Rust seed and its
interpreter/JIT use the Rust runtime, so `bin/simple run` cannot exercise this
function — an interpreted probe printed the correct `5` / `14` but proves
nothing about this line. A native/core-c build was not run: the native build
pipeline (`pipeline/native_project/**`) is claimed by another lane and a
bootstrap was occupying the host. **Close only after a core-c native binary
runs the repro above and prints `OK`.**

## 2026-08-17 independent re-verification (second runtime lane)

The 2026-08-17 note above was re-checked line-by-line against current source and
is **accurate**: `rt_string_len` is at `src/runtime/runtime_native.c:2525-2529`
with exactly the quoted body, and literal interning + `RT_CORE_STRING_FLAG_SHARED`
are at `:2507-2521`. Its refusal to close is also correct and is upheld — no
core-c native binary was run, and no `Results:` line exists for this row.

**New finding, not in the note above — the fallback is only half-safe.**
`rt_core_as_string` (`:1706-1714`) still gates on `rt_core_is_registered_string`.
It returns NULL for two different populations: (a) an *untagged raw* `char*`,
where `strlen` is the right answer, and (b) a value carrying
`RT_VALUE_TAG_HEAP` whose object is simply not in the registry, where `strlen`
runs on a **tagged, misaligned** address and yields garbage or a segfault rather
than the old honest `-1`. The fallback only rescues case (a). Before closing,
the repro should cover an unregistered *tagged* handle, not just a literal.

Status stays OPEN (P2).
