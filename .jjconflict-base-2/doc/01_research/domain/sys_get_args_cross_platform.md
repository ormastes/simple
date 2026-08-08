<!-- codex-research -->
# Cross-platform `sys_get_args` domain research

POSIX specifies that `exec` arguments arrive as `main(int, char *argv[])`, with
`argv[0]` representing the invoked program and the remaining entries preserved
in order. Linux, macOS, and BSD therefore share the narrow hosted ABI; Simple
must publish that array once before user code starts.

Microsoft documents `wmain(int, wchar_t *argv[])` as the Unicode entry point.
Using it avoids active-code-page loss and preserves spaces, Korean text, emoji,
and other UTF-16 command-line content. The runtime decodes invalid surrogate
sequences lossily rather than dropping an entire argument.

References:

- https://pubs.opengroup.org/onlinepubs/9799919799/functions/exec.html
- https://learn.microsoft.com/en-us/cpp/c-language/using-wmain?view=msvc-170
