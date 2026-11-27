# bash_net_blocker.shs: known bypass forms (fail-closed gaps)

- Found: Fable review of the ctx hint-hooks fix, 2026-11-26 (59 crafted PreToolUse payloads, `sh` and `dash`).
- Hook: `.claude/hooks/bash_net_blocker.shs` (blocks curl/wget/inline HTTP in Bash).

## Allowed at both base and after the fix
- `"curl" http://x` (quoted command name)
- `/usr/bin/curl http://x` (absolute path)
- `cu\` + newline + `rl http://x` (line continuation)
- a JSON payload with a second `"command"` key: the later one wins in Claude Code, but the hook reads the first

## Allowed after the fix (was denied at base)
- `echo '<<"EOF"'` + newline + `curl http://x`: a quoted heredoc tag inside a string makes the heredoc skip swallow the next line. The same hole exists at base with an unquoted `<<EOF`.

## Not a hole
- `\u0063url`: the hook doesn't decode `\uXXXX`, and neither does the shell, so it isn't `curl`.

## Expected
Normalise the command before matching: strip quotes from the command word, take the basename, join backslash-newline continuations, and only skip heredoc bodies that a real heredoc operator opened. Parse JSON so the last `command` key is the one checked.
