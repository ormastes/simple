# Explicit Codex prompt-mode planning

Status: AUTHORED_NOT_RUN. Uses the real production DATA planner, no CLI tasks.

1. Explicit Argv mode must put the option terminator before each untrusted prompt,
   keep it one exact argument and clear stdin DATA. Test flag-like text, `resume`,
   `--`, command-substitution text and newline without executing any text.
2. Stdin must preserve the original production plan. Resume Argv planning keeps
   the exact selected session DATA and places its prompt after the delimiter;
   this does not supply session/history ownership for actual Resume effects.
3. Exactly 2048 two-byte characters must measure 4096 bytes and succeed as DATA;
   2049 must refuse. Literal `-`, unknown version/family and non-task actions
   must refuse Argv mode. No fallback to stdin is permitted.

Actual container closed-stdin/non-TTY observation, input-constraint enforcement,
native prompt delivery and task completion are NOT_COVERED by these DATA tests.
