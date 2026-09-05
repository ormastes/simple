# Core-C native paths could not resolve `text.strip`

- **Status:** pure-Simple dispatch fixed; fresh runtime regression pending
- **Observed:** the strict pure-Simple lint binary accepted a clean file, then crashed with `function not found: str.strip` on a deny fixture.
- **Cause:** `strip()` is a documented public alias implemented by the Rust interpreter and stdlib, but pure-Simple interpreter, C generation, and MIR native lowering only dispatched `trim()`.
- **Partial fix:** interpreter dispatch and the unresolved MIR text-special path
  route both public spellings through the existing trim implementation. The
  admitted Phase-2 native lint object nevertheless retained three undefined
  `str.strip` references for resolved chained `slice(...).strip()` calls. The
  bounded lint unblock changes only those three TODO/FIXME parser calls to the
  semantic alias `.trim()`.
- **Current evidence (2026-08-15):** core-C lint reached link after 252
  transaction objects, then exited 1 with `str.strip` and
  `rt_file_atomic_write` unresolved. Evidence is retained at
  `build/essential_tools_phase2_corec/logs/lint.build.{log,status,time}`.
- **Remaining regression:** keep the public contract
  `"  hello  ".strip() == "hello"`, and add a direct native chained receiver
  fixture such as `s.slice(0, s.len()).strip()`. The durable MIR fix must allow
  the text-special arm for a resolved primitive `Str` receiver while
  preserving custom-owner precedence. The next lint tool build must use a
  fresh current core-C runtime provider (the admitted generic runtime root
  lacks `rt_file_atomic_write`) and must exit 1/T001 on the deny fixture rather
  than fail at link.
