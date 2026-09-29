**Split receipt conversion from `to_win_path`; adding `-a` is not a demonstrated fix.** No files changed, tests run, or links touched.

The [state](/C:/Users/ormas/dev/simple/.spipe/windows_full_bootstrap_toolchain_suite/state.md:85) records the older undefined-helper failure. Your current failure occurs at [fixture line 250](/C:/Users/ormas/dev/simple/test/01_unit/scripts/materialize_symlinks_windows_test.shs:249), before producer invocation. It proves the suffix assertion failed—not, independently, what replacement pathname resulted. The [Astra diagnosis](/C:/Users/ormas/dev/simple/.spipe/windows_full_bootstrap_toolchain_suite/astra_receipt_ancestor_status0_diagnostic.md:12) recommends lexical preservation.

Installed help identifies MSYS2 `cygpath` 3.6.5 and Git-Bash 3.5.4. Both describe `-a` only as “output absolute path.” No advertised option guarantees non-resolving conversion. The [local manual](/C:/dev/tool/msys2/usr/share/man/man1/cygpath.1:135) describes `-r` as adding `\\?\`, allowing otherwise-invalid DOS components—not disabling junction traversal. Absolute-path normalization and filesystem-link resolution are distinct operations. Local evidence does **not** establish their implementation relationship; no conversion probes were performed.

Proposed minimal changes:

- At [producer line 424](/C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:424), add a dedicated lexical receipt converter. Accept only `/[A-Za-z]/component/.../leaf`; uppercase the drive letter and replace separators using string operations. Never call `cygpath`, `realpath`, `readlink`, `Resolve-Path`, or change directories on this input.
- Reject UNC explicitly; also relative/native/device paths, unsupported mounts (`/tmp`, `/var/tmp`, `/cygdrive`, `/proc`), backslashes, repeated/trailing separators, `.`/`..`, controls, invalid Unicode, colons, Windows-forbidden characters, trailing dots/spaces, and case-insensitive reserved names including extension forms and superscript COM/LPT digits. NUL cannot occur in argv. Preserve valid Unicode, internal spaces, apostrophes, `$`, backticks, brackets, semicolons and ampersands verbatim.
- Tighten [receipt admission](/C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:117) consistently. At line 438, convert once; retain the existing shared `receipt_path_win` for prepare and publish (line 679). Keep quoted environment transport at line 414; explicitly exclude these variables from MSYS environment conversion and verify Unicode transport.
- Preserve [root-first validation](/C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:241). Require ordinal equality between validated native input and `Path.GetFullPath` before use, including rename construction at line 367: normalization must not silently change accepted spelling.

Focused assertions, **proposed only**:

- Build the fixture beneath an explicit drive path, avoiding default `/tmp`. Before creating the junction, retain independent lexical native alias/target spellings; use the alias spelling for its numeric tag oracle.
- Replace lines 249–251 with exact expected-path comparison, preserving `\output-alias\new\receipt.env`.
- A delegating PowerShell wrapper captures actual prepare/publish destination environment values. Assert exact equality, no target-resolved spelling, prepare rejection naming `output-alias`, no publish, and no receipt or `real-output/new`.
- Add conversion rejection tables and a safe Unicode/metacharacter success case proving identical prepare/publish inputs. Static assertions forbid resolving calls in receipt conversion.

General `to_win_path` may remain for non-security-sensitive targets; it must not establish receipt ancestry or preserved alias identity.