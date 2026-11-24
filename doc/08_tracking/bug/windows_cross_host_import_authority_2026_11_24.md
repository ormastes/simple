# Windows cross-host import authority

The Linux-hosted MinGW Stage2 in manual run 45326410090 (source
656fa39e28a7775da0172a4e8eeeea1ac0ea59f0) linked successfully but emitted
`Thread32First` and `Thread32Next` as fabricated functions returning 3.
The original compiler SHA256 is
`51eaa8c3f9ecacf282cfb52dbee16b29f6220d5cf6e6acad73b4a8bcc412b093`.
Native Windows proof 45336523681 passed `--version`, then timed out after
600 seconds compiling the tracked Hello fixture, with no output and a
28,560 KiB peak. The Job owner enforced its cap and reported quiescence.

The disassembled providers at 0x140001c20 and 0x140001c30 both contain
`b8 03 00 00 00 c3`. The runtime's `resume_primary` loops while
`Thread32Next` succeeds. This proves invalid providers; the exact timeout
stack was not captured and must not be claimed as observed.

The GNU import-library scanner was compiled only on Windows hosts. The
non-Windows link path passed an empty system-library list to shim generation,
even for a Windows GNU output. Select actual target archives in that path,
using the same driver/search ordering as native Windows. Only Windows GNU
outputs opt in; native ELF, MSVC and clang-cl paths retain their behavior.
An optional driver target argument preserves target-prefixed GCC invocation;
failed driver output cannot become archive authority.

## Evidence and limits

- Earlier source-bound resolver/scanner/PE-link proof 45276843909 passed
  Clang/GNU discovery, failed-driver rejection, explicit-search precedence
  and actual ToolHelp imports. Its Windows helper did not execute. All three
  old helper cycles are exhausted and are not repeated by this repair.
- `check-windows-cross-caller.py` executes the production cross-host selection
  statements, resolver, target-flag helper and symbol scanner against real
  toolchain archives. Its small target adapter is test plumbing, not a product
  compiler. It checks Windows GNU selection and Linux/MSVC/clang-cl exclusions.
- Any retained-object replay first requires equivalence with the original PE,
  except explicitly enumerated metadata fields. A changed generated stub
  object and native Hello are diagnostic evidence, not a rebuilt compiler or
  formal bootstrap admission.
- Exact corrected-head verification and mandatory applicable broader gates
  remain pending until recorded. No previous bootstrap/compiler success is
  inferred from this source change.
