# Item 4 Windows native-all dependency repair

Date: 2026-10-04. Overall runtime qualification: **UNRUN**.

The pure-Simple native-all support owner now selects Pdh, NetAPI32, Psapi
and PowrProf for both MSVC and MinGW spellings. The historical Rust-only
repair did not change this owner. Archive selection and non-Windows policy
remain unchanged. This is an implementation increment, not five-host admission.

Tests were committed before the two production array additions. The existing
native-link hardening spec checks each dependency exactly once, both archive
spellings, rejected lookalikes, core-only inputs and non-Windows arrays.
The specs and real SDK link/load checks remain UNRUN; no observed RED/GREEN
cycle, branch coverage or full compiler/MCP test PASS is claimed.

Independent source review of `6c56df3c5d8` against `4190684c8f7` found no P0/P1.
Rebasing onto release `6229a1efd88` preserved all four patches identically
according to `git range-diff`. The intervening release change touched different
files. Whitespace, working/staged direct-env guards and numbered-artifact checks
passed for the source increment.

The test-tree divergence delta passed: zero introduced offenders, 3152 inherited
offenders. Retained list: `.git/item4-windows-native-all-preexisting-offenders.txt`,
SHA256 `2fb68a47bab7953e058a449562ecba2df9f135b8d2e2d99c3e14f373b1c1d719`.
This is a clean delta, not a claim that the whole repository test tree passes.

Separately, the isolated old-source diagnostic prime completed and its minimal
executable ran successfully. See the runner crash report's dated followup.
That diagnostic did not compile this dependency repair or exercise native-all.

Remaining release qualification includes actual SSpec execution, native MSVC
and MinGW SDK-symbol link/load proof, required core/MCP checks, coverage and
the complete Windows/Linux/SimpleOS/BSD/macOS host matrix.
