# Native checked-reader mirror launcher produced no execution evidence

Status: OPEN; setup failure, not a checked-reader correctness failure.

The private packet `build/native_probe/checked-reader-native-mirror-20261013-root` attempted thirteen real core-C ABI assertions. No assertion executed or qualified. The first attempt hit PowerShell execution policy; the second failed before launch because the collector output directory did not exist. The third used packaged PowerShell 7.6.6 with a process-only RemoteSigned policy and a precreated output directory under a clean environment.

Attempt three returned native exit 0 and final Job membership 0, but captured an empty log, created no object/executable/map, and produced no CHILD_RESULT.json. Its process peaked at 99,868 KiB. Exit zero alone must never qualify a test or build. The exact underlying packaged-shell/environment failure remains unproven.

Evidence: `attempt3/receipt.env`, `ATTEMPT2_ADMISSION.json`, and `QUALIFICATION_CLOSED.json` in the packet. The three-attempt criterion is closed without PASS. Existing checked-reader source/runtime archive was not modified. Do not rerun this closed criterion; separately qualify the launcher with a real output sentinel and process-tree evidence before preparing a fresh test scope.

Acceptance for the launcher repair: a bounded child must write an exact sentinel artifact, return its actual result, and terminate with Job0. Then a separately admitted mirror run must report all thirteen named assertion outcomes and bind the executable, map, source inputs, and test result. SDK and system import-library inputs were not sealed in the original packet; no fully reproducible-toolchain claim is valid.
## Separately qualified native launcher

A new setup criterion used the native system `WindowsPowerShell/v1.0/powershell.exe` with a child-process RemoteSigned policy. It wrote the exact `NATIVE_POWERSHELL_SENTINEL_OK` artifact and log, returned the deliberate native exit23, and terminated at Job0. Its receipt SHA256 is `42f599cbcf0f497f3e88c086e75009346e4a15661d8951048dcc9f2c0895d9c9` in `build/native_probe/native-powershell-launcher-sentinel-20261013-root/attempt/receipt.env`.

This qualifies that exact launcher setup. The packaged PowerShell7 clean-environment behavior remains unexplained; no general collector fault is proven. The original thirteen checked-reader assertions remain unexecuted and closed without PASS. Do not infer reader, test-product, memory, or performance qualification from this sentinel.