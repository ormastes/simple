# Scoped embedded C repair verification

Production source tested at9344d12fba0f35abb38130cea1a3af0fbabb9201 on release base0e56cc6bade88499977bb228bc46e696bf987e03. Complete ARM64 and x86_64 production translation units each pass190 assertions under QEMU user mode (exit0). The seven-owner constant check and both extracted logical owners pass. The earlier negative baseline (25 failures per architecture) is retained in merged #7447. Production owner blobs match the original candidate41fb553; current integration changes CI and scoped documentation only beyond that repair.

The fix is specific to primitive C runtime logical/conversion/predicate consumers, preserving existing nonboolean truthiness and raw predicate ABI. Conditional compiler/lib/MCP gates do not apply to these embedded C files. Neither Simple-generated caller nor boot/device/system qualification is claimed. No global bug closure is written. Existing unrelated ARM64 negative-shift compile warning is retained in the compile log.

CI runs both focused and full-TU regressions with relevant source/header/test triggers. Working/staged environment guards, whitespace/layout checks and normal commit hooks passed. No acceptance check is weakened and no known failure is converted to PASS.
