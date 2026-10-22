# Local counterexample probe results

Counterexample probes only; no Simple cache/provider implementation was tested.

Executed in this conversation on 2026-09-25. This is not a performance benchmark or a cache soundness proof.

## Toolchain

### clang
```text
clang version 17.0.0 (https://github.com/swiftlang/llvm-project.git 10999b6d034fe318f3d56c83bddb6572593a8bb0)
Target: x86_64-unknown-linux-gnu
Thread model: posix
InstalledDir: /usr/local/swift/usr/bin
```

### cmake
```text
cmake version 3.31.6

CMake suite maintained and supported by Kitware (kitware.com/cmake).
```

### ninja
```text
1.12.1
```

## Results

| ID | Probe | Outcome | Observation |
|---|---|---|---|
| P01 | Macro definition states are distinct | PASS | Undefined, defined-as-0, defined-empty, and -DMODE (1) produced four distinct results. |
| P02 | Previously unexpanded identifier changes | PASS | An ordinary identifier with no original expansion becomes a macro use after a new definition. |
| P03 | Ordered command-line macro actions | PASS | Reversing -D/-U changed preprocessing; argv ordering cannot be sorted away. |
| P04 | Negative include dependency | PASS | An absent header did not appear in the ordinary dependency list; creating it changed output. |
| P05 | Include-search order is semantic | PASS | The same include spelling selected different content when include search order changed. |
| P06 | Repeated X-macro include | PASS | One header was intentionally processed twice under different function-like macro definitions. |
| P07 | Non-macro pragma state changes layout | PASS | On this x86_64 toolchain, identical header bytes yielded size 8 or 5 under different pragma state. |
| P08 | Textual header semantic context | PASS | The unchanged header and macro configuration still depended on a preceding typedef; header AST reuse needs semantic context. |
| P09 | Stateful builtin counter | PASS | __COUNTER__ reflected incoming preprocessing state, not just macro replacement text. |
| P10 | Native PCH mismatch validation | PASS | Clang accepted matching PCH macro settings and rejected MODE=2 against a MODE=1 PCH. |
| P11 | CMake launcher integration and policy skip hole | PASS | Launcher and File API worked; Ninja did not invoke the launcher on an unchanged build or an undeclared policy-only edit. |
| P12 | Explicit policy dependency closes launcher skip hole | PASS | Adding the registry with OBJECT_DEPENDS made the policy edit trigger another compilation through the launcher. |

## Reproduce

Run `python3 evidence/run_probes.py` with clang, CMake, and Ninja on PATH. The script uses a temporary directory, removes generated binaries, and writes its own results beside itself. The fixed layout checks are specific to the observed x86_64 ABI.

The machine-readable log is `probe_results.json`; full fixture source is in `run_probes.py`. The policy file in the launcher fixture is intentionally opaque text, not a validation of the proposed SDN schema.
