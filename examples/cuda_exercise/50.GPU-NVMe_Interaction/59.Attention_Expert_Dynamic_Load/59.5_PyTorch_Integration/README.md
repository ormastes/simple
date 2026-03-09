# 🔗 Module 59.5: PyTorch Integration Matrix

**Goal**: Encode dispatcher/autograd/AMP checks in executable form so that PyTorch support claims can be validated via code and GPU-aware tests.

## Quick Navigation

- [59.5.1 Goals](#5951-goals)
- [59.5.2 Relationship to Previous Modules](#5952-relationship-to-previous-modules)
- [59.5.3 Project Structure](#5953-project-structure)
- [59.5.4 Build & Run](#5954-build--run)
- [59.5.5 Source Highlights](#5955-source-highlights)
- [59.5.6 Testing](#5956-testing)
- [Summary](#summary)

---

## 59.5.1 Goals
- Mirror the feature table’s PyTorch-related entries with concrete dispatcher checks.
- Tie each check back to a usage example to prove coverage.
- Provide CLI output + CUDA writes for CI validation.

## 59.5.2 Relationship to Previous Modules
- Depends on `59_4_Usage_Examples_lib` to reuse snippet metadata.
- Ensures dispatcher coverage always references a real example file.

## 59.5.3 Project Structure

```
59.5_PyTorch_Integration/
├── README.md
├── CMakeLists.txt
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── common/dispatcher_checks.h
│   ├── host/
│   │   ├── dispatcher_checks.cpp
│   │   └── dispatcher_cli.cpp
│   ├── kernels/dispatcher_kernel.cu
│   └── part_specific/dispatcher_formatter.cpp
└── test/unit/common/test_dispatcher_checks.cpp
```

## 59.5.4 Build & Run

```bash
cmake -B build -S . -G Ninja
ninja -C build 59_5_PyTorch_Integration_cli
./build/50.GPU-NVMe_Interaction/59.Attention_Expert_Dynamic_Load/59.5_PyTorch_Integration/59_5_PyTorch_Integration_cli
```

## 59.5.5 Source Highlights
- `dispatcher_checks.cpp` enumerates the key PyTorch features (autograd, autocast, torch.compile, NVMe loader binding).
- `dispatcher_cli.cpp` prints the matrix and writes check counts to a CUDA buffer.

## 59.5.6 Testing

```bash
ninja -C build 59_5_PyTorch_Integration_unit_common
ctest -C Debug -R 59_5_PyTorch_Integration_unit_common --output-on-failure
```

## Summary

Module 59.5 keeps PyTorch integration honest by tying claims to executable checks. Continue to the NVMe loading internals in Module 59.6 once dispatcher support is verified.

**Next module**: [`../59.6_Dynamic_NVMe_Loading/`](../59.6_Dynamic_NVMe_Loading/)
