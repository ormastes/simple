# 🛠️ Module 59.3: Build & Install Orchestrator

**Goal**: Encode the build + packaging flows for Module 59 in executable form, using the feature matrix (Module 59.2) to ensure each step reflects the advertised capabilities.

## Quick Navigation

- [59.3.1 Goals](#5931-goals)
- [59.3.2 Relationship to Previous Modules](#5932-relationship-to-previous-modules)
- [59.3.3 Project Structure](#5933-project-structure)
- [59.3.4 Build & Run](#5934-build--run)
- [59.3.5 Source Highlights](#5935-source-highlights)
- [59.3.6 Testing](#5936-testing)
- [Summary](#summary)

---

## 59.3.1 Goals
- Provide a definitive build recipe that references real commands (`cmake`, `ninja`, `pip`, `setup.py`).
- Associate every step with a feature from Module 59.2 so documentation, automation, and tooling stay consistent.
- Keep compliance with Module 16+ structure (doxygen, src/, test/, profiling targets).

## 59.3.2 Relationship to Previous Modules
- Links against `59_2_Features_lib` and imports `feature_matrix.h`.
- Each build step documents which feature it satisfies (e.g., PyTorch autograd, NVMe streaming).

## 59.3.3 Project Structure

```
59.3_Build_and_Install/
├── README.md
├── CMakeLists.txt
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── common/build_recipe.h
│   ├── host/
│   │   ├── build_recipe.cpp
│   │   └── build_cli.cpp
│   ├── kernels/build_kernel.cu
│   └── part_specific/build_formatter.cpp
└── test/unit/common/test_build_recipe.cpp
```

## 59.3.4 Build & Run

```bash
cmake -B build -S . -G Ninja
ninja -C build 59_3_Build_and_Install_cli
./build/50.GPU-NVMe_Interaction/59.Attention_Expert_Dynamic_Load/59.3_Build_and_Install/59_3_Build_and_Install_cli
ninja -C build doxygen_59_3_Build_and_Install
```

## 59.3.5 Source Highlights
- `build_recipe.h/.cpp` constructs the step list using `features59::FeatureEntry`.
- `build_cli.cpp` prints the recipe and confirms GPU access by writing the step count through a CUDA kernel.
- `build_formatter.cpp` renders human-readable commands for downstream scripts.

## 59.3.6 Testing

```bash
ninja -C build 59_3_Build_and_Install_unit_common
ctest -C Debug -R 59_3_Build_and_Install_unit_common --output-on-failure
```

Tests ensure the recipe includes ninja/pip commands and remains aligned with Module 59.2.

## Summary

Module 59.3 turns the textual build guidance into a reusable code artifact. Use it to verify tooling expectations before jumping into runtime usage (Module 59.4).

**Next module**: [`../59.4_Usage_Examples/`](../59.4_Usage_Examples/)
