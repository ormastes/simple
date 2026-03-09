# 🚀 Module 59.2: Feature Matrix Engine

**Goal**: Materialize the feature table from Module 59 into code so we can keep the PyTorch, NVMe, and MoE capabilities in sync with the architecture defined by Module 59.1.

## Quick Navigation

- [59.2.1 Goals](#5921-goals)
- [59.2.2 Relationship to 59.1](#5922-relationship-to-591)
- [59.2.3 Project Structure](#5923-project-structure)
- [59.2.4 Build & Run](#5924-build--run)
- [59.2.5 Source Highlights](#5925-source-highlights)
- [59.2.6 Testing](#5926-testing)
- [Summary](#summary)

---

## 59.2.1 Goals
- Keep a definitive feature matrix (autograd, AMP, NVMe streaming, MoE routing) close to code.
- Allow other modules to query feature metadata and align with Module 59.1’s architectural layers.
- Provide CUDA + host coverage, following Module 16+ requirements (doxygen/docs/tests).

## 59.2.2 Relationship to 59.1
- Links directly to the `OverviewSummary` defined in [`../59.1_Overview/src/common/overview_data.h`](../59.1_Overview/src/common/overview_data.h) via target linking.
- Ensures every feature references one of the four canonical layers; tests verify the mapping.

## 59.2.3 Project Structure

```
59.2_Features/
├── README.md
├── CMakeLists.txt
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── common/feature_matrix.h       # Data structures referencing 59.1 overview
│   ├── host/
│   │   ├── feature_matrix.cpp        # Builds matrix from overview
│   │   └── feature_cli.cpp           # Prints matrix + GPU verification
│   ├── kernels/feature_kernel.cu     # Writes feature count to device buffer
│   └── part_specific/feature_formatter.cpp
└── test/unit/common/test_feature_matrix.cpp
```

## 59.2.4 Build & Run

```bash
cmake -B build -S . -G Ninja
ninja -C build 59_2_Features_cli
./build/50.GPU-NVMe_Interaction/59.Attention_Expert_Dynamic_Load/59.2_Features/59_2_Features_cli
ninja -C build doxygen_59_2_Features
```

## 59.2.5 Source Highlights
- `feature_matrix.h` imports `overview_data.h` (Module 59.1) to ensure each feature is tagged with a source layer.
- `feature_cli.cpp` prints the feature table and confirms GPU data path by writing the number of supported features.
- `feature_kernel.cu` mirrors the metadata for CUDA consumers.

## 59.2.6 Testing

```bash
ninja -C build 59_2_Features_unit_common
ctest -C Debug -R 59_2_Features_unit_common --output-on-failure
```

Tests assert that every feature is associated with a known layer from Module 59.1.

## Summary

Module 59.2 is now a full-fledged code module linked to the overview registry. Use it as the canonical source for feature status across the Module 59 family.
