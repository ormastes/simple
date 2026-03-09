# 📚 Module 59.4: Usage Example Catalog

**Goal**: Encode runnable attention/MoE/NVMe snippets so documentation, CLIs, and automation can reference the same catalog generated from real file paths.

## Quick Navigation

- [59.4.1 Goals](#5941-goals)
- [59.4.2 Relationship to Previous Modules](#5942-relationship-to-previous-modules)
- [59.4.3 Project Structure](#5943-project-structure)
- [59.4.4 Build & Run](#5944-build--run)
- [59.4.5 Source Highlights](#5945-source-highlights)
- [59.4.6 Testing](#5946-testing)
- [Summary](#summary)

---

## 59.4.1 Goals
- Provide a single place to look up usage snippets and their underlying files.
- Annotate each snippet with the build step required to run it (via Module 59.3).
- Offer a CLI + CUDA-backed verification so the catalog remains verifiable in CI.

## 59.4.2 Relationship to Previous Modules
- Links against `59_3_Build_and_Install_lib` and consumes `build_recipe.h`.
- Ensures every example references a concrete build prerequisite.

## 59.4.3 Project Structure

```
59.4_Usage_Examples/
├── README.md
├── CMakeLists.txt
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── common/example_registry.h
│   ├── host/
│   │   ├── example_registry.cpp
│   │   └── example_cli.cpp
│   ├── kernels/example_kernel.cu
│   └── part_specific/example_formatter.cpp
└── test/unit/common/test_example_registry.cpp
```

## 59.4.4 Build & Run

```bash
cmake -B build -S . -G Ninja
ninja -C build 59_4_Usage_Examples_cli
./build/50.GPU-NVMe_Interaction/59.Attention_Expert_Dynamic_Load/59.4_Usage_Examples/59_4_Usage_Examples_cli
```

## 59.4.5 Source Highlights
- `example_registry.cpp` enumerates snippets pointing to real files in `python/attention_expert/`.
- `example_cli.cpp` prints the catalog and pushes the snippet count through a CUDA kernel.
- Format helpers keep notes concise for CLI + future docs.

## 59.4.6 Testing

```bash
ninja -C build 59_4_Usage_Examples_unit_common
ctest -C Debug -R 59_4_Usage_Examples_unit_common --output-on-failure
```

## Summary

Module 59.4 keeps the README usage examples honest by generating them from code. Use it as the foundation for PyTorch integration checks in Module 59.5.

**Next module**: [`../59.5_PyTorch_Integration/`](../59.5_PyTorch_Integration/)
