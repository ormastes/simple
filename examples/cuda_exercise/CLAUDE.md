# CUDA Exercise Documentation Format Guide

## Purpose
Establish consistent documentation format for CUDA exercise modules ensuring clarity, maintainability, and effective learning progression.

---

## Directory Structure Rules

### Three-Tier Hierarchy

**Parent Categories (X0: 10, 20, 30)**
- Navigation hubs containing ONLY README.md and child modules
- NO src/, test/, or CMakeLists.txt at parent level
- Structure: `X0.Category_Name/` → `README.md` + `X1.Module/`, `X2.Module/`, etc.

**Basic Modules (11-15)**
```
XX.Module_Name/
├── README.md
├── CMakeLists.txt
└── *.cu, *.h files (flat structure)
```

**Advanced Modules (16+)**
```
XX.Module_Name/
├── README.md
├── CMakeLists.txt
├── doxygen/               # REQUIRED for Module 16+
│   ├── Doxyfile.in
│   ├── mainpage.md
│   └── src/              # Generated (DO NOT commit)
├── src/
│   ├── common/           # Shared utilities, data structures
│   ├── host/             # CPU-side implementations
│   ├── kernels/          # CUDA kernel implementations
│   └── part_specific/    # Module-specific code
└── test/
    ├── helper/           # Test utilities, mock objects, test data generators
    └── unit/
        ├── common/, host/, kernels/, part_specific/
```

### Optional Directories

**scripts/** - Setup scripts, automation (must be executable, idempotent, self-documenting)

**driver/** - Kernel modules (use kbuild, not CMake; document module parameters and loading)

**Root scripts/** - Repository-wide utilities (environment setup, profiling permissions, build automation)

---

## README.md Format

### Module README Template

```markdown
# 🎯 Part XX: Module Title
**Goal**: One-sentence objective.

## Project Structure
[Directory tree showing src/ and test/ organization]

## Quick Navigation
- [XX.1 Topic One](#xx1-topic-one)
- [Build & Run](#build--run)

---

## **XX.1 Section Title**
1-2 sentences explaining concept's purpose and relevance.

### **XX.1.1 Subsection**
Brief explanation.

### **XX.1.2 Implementation Example**
Code with file references:
```cpp
// filename.cu - Brief description
[Code snippet]
```
**Key Points**: Bullet list
**Source**: `src/path/file.cu:lines`

### **XX.1.3 Practical Usage**
Working example with expected output.

## **XX.7 Summary**
- **Key Takeaways**: 3-5 bullet points
- **Performance Metrics**: GFLOPS, efficiency
- **Common Errors**: Table of error/cause/solution
- **Next Steps**: Links to next module
- **References**: External docs
```

### Parent Directory README Rules

**CRITICAL**: X0 directories (10, 20, 30) contain ONLY README.md (no src/test/CMakeLists.txt)

```markdown
# 🚀 Category Title
> Brief category description

## 🧩 Part XX: Module Name
**Goal**: Objective. See [XX.Module/README.md](XX.Module/README.md)
- **XX.1** [Section](XX.Module/README.md#anchor)

## ✅ Summary
1. **Key Concept**: Brief explanation
**Next Steps**: [Next Category](../NextCategory/README.md)
```

---

## Testing Requirements

**MANDATORY from Module 16+**. Always build and run tests.

### Unit Test with GpuTest Base Class

```cpp
#include <gtest/gtest.h>
#include "gpu_gtest.h"

class MyKernelTest : public GpuTest {
    // Automatic CUDA setup/teardown
};

TEST_F(MyKernelTest, CorrectnessCheck) {
    // Test implementation
}

GPU_TEST(KernelTest, DeviceSideTest) {
    // Device-side verification
}
```

### Integration Tests

Pattern-based verification for file/device I/O:
- **Non-Destructive**: Test files only, don't modify system
- **Pattern Types**: Sequential (0), Alternating (1), Block-based (2), Prime (3)

### Custom GPU Test Main

Link with `gpu_gtest.cpp` (not `gtest_main`) for device info printing:
```cmake
target_link_libraries(test_exe GTest::gtest gpu_gtest.cpp)
```

---

## Build System Requirements

### CMake Include Path Management

**CRITICAL**: Use target-based dependency propagation. **NO relative paths like `../../`**

#### Export Include Directories with PUBLIC

```cmake
add_library(my_lib STATIC src/impl.cpp)
target_include_directories(my_lib PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}  # Export entire src/ tree
)
```

#### Link to Dependencies (Don't Manual Paths)

```cmake
# ✅ CORRECT
target_link_libraries(module_b_lib PUBLIC module_a_lib)

# ❌ WRONG
target_include_directories(module_b_lib PRIVATE ${CMAKE_SOURCE_DIR}/module_a/include)
```

#### Include Headers Without Relative Paths

```cpp
// ✅ CORRECT
#include "common/header.h"      // Via target_link_libraries
#include "kernels/kernel.h"

// ❌ WRONG
#include "../../module/include/header.h"
```

### CMakeLists.txt Template (Module 16+)

**Root CMakeLists.txt**
```cmake
project(XX_Module_Name CUDA CXX)
set(MODULE ${PROJECT_NAME})
add_subdirectory(src)
add_subdirectory(test)
```

**src/CMakeLists.txt**
```cmake
add_library(${MODULE}_lib STATIC
    kernels/kernel1.cu
    host/host_impl.cpp
)
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(${MODULE}_lib PUBLIC CudaCustomLib ${CUDA_BASIC_LIB})

# Doxygen (REQUIRED for Module 16+)
find_package(Doxygen QUIET)
if(DOXYGEN_FOUND)
    set(DOXYGEN_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in)
    configure_file(${DOXYGEN_IN} ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile @ONLY)
    add_custom_target(doxygen_${MODULE}
        COMMAND ${DOXYGEN_EXECUTABLE} ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)
endif()
```

**test/CMakeLists.txt**
```cmake
add_executable(${MODULE}_test
    unit/kernels/test_kernel1.cu
    unit/host/test_host.cpp
)
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib
    ${GTEST_BASIC_LIB}
)
gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)  # MANDATORY from Module 15+
```

**Key Principles**:
- Libraries export `src/` as PUBLIC/INTERFACE for tests
- Tests link to libraries (automatic include path propagation)
- Profiling targets for ALL executables (demos, tests, benchmarks)
- Use `CUDA_BASIC_LIB` and `GTEST_BASIC_LIB` instead of manual library specs

---

## Doxygen Comment Style Guide

**REQUIRED for Module 16+**: All public APIs must have Doxygen comments.

### Common Tags

```cpp
/**
 * @file filename.cu
 * @brief One-line description
 */

/**
 * @brief One-line description
 * @param[in]  input  Input parameter
 * @param[out] output Output parameter
 * @return Return value description
 * @note Important note
 * @warning Warning message
 * @performance Performance characteristics
 * @code
 * // Usage example
 * @endcode
 */
__global__ void kernel(float* data, int n);

/// @brief Brief class description
class MyClass {
    int value_;  ///< Member description
};
```

### Quick Reference

- **Functions**: @brief, @param, @return, @note, @warning, @code
- **Classes**: @brief, member inline `///<`
- **Files**: @file, @brief
- **Sections**: @defgroup, @addtogroup, @ingroup

Generate docs: `ninja doxygen_XX_Module_Name`

---

## Documentation Quality Checklist

### Parent Directories (X0)
- [ ] ONLY README.md and child modules (NO src/test/CMakeLists.txt)
- [ ] Links to all child modules with section numbers (XX.1, XX.2)

### Individual Modules
- [ ] 1-2 sentence intro for every section
- [ ] Code examples reference actual source files
- [ ] Module 16+ has doxygen/ with Doxyfile.in and mainpage.md
- [ ] All public APIs have Doxygen comments
- [ ] Tests include correctness and performance
- [ ] CMakeLists.txt follows standard template
- [ ] Profiling targets added (Module 15+)
- [ ] Summary section with metrics and next steps

---

## Special Sections for Advanced Topics

### GPU-NVMe Interaction
Progression: Host I/O → Pinned Memory → GPU Memory → GPU Queues
- NVMe userspace I/O with VFIO
- Pinned memory and P2P mapping
- GPU-initiated NVMe commands
- Doorbell modes (Host, DBC Shadow, Host Daemon, GPU MMIO)

### GPU Optimization
Progression: CPU Baseline → PyCUDA → C API → Native CUDA → Optimizations
- CPU baseline with PyCUDA wrappers
- C API migration
- PyTorch native CUDA extensions
- Progressive optimizations
- Memory usage analysis

---

## Example Excellence: Matrix Multiplication

Reference standard showing:
1. **Progression**: Naive → Tiled → Vectorized → Tensor Core
2. **Metrics**: GFLOPS at each level
3. **Analysis**: Roofline model (bandwidth vs compute limits)
4. **Testing**: Validation against cuBLAS
5. **Documentation**: Clear explanation of each optimization

Demonstrates mastery of memory hierarchy, parallelization, hardware utilization, performance analysis, and production testing.

---

## Additional Notes

- Use `ninja` over `make`
- Use CUDA 13.0+
- Use C++20 standard
- Use GoogleTest with `00.test_lib/gpu_gtest.h` for GPU tests
- Use `00.cuda_custom_lib/cuda_utils.h` for CUDA utilities
- Use `CUDA_BASIC_LIB` and `GTEST_BASIC_LIB` in CMake
- Every section (# ## ###) needs 1-2 sentence explanation
