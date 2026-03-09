# Repository Guidelines

## Project Structure & Module Organization

### Three-Tier Hierarchy
- **Parent Categories (X0: 10, 20, 30)**: Navigation hubs containing ONLY README.md and child modules. **CRITICAL**: NO src/, test/, or CMakeLists.txt at parent level.
- **Basic Modules (11-15)**: Flat structure with README.md, CMakeLists.txt, and source files.
- **Advanced Modules (16+)**: Organized structure with doxygen/, src/, and test/ directories.

### Directory Structure
- `00.cmake_lib/` - Shared CMake utilities (profiling hooks, testing helpers)
- `00.cuda_custom_lib/`, `00.demo/`, `00.demo_lib/` - Canonical kernels and helper libraries
- `00.test_lib/` - GoogleTest utilities (`gpu_gtest.h`, `gtest_generator.h`)
- Numbered chapters: `10.cuda_basic/` ... `70.GPU_Optimization/`
- Module structure (16+):
  ```
  XX.Module_Name/
  ├── README.md, CMakeLists.txt
  ├── doxygen/          # REQUIRED for Module 16+
  ├── src/
  │   ├── common/       # Shared utilities
  │   ├── host/         # CPU-side code
  │   ├── kernels/      # CUDA kernels
  │   └── part_specific/
  └── test/unit/        # Mirror src/ structure
  ```
- Supporting assets: `data/` for sample inputs, `logs/` for benchmarks
- `scripts/` (root) - Project-wide utilities affecting entire repository
- `XX.Module_Name/scripts/` (module-specific) - Module setup and automation

## Build, Test, and Development Commands

### Build Configuration
- `cmake -B build -S . -G Ninja` - Configure Ninja build tree
- `ninja -C build` - Build all targets
- `ninja -C build <target_name>` - Build specific target
- `ninja -C build doxygen_XX_Module_Name` - Generate documentation (Module 16+)

### Testing
- `ctest --output-on-failure` - Run all tests from build directory
- `ctest -R pattern` - Run tests matching pattern (e.g., `ctest -R 19.CUDA_Memory_API`)
- All tests from Module 16+ must pass before committing

### Profiling
- `ninja -C build run_nsys_<target>` - Nsight Systems profiling
- `ninja -C build run_ncu_<target>` - Nsight Compute profiling
- If Nsight Compute reports `ERR_NVGPUCTRPERM`, run `sudo ./scripts/setup_ncu_permissions.sh`

### Environment Setup
- `./scripts/setup_env.sh` - Configure CUDA environment variables
- `./scripts/run_all_benchmarks_bg.sh` - Run all benchmarks in background
- `./scripts/monitor_benchmarks.sh` - Monitor benchmark progress

## Coding Style & Naming Conventions

### File Organization
- `.cpp` for host code, `.cu`/`.cuh` for device kernels
- 4-space indentation, same-line braces
- Use C++20 standard, CUDA 13.0+

### Naming Conventions (enforced by .clang-tidy)
- Functions: `camelBack`
- Classes: `CamelCase`
- Variables: `lower_case`
- Macros: `UPPER_CASE`
- Constants: `kCamelCase`

### Include Path Management
**CRITICAL**: Use target-based dependency propagation. **NO relative paths like `../../`**

```cpp
// ✅ CORRECT
#include "common/header.h"      // Via target_link_libraries
#include "kernels/kernel.h"

// ❌ WRONG
#include "../../module/include/header.h"
```

### CMake Best Practices
- Export include directories with `target_include_directories(lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})`
- Link dependencies with `target_link_libraries(target PUBLIC dependency_lib)` for automatic include path propagation
- Use `CUDA_BASIC_LIB` and `GTEST_BASIC_LIB` instead of manual library specifications
- Add profiling targets for ALL executables (Module 15+): `add_profiling_targets(target)`

### Helper Libraries
- `cuda_utils.h` (from `00.cuda_custom_lib/`) - CUDA error checking, memory allocation
- `gpu_gtest.h` (from `00.test_lib/`) - GPU test fixtures with automatic device setup
- Use NVTX ranges instead of custom logging

## Testing Guidelines

### Test Structure (Module 16+)
- **Unit tests**: `test/unit/` - Mirror `src/` directory structure (common/, host/, kernels/, part_specific/)
- **Integration tests**: `test/integration/` - End-to-end workflows, hardware tests
- Use `GpuTest` base class for automatic CUDA setup/teardown:
  ```cpp
  class MyKernelTest : public GpuTest {
      // Automatic CUDA device initialization
  };
  ```

### Test Requirements
- All modules from Module 16+ must have comprehensive tests
- Use GoogleTest with `GTestCudaGenerator` macros (`GPU_TEST`, `GPU_EXPECT_*`)
- Register tests: `gtest_discover_tests(test_target)`
- Add profiling: `add_profiling_targets(test_target)`
- Link with `${GTEST_BASIC_LIB}` for automatic test utilities

### Integration Test Patterns
- **Pattern-based verification** for file/device I/O
- **Non-destructive**: Test files only, don't modify system state
- Pattern types: Sequential (0), Alternating (1), Block-based (2), Prime (3)

## Documentation Requirements

### README.md Format
Every module must have:
- Goal statement (one-sentence objective)
- Project structure (directory tree)
- Quick navigation links
- 1-2 sentence intro for EVERY section
- Code examples referencing actual source files
- Summary with key takeaways, metrics, and next steps

### Doxygen (REQUIRED for Module 16+)
All advanced modules must include `doxygen/` directory with:
- `Doxyfile.in` - Configuration template
- `mainpage.md` - Architecture overview
- All public APIs documented with `@brief`, `@param`, `@return`, `@note`
- Generate docs: `ninja doxygen_XX_Module_Name`

### Parent Directory README Rules
Parent categories (10, 20, 30) contain ONLY:
- README.md with navigation links to child modules
- NO src/, test/, or CMakeLists.txt
- Links must include section numbers (XX.1, XX.2, etc.)

## Commit & Pull Request Guidelines

### Commit Format
- Use short, imperative commits with prefixes:
  - `docs:` - Documentation changes
  - `feat:` - New features
  - `fix:` - Bug fixes
  - `refactor:` - Code refactoring
  - `test:` - Test additions/changes
- Include module numbers: `feat(55.0): Add GPU P2P mapping support`
- End with Claude Code signature:
  ```
  🤖 Generated with [Claude Code](https://claude.com/claude-code)

  Co-Authored-By: Claude <noreply@anthropic.com>
  ```

### Pull Request Requirements
- Link relevant issues
- Summarize affected modules
- Call out GPU/NVMe hardware prerequisites
- Attach key artifacts (`logs/*.log`, benchmark results)
- Flag profiling or hardware steps for reviewers
- Ensure all tests pass (Module 16+)

## GPU/NVMe Hardware Setup

### CUDA Environment
- Use CUDA 13.0 or above
- Run `./scripts/setup_env.sh` for environment configuration
- Profiling permissions: `sudo ./scripts/setup_ncu_permissions.sh`

### NVMe/VFIO Setup (Module 50+)
- VFIO device binding required for GPU-initiated NVMe I/O
- Setup scripts in module-specific `scripts/` directories
- Check IOMMU groups: `./scripts/setup_vfio_test_env.sh`
- Kernel modules (driver/) built with kbuild, not CMake

### DBC (Doorbell Buffer Config) Detection
- Check NVMe DBC support: Module 55.2 provides detection tool
- Modes supported:
  - Mode 1: Host + MMIO (universal)
  - Mode 3: Host + Daemon (consumer drives)
  - Mode 4: DBC Shadow (enterprise NVMe)
  - Mode 5: GPU + Daemon (GPU-initiated)

## Special Module Types

### GPU-NVMe Interaction (Module 50+)
Progression: Host I/O → Pinned Memory → GPU Memory → GPU Queues
- Requires VFIO, IOMMU, P2P mapping
- Kernel module: `gpu_p2p_nvme` for GPU-NVMe DMA
- Integration tests require real hardware

### GPU Optimization (Module 70+)
Progression: CPU Baseline → PyCUDA → C API → Native CUDA → Optimizations
- CPU baseline for comparison
- PyTorch native CUDA extensions
- Progressive optimization demonstrations
- Memory usage analysis

## Quick Reference

**Build**: `ninja -C build`
**Test**: `ctest --output-on-failure`
**Profile**: `ninja run_nsys_<target>`
**Docs**: `ninja doxygen_XX_Module_Name`
**Style**: Match existing code, follow `.clang-tidy`
**Include paths**: Use target dependencies, no `../../`
**Module 16+ requirements**: doxygen/, comprehensive tests, profiling targets

For detailed documentation format guidelines, see `CLAUDE.md`.
