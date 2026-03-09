#include "build_recipe.h"

namespace build59 {
namespace {

BuildStep make_step(const std::string& name,
                    const std::string& command,
                    const std::string& note,
                    const features59::FeatureEntry& feature) {
    return BuildStep{name, command, note, feature};
}

}  // namespace

BuildRecipe buildDefaultRecipe() {
    const auto matrix = features59::buildDefaultMatrix();
    BuildRecipe recipe;
    recipe.steps = {
        make_step("Configure CMake", "cmake -B build -S . -G Ninja",
                  "Preps CUDA + PyTorch feature targets.",
                  matrix.entries[0]),
        make_step("Build Core Kernels", "ninja -C build attention_expert_kernels_59",
                  "Exercises CUDA Graph friendly kernels.",
                  matrix.entries[2]),
        make_step("Optional PyTorch Bindings",
                  "ninja -C build attention_expert_torch_59",
                  "Requires Torch detection for dispatcher features.",
                  matrix.entries[0]),
        make_step("Python Editable Install", "pip install -e python",
                  "Matches python nn.Module wrappers.",
                  matrix.entries[5]),
        make_step("Wheel Packaging", "python setup.py bdist_wheel",
                  "For deployment scenarios backed by NVMe streaming.",
                  matrix.entries[3]),
    };
    return recipe;
}

}  // namespace build59
