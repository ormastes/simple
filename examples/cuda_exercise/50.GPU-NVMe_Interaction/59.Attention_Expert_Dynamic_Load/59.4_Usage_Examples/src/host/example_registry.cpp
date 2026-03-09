#include "example_registry.h"

namespace examples59 {
namespace {

ExampleSnippet make_snippet(const std::string& name,
                            const std::string& file_path,
                            const std::string& description,
                            const build59::BuildStep& step) {
    return ExampleSnippet{name, file_path, description, step};
}

}  // namespace

ExampleCatalog buildExampleCatalog() {
    const auto recipe = build59::buildDefaultRecipe();
    ExampleCatalog catalog;
    catalog.snippets = {
        make_snippet("CUDA Attention Smoke Test",
                     "python/attention_expert/examples/training_with_nvme.py",
                     "Runs attention forward/backward with NVMe-enabled weights.",
                     recipe.steps[0]),
        make_snippet("MoE Autograd Check",
                     "python/attention_expert/ops.py",
                     "Instantiates MixtureOfExperts and tests gradients.",
                     recipe.steps[2]),
        make_snippet("TensorNVMeReader Demo",
                     "python/attention_expert/nvme_loader.py",
                     "Streams tensors from NVMe into CUDA buffers.",
                     recipe.steps[3]),
    };
    return catalog;
}

}  // namespace examples59
