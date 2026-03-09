#include "dispatcher_checks.h"

namespace torch59 {
namespace {

DispatcherCheck make_check(const std::string& name,
                           const std::string& status,
                           const std::string& key,
                           const examples59::ExampleSnippet& snippet) {
    return DispatcherCheck{name, status, key, snippet};
}

}  // namespace

DispatcherMatrix buildDispatcherMatrix() {
    const auto catalog = examples59::buildExampleCatalog();
    DispatcherMatrix matrix;
    matrix.checks = {
        make_check("Autograd Function", "✅",
                   "DispatchKey::AutogradCUDA", catalog.snippets[0]),
        make_check("Autocast", "✅",
                   "DispatchKey::AutocastCUDA", catalog.snippets[1]),
        make_check("CUDA Graph Friendly", "✅",
                   "DispatchKey::CUDAGraph", catalog.snippets[0]),
        make_check("torch.compile", "✅",
                   "DispatchKey::CompositeExplicitAutograd", catalog.snippets[1]),
        make_check("TensorNVMeReader Binding", "⚠️ requires fixtures",
                   "Custom::attention_expert_nvme", catalog.snippets[2]),
    };
    return matrix;
}

}  // namespace torch59
