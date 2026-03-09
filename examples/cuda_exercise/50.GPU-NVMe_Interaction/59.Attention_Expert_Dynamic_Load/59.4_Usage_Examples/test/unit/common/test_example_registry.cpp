#include <gtest/gtest.h>

#include "example_registry.h"

namespace {

using examples59::buildExampleCatalog;

TEST(ExampleRegistryTest, HasAtLeastThreeSnippets) {
    const auto catalog = buildExampleCatalog();
    EXPECT_GE(catalog.snippetCount(), 3u);
}

TEST(ExampleRegistryTest, SnippetsIncludePythonPaths) {
    const auto catalog = buildExampleCatalog();
    bool seen_python = false;
    for (const auto& snippet : catalog.snippets) {
        if (snippet.file_path.find("python/attention_expert") != std::string::npos) {
            seen_python = true;
        }
    }
    EXPECT_TRUE(seen_python);
}

}  // namespace
