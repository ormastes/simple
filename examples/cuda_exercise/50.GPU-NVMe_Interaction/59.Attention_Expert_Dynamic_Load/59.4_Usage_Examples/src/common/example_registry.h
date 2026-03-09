/**
 * @file example_registry.h
 * @brief Module 59.4 usage examples registry
 */

#pragma once

#include "build_recipe.h"

#include <string>
#include <vector>

namespace examples59 {

/**
 * @brief Example code snippet
 */
struct ExampleSnippet {
    std::string name;
    std::string file_path;
    std::string description;
    build59::BuildStep prerequisite;
};

/**
 * @brief Catalog of example snippets
 */
struct ExampleCatalog {
    std::vector<ExampleSnippet> snippets;

    [[nodiscard]] std::size_t snippetCount() const noexcept {
        return snippets.size();
    }
};

/**
 * @brief Build example catalog
 * @return Example catalog with default snippets
 */
ExampleCatalog buildExampleCatalog();

/**
 * @brief Format catalog for display
 * @param catalog Example catalog to format
 * @return Formatted string
 */
std::string formatCatalog(const ExampleCatalog& catalog);

/**
 * @brief Populate device memory with snippet count
 * @param device_ptr Device memory pointer
 * @param snippet_count Number of snippets
 */
void populateDeviceSnippetCount(int* device_ptr, int snippet_count);

}  // namespace examples59
