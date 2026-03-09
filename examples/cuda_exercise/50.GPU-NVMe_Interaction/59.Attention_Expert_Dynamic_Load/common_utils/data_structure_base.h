/**
 * @file data_structure_base.h
 * @brief Base templates for Module 59 data structures
 */

#pragma once

#include <string>
#include <vector>
#include <cstddef>

namespace module59 {
namespace base {

/**
 * @brief Base entry type for all Module 59 collections
 * @tparam DependencyType Type of dependency field
 */
template<typename DependencyType>
struct EntryBase {
    std::string name;
    std::string description;
    DependencyType dependency;
};

/**
 * @brief Base collection type with standard count method
 * @tparam EntryType Type of entries in collection
 */
template<typename EntryType>
struct CollectionBase {
    std::vector<EntryType> entries;

    /**
     * @brief Get the number of entries
     * @return Entry count
     */
    [[nodiscard]] std::size_t count() const noexcept {
        return entries.size();
    }
};

/**
 * @brief Standard interface for Module 59 data builders
 * @tparam CollectionType The collection type to build
 */
template<typename CollectionType>
struct BuilderInterface {
    virtual ~BuilderInterface() = default;
    virtual CollectionType build() const = 0;
};

/**
 * @brief Macro to quickly define a Module 59 data structure
 */
#define DEFINE_MODULE59_DATA_STRUCTURE(Namespace, EntryName, CollectionName, DependencyType) \
namespace Namespace { \
struct EntryName##Entry { \
    std::string name; \
    std::string description; \
    DependencyType dependency; \
}; \
\
struct CollectionName { \
    std::vector<EntryName##Entry> entries; \
    [[nodiscard]] std::size_t EntryName##Count() const noexcept { \
        return entries.size(); \
    } \
}; \
\
CollectionName build##CollectionName(); \
std::string format##CollectionName(const CollectionName& obj); \
void populateDevice##CollectionName##Count(int* device_ptr, int count); \
}

} // namespace base
} // namespace module59