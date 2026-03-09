/**
 * @file formatter_template.h
 * @brief Template-based formatter for Module 59
 */

#pragma once

#include <sstream>
#include <string>
#include <vector>
#include <functional>

namespace module59 {
namespace formatter {

/**
 * @brief Generic formatter for collection types
 * @tparam CollectionType Type containing entries to format
 * @tparam EntryType Type of each entry
 */
template<typename CollectionType, typename EntryType>
class GenericFormatter {
public:
    struct FormatConfig {
        std::string header;
        std::string entry_prefix = "  ";
        std::function<std::string(const EntryType&, std::size_t)> entry_formatter;
        std::function<std::size_t(const CollectionType&)> count_extractor;
        std::function<const std::vector<EntryType>&(const CollectionType&)> entries_extractor;
    };

    static std::string format(const CollectionType& collection, const FormatConfig& config) {
        std::ostringstream oss;

        const std::size_t count = config.count_extractor(collection);
        oss << config.header << " (" << count << " entries)\n";

        const auto& entries = config.entries_extractor(collection);
        std::size_t idx = 1;

        for (const auto& entry : entries) {
            oss << config.entry_prefix << "[" << idx << "] "
                << config.entry_formatter(entry, idx) << '\n';
            ++idx;
        }

        return oss.str();
    }
};

/**
 * @brief Standard entry formatter for entries with name and description fields
 */
template<typename EntryType>
std::string standardEntryFormatter(const EntryType& entry, std::size_t /*idx*/) {
    std::ostringstream oss;
    oss << entry.name;

    // Add optional fields if they exist (using SFINAE)
    if constexpr (requires { entry.description; }) {
        oss << "\n      " << entry.description;
    }
    if constexpr (requires { entry.file; }) {
        oss << "\n      File: " << entry.file;
    }
    if constexpr (requires { entry.command; }) {
        oss << "\n      Command: " << entry.command;
    }
    if constexpr (requires { entry.device; }) {
        oss << "\n      Device: " << entry.device;
    }

    return oss.str();
}

// Convenience macro for standard formatters
#define DEFINE_STANDARD_FORMATTER(Namespace, Type, Header) \
namespace Namespace { \
std::string format##Type(const Type& obj) { \
    using Formatter = module59::formatter::GenericFormatter<Type, decltype(obj.entries[0])>; \
    typename Formatter::FormatConfig config{ \
        .header = Header, \
        .entry_formatter = module59::formatter::standardEntryFormatter<decltype(obj.entries[0])>, \
        .count_extractor = [](const Type& t) { return t.entries.size(); }, \
        .entries_extractor = [](const Type& t) -> const auto& { return t.entries; } \
    }; \
    return Formatter::format(obj, config); \
} \
}

} // namespace formatter
} // namespace module59