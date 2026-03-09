#include "example_registry.h"

#include <sstream>

namespace examples59 {

std::string formatCatalog(const ExampleCatalog& catalog) {
    std::ostringstream oss;
    oss << "Usage Example Catalog (" << catalog.snippetCount() << " entries)\n";
    std::size_t index = 1;
    for (const auto& snippet : catalog.snippets) {
        oss << "  [" << index++ << "] " << snippet.name << "\n"
            << "      File: " << snippet.file_path << "\n"
            << "      Desc: " << snippet.description << "\n"
            << "      Requires: " << snippet.prerequisite.name << '\n';
    }
    return oss.str();
}

}  // namespace examples59
