/**
 * @file huggingface_loader.cpp
 * @brief SafeTensors format parser for HuggingFace model loading
 *
 * Implements parsing of the SafeTensors binary format:
 * 1. Read 8-byte little-endian header length
 * 2. Read and parse JSON metadata describing tensor names, dtypes, shapes, and offsets
 * 3. Extract tensor data from the data section following the header
 *
 * The JSON parsing is done with a minimal hand-rolled parser to avoid
 * external dependencies. Only the subset of JSON needed for SafeTensors
 * metadata is supported.
 */

#include "common/safetensors.h"
#include <cuda_runtime.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <string>
#include <algorithm>

#ifdef __linux__
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#endif

namespace llm {

// ============================================================================
// Minimal JSON parsing helpers for SafeTensors metadata
// ============================================================================

/**
 * @brief Skip whitespace characters in JSON string
 */
static const char* skip_ws(const char* p) {
    while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r') p++;
    return p;
}

/**
 * @brief Parse a JSON string value (assumes cursor is on opening quote)
 * @return The parsed string, cursor advanced past closing quote
 */
static std::string parse_json_string(const char*& p) {
    if (*p != '"') return "";
    p++; // skip opening quote
    std::string result;
    while (*p && *p != '"') {
        if (*p == '\\') {
            p++;
            if (*p == '"') result += '"';
            else if (*p == '\\') result += '\\';
            else if (*p == 'n') result += '\n';
            else result += *p;
        } else {
            result += *p;
        }
        p++;
    }
    if (*p == '"') p++; // skip closing quote
    return result;
}

/**
 * @brief Parse a JSON integer value
 */
static int64_t parse_json_int(const char*& p) {
    char* end = nullptr;
    int64_t val = strtoll(p, &end, 10);
    p = end;
    return val;
}

/**
 * @brief Parse dtype string into SafeTensorsDtype enum
 */
static SafeTensorsDtype parse_dtype(const std::string& s) {
    if (s == "F32") return SafeTensorsDtype::F32;
    if (s == "F16") return SafeTensorsDtype::F16;
    if (s == "BF16") return SafeTensorsDtype::BF16;
    if (s == "F64") return SafeTensorsDtype::F64;
    if (s == "I32") return SafeTensorsDtype::I32;
    if (s == "I64") return SafeTensorsDtype::I64;
    if (s == "BOOL") return SafeTensorsDtype::BOOL;
    if (s == "U8") return SafeTensorsDtype::U8;
    return SafeTensorsDtype::F32; // default fallback
}

/**
 * @brief Parse the JSON header from a SafeTensors file
 *
 * The JSON header has the form:
 * {
 *   "__metadata__": { ... },
 *   "tensor_name": {
 *     "dtype": "F32",
 *     "shape": [dim0, dim1, ...],
 *     "data_offsets": [begin, end]
 *   },
 *   ...
 * }
 */
static bool parse_json_header(const char* json, int64_t json_len,
                               SafeTensorsHeader& header) {
    const char* p = json;
    const char* end = json + json_len;

    p = skip_ws(p);
    if (*p != '{') return false;
    p++; // skip '{'

    while (p < end) {
        p = skip_ws(p);
        if (*p == '}') break;
        if (*p == ',') { p++; continue; }

        // Parse key (tensor name or "__metadata__")
        std::string key = parse_json_string(p);
        p = skip_ws(p);
        if (*p != ':') return false;
        p++; // skip ':'
        p = skip_ws(p);

        if (key == "__metadata__") {
            // Skip metadata object: find matching '}'
            int depth = 0;
            if (*p == '{') {
                depth = 1;
                p++;
                while (p < end && depth > 0) {
                    if (*p == '{') depth++;
                    else if (*p == '}') depth--;
                    else if (*p == '"') {
                        p++; // skip opening quote
                        while (p < end && *p != '"') {
                            if (*p == '\\') p++;
                            p++;
                        }
                    }
                    p++;
                }
            }
            continue;
        }

        // Parse tensor info object
        if (*p != '{') return false;
        p++; // skip '{'

        SafeTensorInfo info;
        info.name = key;

        while (p < end) {
            p = skip_ws(p);
            if (*p == '}') { p++; break; }
            if (*p == ',') { p++; continue; }

            std::string field = parse_json_string(p);
            p = skip_ws(p);
            if (*p != ':') return false;
            p++; // skip ':'
            p = skip_ws(p);

            if (field == "dtype") {
                info.dtype = parse_dtype(parse_json_string(p));
            } else if (field == "shape") {
                if (*p != '[') return false;
                p++; // skip '['
                while (p < end) {
                    p = skip_ws(p);
                    if (*p == ']') { p++; break; }
                    if (*p == ',') { p++; continue; }
                    info.shape.push_back(parse_json_int(p));
                }
            } else if (field == "data_offsets") {
                if (*p != '[') return false;
                p++; // skip '['
                p = skip_ws(p);
                info.data_offset_begin = parse_json_int(p);
                p = skip_ws(p);
                if (*p == ',') p++;
                p = skip_ws(p);
                info.data_offset_end = parse_json_int(p);
                p = skip_ws(p);
                if (*p == ']') p++;
            } else {
                // Skip unknown value
                if (*p == '"') {
                    parse_json_string(p);
                } else if (*p == '[' || *p == '{') {
                    int depth = 1;
                    char open = *p;
                    char close = (open == '[') ? ']' : '}';
                    p++;
                    while (p < end && depth > 0) {
                        if (*p == open) depth++;
                        else if (*p == close) depth--;
                        p++;
                    }
                } else {
                    while (p < end && *p != ',' && *p != '}') p++;
                }
            }
        }

        header.tensors.push_back(info);
    }

    return true;
}

// ============================================================================
// Public API implementation
// ============================================================================

bool parse_safetensors(const std::string& filepath, SafeTensorsHeader& header) {
    FILE* fp = fopen(filepath.c_str(), "rb");
    if (!fp) {
        fprintf(stderr, "Error: Cannot open %s for reading\n", filepath.c_str());
        return false;
    }

    // Read 8-byte header size (little-endian uint64)
    uint64_t header_size = 0;
    if (fread(&header_size, sizeof(uint64_t), 1, fp) != 1) {
        fprintf(stderr, "Error: Cannot read header size from %s\n", filepath.c_str());
        fclose(fp);
        return false;
    }
    header.header_size = static_cast<int64_t>(header_size);

    // Sanity check: header should be reasonable size (< 100MB)
    if (header_size > 100 * 1024 * 1024) {
        fprintf(stderr, "Error: Header size too large (%llu bytes)\n",
                static_cast<unsigned long long>(header_size));
        fclose(fp);
        return false;
    }

    // Read JSON header
    std::vector<char> json_buf(header_size + 1, 0);
    if (fread(json_buf.data(), 1, header_size, fp) != header_size) {
        fprintf(stderr, "Error: Cannot read JSON header from %s\n", filepath.c_str());
        fclose(fp);
        return false;
    }
    fclose(fp);

    // Parse JSON
    return parse_json_header(json_buf.data(), header_size, header);
}

bool load_safetensor_data(const std::string& filepath,
                          const SafeTensorsHeader& header,
                          const std::string& tensor_name,
                          float* d_output) {
    // Find the tensor in the header
    const SafeTensorInfo* info = nullptr;
    for (const auto& t : header.tensors) {
        if (t.name == tensor_name) {
            info = &t;
            break;
        }
    }

    if (!info) {
        fprintf(stderr, "Error: Tensor '%s' not found in SafeTensors file\n",
                tensor_name.c_str());
        return false;
    }

    FILE* fp = fopen(filepath.c_str(), "rb");
    if (!fp) return false;

    // Data starts after 8-byte size prefix + header
    int64_t data_section_offset = 8 + header.header_size;
    int64_t tensor_offset = data_section_offset + info->data_offset_begin;
    int64_t tensor_bytes = info->byte_size();

    fseek(fp, tensor_offset, SEEK_SET);

    if (info->dtype == SafeTensorsDtype::F32) {
        // Direct load: read float data and copy to device
        std::vector<float> h_data(info->num_elements());
        size_t read = fread(h_data.data(), sizeof(float), h_data.size(), fp);
        fclose(fp);

        if (read != h_data.size()) return false;

        cudaMemcpy(d_output, h_data.data(), tensor_bytes, cudaMemcpyHostToDevice);
    } else {
        // For F16/BF16, read raw bytes and convert to F32 on host
        std::vector<uint8_t> raw(tensor_bytes);
        size_t read = fread(raw.data(), 1, tensor_bytes, fp);
        fclose(fp);

        if (static_cast<int64_t>(read) != tensor_bytes) return false;

        int64_t n = info->num_elements();
        std::vector<float> h_data(n);

        if (info->dtype == SafeTensorsDtype::F16) {
            // F16 -> F32 conversion: IEEE 754 half-precision
            const uint16_t* src = reinterpret_cast<const uint16_t*>(raw.data());
            for (int64_t i = 0; i < n; i++) {
                uint16_t h = src[i];
                uint32_t sign = (h & 0x8000) << 16;
                uint32_t exp = (h >> 10) & 0x1F;
                uint32_t mant = h & 0x03FF;

                uint32_t f;
                if (exp == 0) {
                    f = sign; // zero or subnormal (treated as zero)
                } else if (exp == 31) {
                    f = sign | 0x7F800000 | (mant << 13); // inf or nan
                } else {
                    f = sign | ((exp + 112) << 23) | (mant << 13);
                }
                memcpy(&h_data[i], &f, sizeof(float));
            }
        } else {
            // BF16 -> F32: just shift left by 16 bits
            const uint16_t* src = reinterpret_cast<const uint16_t*>(raw.data());
            for (int64_t i = 0; i < n; i++) {
                uint32_t f = static_cast<uint32_t>(src[i]) << 16;
                memcpy(&h_data[i], &f, sizeof(float));
            }
        }

        cudaMemcpy(d_output, h_data.data(), n * sizeof(float), cudaMemcpyHostToDevice);
    }

    return true;
}

#ifdef __linux__

bool mmap_safetensors(const std::string& filepath, void*& addr, size_t& length) {
    int fd = open(filepath.c_str(), O_RDONLY);
    if (fd < 0) {
        fprintf(stderr, "Error: Cannot open %s for mmap\n", filepath.c_str());
        return false;
    }

    struct stat st;
    if (fstat(fd, &st) != 0) {
        close(fd);
        return false;
    }
    length = st.st_size;

    addr = mmap(nullptr, length, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);

    if (addr == MAP_FAILED) {
        addr = nullptr;
        return false;
    }

    return true;
}

void munmap_safetensors(void* addr, size_t length) {
    if (addr) {
        munmap(addr, length);
    }
}

#else

bool mmap_safetensors(const std::string& filepath, void*& addr, size_t& length) {
    fprintf(stderr, "Error: mmap not supported on this platform\n");
    return false;
}

void munmap_safetensors(void* addr, size_t length) {
    (void)addr;
    (void)length;
}

#endif

const char* dtype_to_string(SafeTensorsDtype dtype) {
    switch (dtype) {
        case SafeTensorsDtype::F16:  return "F16";
        case SafeTensorsDtype::BF16: return "BF16";
        case SafeTensorsDtype::F32:  return "F32";
        case SafeTensorsDtype::F64:  return "F64";
        case SafeTensorsDtype::I32:  return "I32";
        case SafeTensorsDtype::I64:  return "I64";
        case SafeTensorsDtype::BOOL: return "BOOL";
        case SafeTensorsDtype::U8:   return "U8";
        default:                     return "UNKNOWN";
    }
}

int dtype_byte_size(SafeTensorsDtype dtype) {
    switch (dtype) {
        case SafeTensorsDtype::F16:  return 2;
        case SafeTensorsDtype::BF16: return 2;
        case SafeTensorsDtype::F32:  return 4;
        case SafeTensorsDtype::F64:  return 8;
        case SafeTensorsDtype::I32:  return 4;
        case SafeTensorsDtype::I64:  return 8;
        case SafeTensorsDtype::BOOL: return 1;
        case SafeTensorsDtype::U8:   return 1;
        default:                     return 0;
    }
}

} // namespace llm
