#ifndef SIMPLE_KPF_GENERATED_SCHEMA_HPP
#define SIMPLE_KPF_GENERATED_SCHEMA_HPP

#include <array>
#include <cstdint>

namespace simple::kpf::generated {

inline constexpr std::uint32_t abi_v1 = 1;
inline constexpr char schema_digest[] = "42a1584d4146fe4507a9ecaffddc09bfa0290549da8010ad0161c10b10197fcc";
inline constexpr std::uint64_t abi_layout_prefix_size_v1 = 32;
struct AbiLayoutVectorV1 { const char *name; std::uint64_t available_size; std::uint64_t struct_size; std::uint64_t payload_offset; std::uint64_t payload_length; std::uint64_t required_alignment; std::uint64_t reserved0; bool expected_valid; };
constexpr bool validate_abi_layout_vector_v1(const AbiLayoutVectorV1 &vector) noexcept { return vector.struct_size >= abi_layout_prefix_size_v1 && vector.struct_size <= vector.available_size && vector.reserved0 == 0 && vector.required_alignment != 0 && (vector.required_alignment & (vector.required_alignment - 1)) == 0 && vector.payload_offset >= vector.struct_size && vector.payload_offset <= vector.available_size && vector.payload_offset % vector.required_alignment == 0 && vector.payload_length <= vector.available_size - vector.payload_offset; }
inline constexpr std::array<AbiLayoutVectorV1, 9> abi_layout_vectors_v1{{
    {"valid_exact", 48, 32, 32, 16, 8, 0, true},
    {"valid_append_only_tail", 56, 40, 40, 16, 8, 0, true},
    {"truncated_prefix", 48, 31, 32, 16, 8, 0, false},
    {"declared_oversize", 48, 56, 56, 0, 8, 0, false},
    {"reserved_nonzero", 48, 32, 32, 16, 8, 1, false},
    {"offset_before_header", 48, 32, 24, 16, 8, 0, false},
    {"offset_length_overflow", 48, 32, 40, 16, 8, 0, false},
    {"misaligned_offset", 48, 32, 36, 8, 8, 0, false},
    {"invalid_alignment", 48, 32, 32, 16, 3, 0, false},
}};

namespace interface_Admin {
inline constexpr char id[] = "774ef7ed0867a5504ca3899f4a8510fe";
inline constexpr std::uint32_t major = 2;
inline constexpr std::uint64_t required_operation_mask = 1ULL;
inline constexpr std::uint32_t operation_close_slot = 0;
inline constexpr char operation_close_id[] = "2a9d56986e4ac46941252f0e3d30f20";
} // namespace interface_Admin

namespace interface_Query {
inline constexpr char id[] = "652892b824034510f0dd913ba07aa15c";
inline constexpr std::uint32_t major = 1;
inline constexpr std::uint64_t required_operation_mask = 2ULL;
inline constexpr std::uint32_t operation_poll_slot = 0;
inline constexpr char operation_poll_id[] = "babf0f4e009397173c2fb0e9f3a0f76";
inline constexpr std::uint32_t operation_submit_slot = 1;
inline constexpr char operation_submit_id[] = "067d29d193ceaea1cbd9904868ad4ea9";
} // namespace interface_Query

} // namespace simple::kpf::generated

#endif
