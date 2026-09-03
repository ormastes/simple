#ifndef SIMPLE_KPF_GENERATED_SCHEMA_HPP
#define SIMPLE_KPF_GENERATED_SCHEMA_HPP

#include <cstdint>

namespace simple::kpf::generated {

inline constexpr std::uint32_t abi_v1 = 1;
inline constexpr char schema_digest[] = "42a1584d4146fe4507a9ecaffddc09bfa0290549da8010ad0161c10b10197fcc";

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
