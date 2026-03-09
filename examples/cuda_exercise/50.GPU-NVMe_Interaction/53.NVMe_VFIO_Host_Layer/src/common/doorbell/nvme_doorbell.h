/**
 * @file nvme_doorbell.h
 * @brief NVMe doorbell strategies using CRTP for zero-overhead dispatch
 */

#pragma once

#include <cstdint>
#include <type_traits>
#include <atomic>
#include "cuda_utils.h"

// ============================================================================
// Base Doorbell Handle
// ============================================================================

/// Base struct for type-safe doorbell polymorphism
struct DoorbellHandle {
    virtual ~DoorbellHandle() = default;
};

/**
 * @brief Write to volatile memory with system-wide fence before and after
 * @param[out] dst Destination pointer (volatile for hardware visibility)
 * @param[in] value Value to write
 * @note GPU: Uses __threadfence_system(); Host: Uses atomic fences
 */
__host__ __device__ inline void fenced_write(volatile uint32_t* dst, uint32_t value) {
#ifdef __CUDA_ARCH__
    __threadfence_system();
    *dst = value;
    __threadfence_system();
#else
    std::atomic_thread_fence(std::memory_order_release);
    *dst = value;
    std::atomic_thread_fence(std::memory_order_seq_cst);
#endif
}

/**
 * @brief Write to volatile memory with bidirectional fencing
 * @param[out] dst Destination pointer (volatile for hardware visibility)
 * @param[in] value Value to write
 * @note GPU: Uses __threadfence_system(); Host: Uses release+acquire fences
 */
__host__ __device__ inline void double_fenced_write(volatile uint32_t* dst, uint32_t value) {
#ifdef __CUDA_ARCH__
    __threadfence_system();
    *dst = value;
    __threadfence_system();
#else
    std::atomic_thread_fence(std::memory_order_release);
    *dst = value;
    std::atomic_thread_fence(std::memory_order_acquire);
#endif
}

// ============================================================================
// Type Traits
// ============================================================================

/// Type trait for doorbell handle check
template<typename T>
struct is_doorbell_handle {
    static constexpr bool value = std::is_base_of_v<DoorbellHandle, T>;
};

template<typename T>
inline constexpr bool is_doorbell_handle_v = is_doorbell_handle<T>::value;

// ============================================================================
// Doorbell Mode Enumeration
// ============================================================================

/// Doorbell mode: <builder>_<mechanism> where builder={HOST,GPU}, mechanism={MMIO,DBC,DBC_DAEMON}
enum : uint8_t {
    DOORBELL_MODE_HOST_MMIO       = 0,  ///< Host queue + MMIO doorbell (host only)
    DOORBELL_MODE_HOST_DBC         = 2,  ///< Host queue + hardware DBC
    DOORBELL_MODE_GPU_DBC          = 3,  ///< GPU queue + hardware DBC (M55.2)
    DOORBELL_MODE_HOST_DBC_DAEMON  = 4,  ///< Host queue + daemon DBC
    DOORBELL_MODE_GPU_DBC_DAEMON   = 5   ///< GPU queue + daemon DBC (M55.3)
};

using DoorbellMode = uint8_t;

// ============================================================================
// Legacy Doorbell Enum (compatibility)
// ============================================================================

/// @deprecated Prefer DoorbellHandle-based interfaces; retained for C ABI
enum DoorbellType : uint8_t {
    DOORBELL_MMIO              = 0,  // Direct MMIO doorbell (host only)
    DOORBELL_DEFERRED          = 1,
    DOORBELL_DEFERRED_EVENTIDX = 2
};

// ============================================================================
// Doorbell Handle Tags (host defaults)
// ============================================================================

/// Marker type for immediate doorbells (MMIO - host only)
class ImmediateDoorbell : public DoorbellHandle {
public:
    static constexpr DoorbellMode mode = 0;  // Direct MMIO mode
};

/// Marker type for deferred doorbells (DBC shadow buffers or daemons)
class DeferredDoorbell : public DoorbellHandle {
public:
    static constexpr DoorbellMode mode = DOORBELL_MODE_GPU_DBC_DAEMON;
};

/// Marker type for event-indexed (DBC) doorbells
class EventIndexedDoorbell : public DeferredDoorbell {
public:
    static constexpr DoorbellMode mode = DOORBELL_MODE_HOST_DBC;
};

/**
 * @brief Get singleton immediate doorbell handle (MMIO mode)
 * @return Reference to static ImmediateDoorbell instance
 */
inline const ImmediateDoorbell& getImmediateDoorbellHandle() {
    static const ImmediateDoorbell handle{};
    return handle;
}

/**
 * @brief Get singleton deferred doorbell handle (daemon/shadow mode)
 * @return Reference to static DeferredDoorbell instance
 */
inline const DeferredDoorbell& getDeferredDoorbellHandle() {
    static const DeferredDoorbell handle{};
    return handle;
}

/**
 * @brief Get singleton event-indexed doorbell handle (DBC mode)
 * @return Reference to static EventIndexedDoorbell instance
 */
inline const EventIndexedDoorbell& getEventIndexedDoorbellHandle() {
    static const EventIndexedDoorbell handle{};
    return handle;
}

/**
 * @brief Check if handle is immediate (MMIO) doorbell
 * @param[in] handle Doorbell handle to check
 * @return true if handle is ImmediateDoorbell type
 */
inline bool is_immediate_doorbell(const DoorbellHandle& handle) {
    return dynamic_cast<const ImmediateDoorbell*>(&handle) != nullptr;
}

/**
 * @brief Check if handle is event-indexed (DBC hardware) doorbell
 * @param[in] handle Doorbell handle to check
 * @return true if handle is EventIndexedDoorbell type
 */
inline bool is_event_indexed_doorbell(const DoorbellHandle& handle) {
    return dynamic_cast<const EventIndexedDoorbell*>(&handle) != nullptr;
}

/**
 * @brief Check if handle is deferred (shadow/daemon) doorbell
 * @param[in] handle Doorbell handle to check
 * @return true if handle is DeferredDoorbell type
 */
inline bool is_deferred_doorbell(const DoorbellHandle& handle) {
    return dynamic_cast<const DeferredDoorbell*>(&handle) != nullptr;
}

// ============================================================================
// Doorbell Strategy Pattern (CRTP Base Class)
// ============================================================================

/// CRTP base for zero-overhead doorbell dispatch
template<typename Derived>
class DoorbellStrategy : public DoorbellHandle {
public:
    /// Ring SQ doorbell (compile-time dispatch to Derived::ring_sq_doorbell_impl)
    __device__ __host__ inline void ring_sq_doorbell(uint16_t tail) {
        static_cast<Derived*>(this)->ring_sq_doorbell_impl(tail);
    }

    /// Ring CQ doorbell
    __device__ __host__ inline void ring_cq_doorbell(uint16_t head) {
        static_cast<Derived*>(this)->ring_cq_doorbell_impl(head);
    }

protected:
    __device__ __host__ DoorbellStrategy() = default;
    ~DoorbellStrategy() = default;
    DoorbellStrategy(const DoorbellStrategy&) = delete;
    DoorbellStrategy& operator=(const DoorbellStrategy&) = delete;
    __device__ __host__ DoorbellStrategy(DoorbellStrategy&&) = default;
    __device__ __host__ DoorbellStrategy& operator=(DoorbellStrategy&&) = default;
};

/// Type trait for doorbell strategy verification
template<typename T>
struct is_doorbell_strategy {
    static constexpr bool value = std::is_base_of<DoorbellStrategy<T>, T>::value;
};

template<typename T>
inline constexpr bool is_doorbell_strategy_v = is_doorbell_strategy<T>::value;

// ============================================================================
// MMIO Doorbell Strategy Implementation
// ============================================================================

/**
 * @note MmioDoorbell class removed - GPU kernels cannot access MMIO registers
 * Use ShadowDoorbell or DBC Daemon mechanisms instead
 */

// ============================================================================
// Shadow Doorbell Strategy Implementation (DBC)
// ============================================================================

/**
 * @brief Shadow doorbell (DBC) with writes to pinned host memory buffer
 */
class ShadowDoorbell : public DoorbellStrategy<ShadowDoorbell> {
public:
    static constexpr DoorbellMode doorbell_mode = DOORBELL_MODE_HOST_DBC;

private:
    volatile uint32_t* shadow_db_base_;  ///< Base pointer to shadow doorbell buffer
    uint16_t qid_;                       ///< Queue ID (for index calculation)

public:
    /**
     * @brief Construct shadow doorbell with DBC buffer and queue ID
     * @param[in] shadow_db_base Base pointer to DBC shadow buffer (host pinned memory)
     * @param[in] qid Queue ID (used for offset calculation: [2*qid] = SQ, [2*qid+1] = CQ)
     */
    __device__ __host__
    ShadowDoorbell(volatile uint32_t* shadow_db_base, uint16_t qid)
        : shadow_db_base_(shadow_db_base), qid_(qid) {}

    /**
     * @brief Ring submission queue doorbell to shadow buffer
     * @param[in] tail New SQ tail value (0..queue_depth-1)
     * @note Writes to shadow_db_base[2*qid] with bidirectional fencing
     */
    __device__ __host__ inline void ring_sq_doorbell_impl(uint16_t tail) {
        double_fenced_write(&shadow_db_base_[2 * qid_], tail);
    }

    /**
     * @brief Ring completion queue doorbell to shadow buffer
     * @param[in] head New CQ head value (0..queue_depth-1)
     * @note Writes to shadow_db_base[2*qid+1] with bidirectional fencing
     */
    __device__ __host__ inline void ring_cq_doorbell_impl(uint16_t head) {
        double_fenced_write(&shadow_db_base_[2 * qid_ + 1], head);
    }

    // Accessors
    /// @brief Read current SQ shadow doorbell value
    __device__ __host__ inline uint32_t read_sq_doorbell() const { return shadow_db_base_[2 * qid_]; }
    /// @brief Read current CQ shadow doorbell value
    __device__ __host__ inline uint32_t read_cq_doorbell() const { return shadow_db_base_[2 * qid_ + 1]; }
    /// @brief Get queue ID
    __device__ __host__ inline uint16_t queue_id() const { return qid_; }
    /// @brief Get base pointer to shadow doorbell buffer
    __device__ __host__ inline volatile uint32_t* shadow_db_ptr() const { return shadow_db_base_; }
    /// @brief Get SQ shadow doorbell pointer (shadow_db_base + 2*qid)
    __device__ __host__ inline volatile uint32_t* sq_doorbell_ptr() const { return &shadow_db_base_[2 * qid_]; }
    /// @brief Get CQ shadow doorbell pointer (shadow_db_base + 2*qid + 1)
    __device__ __host__ inline volatile uint32_t* cq_doorbell_ptr() const { return &shadow_db_base_[2 * qid_ + 1]; }
};

// Verify that ShadowDoorbell properly implements DoorbellStrategy interface
static_assert(is_doorbell_strategy_v<ShadowDoorbell>,
              "ShadowDoorbell must inherit from DoorbellStrategy<ShadowDoorbell>");

/// Event Index Buffer: optional interrupt moderation with DBC (NVMe 1.4 §8.6, not implemented here)
