#ifndef SIMPLE_SDK_KERNEL_PLUGIN_CPP_KPF_V1_HPP
#define SIMPLE_SDK_KERNEL_PLUGIN_CPP_KPF_V1_HPP

#include "../c/kpf_v1.h"

#include <cstddef>
#include <cstdint>

namespace simple::kpf {

class Session final {
public:
    Session() noexcept = default;

    static simple_kpf_status_v1 open(
        const simple_kpf_operation_table_v1 &operations,
        std::uint64_t provider_context,
        simple_kpf_borrowed_bytes_v1 configuration,
        Session &result) noexcept {
        if (result.active_) {
            return SIMPLE_KPF_STATUS_REJECTED;
        }
        std::uint64_t session = 0;
        const auto status =
            operations.open_session(provider_context, &configuration, &session);
        if (status == SIMPLE_KPF_STATUS_OK) {
            result.operations_ = &operations;
            result.provider_context_ = provider_context;
            result.session_ = session;
            result.active_ = true;
        }
        return status;
    }

    Session(const Session &) = delete;
    Session &operator=(const Session &) = delete;

    Session(Session &&other) noexcept { move_from(other); }

    Session &operator=(Session &&other) noexcept {
        if (this != &other) {
            shutdown(0, 0);
            move_from(other);
        }
        return *this;
    }

    ~Session() noexcept { shutdown(0, 0); }

    simple_kpf_status_v1 submit(
        std::uint64_t generation,
        std::uint64_t request,
        std::uint32_t interface_slot,
        std::uint32_t operation_slot,
        std::uint64_t deadline_ns,
        simple_kpf_borrowed_bytes_v1 input,
        simple_kpf_output_buffer_v1 &output) noexcept {
        if (!active_ || quiesced_) {
            return SIMPLE_KPF_STATUS_REJECTED;
        }
        auto call = simple_kpf_call_v1(generation, session_, request,
                                       interface_slot, operation_slot, deadline_ns);
        return operations_->submit_batch(provider_context_, &call, &input, &output);
    }

    simple_kpf_status_v1 quiesce(
        std::uint64_t deadline_ns,
        std::uint64_t flags = 0) noexcept {
        if (!active_) {
            return SIMPLE_KPF_STATUS_STALE_HANDLE;
        }
        if (quiesced_) {
            return SIMPLE_KPF_STATUS_OK;
        }
        const auto status = operations_->quiesce(
            provider_context_, session_, deadline_ns, flags);
        if (status == SIMPLE_KPF_STATUS_OK) {
            quiesced_ = true;
        }
        return status;
    }

    simple_kpf_status_v1 close() noexcept {
        if (!active_) {
            return SIMPLE_KPF_STATUS_OK;
        }
        if (!quiesced_) {
            return SIMPLE_KPF_STATUS_REJECTED;
        }
        const auto status = operations_->close_session(provider_context_, session_);
        if (status == SIMPLE_KPF_STATUS_OK) {
            reset();
        }
        return status;
    }

    simple_kpf_status_v1 shutdown(
        std::uint64_t deadline_ns,
        std::uint64_t flags = 0) noexcept {
        if (!active_) {
            return SIMPLE_KPF_STATUS_OK;
        }
        const auto quiesce_status = quiesce(deadline_ns, flags);
        if (quiesce_status != SIMPLE_KPF_STATUS_OK) {
            return quiesce_status;
        }
        return close();
    }

    bool active() const noexcept { return active_; }
    std::uint64_t handle() const noexcept { return session_; }

private:
    void move_from(Session &other) noexcept {
        operations_ = other.operations_;
        provider_context_ = other.provider_context_;
        session_ = other.session_;
        active_ = other.active_;
        quiesced_ = other.quiesced_;
        other.reset();
    }

    void reset() noexcept {
        operations_ = nullptr;
        provider_context_ = 0;
        session_ = 0;
        active_ = false;
        quiesced_ = false;
    }

    const simple_kpf_operation_table_v1 *operations_ = nullptr;
    std::uint64_t provider_context_ = 0;
    std::uint64_t session_ = 0;
    bool active_ = false;
    bool quiesced_ = false;
};

} // namespace simple::kpf

#endif
