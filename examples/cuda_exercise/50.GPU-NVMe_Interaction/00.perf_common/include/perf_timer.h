/**
 * @file perf_timer.h
 * @brief CPU and GPU timer utilities
 */

#ifndef PERF_TIMER_H
#define PERF_TIMER_H

#include <chrono>
#include <cuda_runtime.h>
#include <cstdio>
#include <stdexcept>
#include <string>

namespace perf_common {

/**
 * @brief High-precision CPU timer with flexible usage modes
 *
 * Supports both:
 * - Auto-start on construction (Module 53 style)
 * - Explicit start/stop (Module 57 style)
 */
class Timer {
public:
    using Clock = std::chrono::high_resolution_clock;
    using TimePoint = Clock::time_point;
    using Duration = std::chrono::duration<double>;

private:
    TimePoint start_time_;
    TimePoint end_time_;
    bool running_;
    bool auto_started_;

public:
    /**
     * @brief Constructor with optional auto-start
     * @param auto_start If true, starts timing immediately (default: true)
     */
    explicit Timer(bool auto_start = true)
        : running_(auto_start), auto_started_(auto_start) {
        if (auto_start) {
            start_time_ = Clock::now();
        }
    }

    /**
     * @brief Explicitly start timing (resets if already started)
     */
    void start() {
        start_time_ = Clock::now();
        running_ = true;
        auto_started_ = false;
    }

    /**
     * @brief Stop timing and record end time
     */
    void stop() {
        end_time_ = Clock::now();
        running_ = false;
    }

    /**
     * @brief Reset timer to current time (restarts if running)
     */
    void reset() {
        start_time_ = Clock::now();
        if (!running_) {
            running_ = true;
        }
    }

    /**
     * @brief Get elapsed time in nanoseconds
     */
    uint64_t elapsed_ns() const {
        auto end = running_ ? Clock::now() : end_time_;
        return std::chrono::duration_cast<std::chrono::nanoseconds>(
            end - start_time_).count();
    }

    /**
     * @brief Get elapsed time in microseconds
     */
    double elapsed_us() const {
        return elapsed_ns() / 1000.0;
    }

    /**
     * @brief Get elapsed time in milliseconds
     */
    double elapsed_ms() const {
        return elapsed_ns() / 1000000.0;
    }

    /**
     * @brief Get elapsed time in seconds
     */
    double elapsed_s() const {
        return elapsed_ns() / 1000000000.0;
    }

    /**
     * @brief Check if timer is currently running
     */
    bool is_running() const { return running_; }
};

/**
 * @brief CUDA event-based GPU timer for accurate kernel timing
 */
class CudaTimer {
private:
    cudaEvent_t start_event_;
    cudaEvent_t stop_event_;
    bool running_;
    bool events_created_;

public:
    CudaTimer() : running_(false), events_created_(false) {
        cudaEventCreate(&start_event_);
        cudaEventCreate(&stop_event_);
        events_created_ = true;
    }

    ~CudaTimer() {
        if (events_created_) {
            cudaEventDestroy(start_event_);
            cudaEventDestroy(stop_event_);
        }
    }

    // Delete copy constructor and assignment
    CudaTimer(const CudaTimer&) = delete;
    CudaTimer& operator=(const CudaTimer&) = delete;

    // Allow move semantics
    CudaTimer(CudaTimer&& other) noexcept
        : start_event_(other.start_event_),
          stop_event_(other.stop_event_),
          running_(other.running_),
          events_created_(other.events_created_) {
        other.events_created_ = false;
    }

    /**
     * @brief Start GPU timing
     * @param stream CUDA stream to record event on (default: 0)
     */
    void start(cudaStream_t stream = 0) {
        cudaEventRecord(start_event_, stream);
        running_ = true;
    }

    /**
     * @brief Stop GPU timing
     * @param stream CUDA stream to record event on (default: 0)
     */
    void stop(cudaStream_t stream = 0) {
        cudaEventRecord(stop_event_, stream);
        running_ = false;
    }

    /**
     * @brief Get elapsed time in milliseconds (blocks until events complete)
     */
    float elapsed_ms() {
        if (running_) {
            throw std::runtime_error("Timer still running - call stop() first");
        }

        cudaEventSynchronize(stop_event_);
        float ms = 0;
        cudaEventElapsedTime(&ms, start_event_, stop_event_);
        return ms;
    }

    /**
     * @brief Get elapsed time in microseconds
     */
    float elapsed_us() {
        return elapsed_ms() * 1000.0f;
    }

    /**
     * @brief Get elapsed time in nanoseconds
     */
    uint64_t elapsed_ns() {
        return static_cast<uint64_t>(elapsed_ms() * 1000000.0f);
    }
};

/**
 * @brief Scoped timer that automatically prints elapsed time
 */
class ScopedTimer {
private:
    Timer timer_;
    std::string name_;
    bool print_on_destroy_;

public:
    ScopedTimer(const std::string& name, bool print = true)
        : timer_(true), name_(name), print_on_destroy_(print) {}

    ~ScopedTimer() {
        if (print_on_destroy_) {
            printf("[%s] Elapsed: %.3f ms\n", name_.c_str(), timer_.elapsed_ms());
        }
    }

    double elapsed_ms() const { return timer_.elapsed_ms(); }
};

} // namespace perf_common

#endif // PERF_TIMER_H
