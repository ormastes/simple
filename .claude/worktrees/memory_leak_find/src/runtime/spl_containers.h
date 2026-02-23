// spl_containers.h — C++ stdlib thin wrappers for Simple containers
// Header-only, no runtime.h dependency.
// Generated code includes this for Array, Dict, Set, List, Option types.

#ifndef SPL_CONTAINERS_H
#define SPL_CONTAINERS_H

#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <list>
#include <string>
#include <cstdint>
#include <stdexcept>
#include <algorithm>
#include <tuple>

namespace spl {

// ============================================================================
// Option<T> — nullable value wrapper
// ============================================================================

template <typename T>
class Option {
    bool present_;
    T value_;

public:
    Option() : present_(false), value_{} {}
    explicit Option(T val) : present_(true), value_(std::move(val)) {}

    static Option none() { return Option(); }
    static Option some(T val) { return Option(std::move(val)); }

    bool has_value() const { return present_; }

    T unwrap() const {
        if (!present_) throw std::runtime_error("unwrap on empty Option");
        return value_;
    }

    T unwrap_or(T default_val) const {
        return present_ ? value_ : default_val;
    }

    explicit operator bool() const { return present_; }
};

// ============================================================================
// Array<T> — wraps std::vector<T>
// ============================================================================

template <typename T>
class Array {
    std::vector<T> data_;

public:
    Array() = default;
    Array(std::initializer_list<T> init) : data_(init) {}
    explicit Array(std::vector<T> v) : data_(std::move(v)) {}

    void push(const T& val) { data_.push_back(val); }

    Option<T> pop() {
        if (data_.empty()) return Option<T>::none();
        T val = std::move(data_.back());
        data_.pop_back();
        return Option<T>::some(std::move(val));
    }

    T get(int64_t idx) const {
        if (idx < 0 || idx >= static_cast<int64_t>(data_.size()))
            throw std::runtime_error("Array index out of bounds");
        return data_[static_cast<size_t>(idx)];
    }

    void set(int64_t idx, const T& val) {
        if (idx < 0 || idx >= static_cast<int64_t>(data_.size()))
            throw std::runtime_error("Array index out of bounds");
        data_[static_cast<size_t>(idx)] = val;
    }

    int64_t len() const { return static_cast<int64_t>(data_.size()); }

    Array<T> slice(int64_t start, int64_t end) const {
        if (start < 0) start = 0;
        if (end > static_cast<int64_t>(data_.size()))
            end = static_cast<int64_t>(data_.size());
        if (start >= end) return Array<T>();
        return Array<T>(std::vector<T>(
            data_.begin() + start,
            data_.begin() + end));
    }

    Array<T> concat(const Array<T>& other) const {
        std::vector<T> result = data_;
        result.insert(result.end(), other.data_.begin(), other.data_.end());
        return Array<T>(std::move(result));
    }

    bool contains(const T& val) const {
        return std::find(data_.begin(), data_.end(), val) != data_.end();
    }

    const std::vector<T>& raw() const { return data_; }
    std::vector<T>& raw() { return data_; }
};

// ============================================================================
// Dict<V> — wraps std::unordered_map<std::string, V>
// ============================================================================

template <typename V>
class Dict {
    std::unordered_map<std::string, V> data_;

public:
    Dict() = default;

    void set(const std::string& key, const V& val) { data_[key] = val; }

    Option<V> get(const std::string& key) const {
        auto it = data_.find(key);
        if (it == data_.end()) return Option<V>::none();
        return Option<V>::some(it->second);
    }

    bool contains(const std::string& key) const {
        return data_.count(key) > 0;
    }

    bool remove(const std::string& key) {
        return data_.erase(key) > 0;
    }

    int64_t len() const { return static_cast<int64_t>(data_.size()); }

    Array<std::string> keys() const {
        Array<std::string> result;
        for (const auto& [k, v] : data_) result.push(k);
        return result;
    }

    Array<V> values() const {
        Array<V> result;
        for (const auto& [k, v] : data_) result.push(v);
        return result;
    }

    const std::unordered_map<std::string, V>& raw() const { return data_; }
    std::unordered_map<std::string, V>& raw() { return data_; }
};

// ============================================================================
// Set<T> — wraps std::unordered_set<T>
// ============================================================================

template <typename T>
class Set {
    std::unordered_set<T> data_;

public:
    Set() = default;

    void insert(const T& val) { data_.insert(val); }
    bool contains(const T& val) const { return data_.count(val) > 0; }
    bool remove(const T& val) { return data_.erase(val) > 0; }
    int64_t len() const { return static_cast<int64_t>(data_.size()); }

    const std::unordered_set<T>& raw() const { return data_; }
};

// ============================================================================
// List<T> — wraps std::list<T>
// ============================================================================

template <typename T>
class List {
    std::list<T> data_;

public:
    List() = default;

    void push_back(const T& val) { data_.push_back(val); }
    void push_front(const T& val) { data_.push_front(val); }

    Option<T> pop_back() {
        if (data_.empty()) return Option<T>::none();
        T val = std::move(data_.back());
        data_.pop_back();
        return Option<T>::some(std::move(val));
    }

    int64_t len() const { return static_cast<int64_t>(data_.size()); }

    const std::list<T>& raw() const { return data_; }
};

} // namespace spl

#endif // SPL_CONTAINERS_H
