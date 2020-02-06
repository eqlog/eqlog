#pragma once

#include <cstddef>
#include <vector>
#include <functional>

// helper for creating overloaded function using lambdas; see formula_join_plan
template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

inline std::size_t combine_hashes(std::size_t h1, std::size_t h2) {
    return h1 ^ (h2 + 0x9e3779b9 + (h1 << 6) + (h1 >> 2));
}


template<class T, class... Ts>
struct combined_hash_impl;
template<class T>
struct combined_hash_impl<T> {
    static std::size_t doit(const T& t) {
        return std::hash<T>{}(t);
    }
};
template<class T, class... Ts> 
struct combined_hash_impl {
    static std::size_t doit(const T& t, const Ts&... ts) {
        return combine_hashes(std::hash<T>{}(t), combined_hash_impl<Ts...>::doit(ts...));
    }
};

template<class T, class... Ts>
std::size_t combined_hash(const T& t, const Ts&... ts) {
    return combined_hash_impl<T, Ts...>::doit(t, ts...);
}

namespace std {
    template<class T>
    struct hash<vector<T>> {
        // TODO: make this dependent on T
        size_t operator()(const vector<T>& v) const {
            size_t accum = 791658261336296109; // some random but fixed 64 bit value
            for (const auto& t : v) {
                accum = combine_hashes(accum, std::hash<T>{}(t));
            }
            return accum;
        }
    };
}
