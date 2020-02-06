#pragma once

#include <closure.hpp>
#include <phl.hpp>
#include <vector>
#include <tuple>
#include <unordered_map>
#include <unordered_set>

struct join_plan {
    std::size_t joined_row_size;
    std::vector<relation> relations;
    std::unordered_map<term, size_t> term_indices;
    std::vector<std::pair<size_t, size_t>> equalities;
};

join_plan formula_join_plan(const formula& f);

std::unordered_set<std::vector<size_t>> compute_join(
    const join_plan& plan,
    const partial_structure& pstruct
);
