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

struct surjective_conclusion_plan {
    std::vector<std::pair<std::size_t, std::size_t>> concluded_equalities;
    std::vector<std::pair<predicate, std::vector<size_t>>> concluded_predicates;
};

surjective_conclusion_plan plan_surjective_conclusion(
    const join_plan& premise_plan,
    const formula& conclusion
);

struct surjective_delta {
    std::vector<std::pair<std::size_t, std::size_t>> equalities; // use union find?
    std::unordered_map<predicate, std::unordered_set<std::vector<std::size_t>>> relations;
};

bool merge_into(const surjective_delta& delta, partial_structure& pstruct);

void surjective_closure_step(
    const join_plan& premise_plan,
    const surjective_conclusion_plan& conclusion_plan,
    const partial_structure& pstruct,
    surjective_delta& delta
);
