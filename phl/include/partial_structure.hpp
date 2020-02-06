#pragma once

#include <phl.hpp>
#include <util.hpp>

#include <unordered_map>
#include <unordered_set>
#include <string_view>
#include <vector>
#include <variant>

using relation = std::variant<predicate, operation>;

struct partial_structure {
    std::unordered_map<std::size_t, sort> carrier;
    // one relation for each predicate and operation, stored in the order as
    // they appear in (signature.predicates ++ signature.operations)
    std::unordered_map<
        relation,
        std::unordered_set<std::vector<std::size_t>>
    > relations;
};
