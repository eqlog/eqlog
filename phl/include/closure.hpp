#pragma once

#include <phl.hpp>
#include <partial_structure.hpp>

void surjective_closure(
    const std::vector<sequent>& surjective_sequents,
    partial_structure& pstruct
);
