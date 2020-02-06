#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include <doctest/doctest.h>

#include <closure_impl.hpp>

using std::vector;
using std::optional;
using std::nullopt;
using std::pair;
using std::variant;
using std::unordered_map;
using std::unordered_set;


using rels = vector<variant<predicate, operation>>;
using eqs = vector<pair<size_t, size_t>>;
using indices = unordered_map<term, size_t>;
using rows = unordered_set<vector<size_t>>;

TEST_CASE("formula_join_plan on empty formula") {
    join_plan plan = formula_join_plan({});
    REQUIRE(plan.joined_row_size == 0);
    REQUIRE(plan.relations == rels({}));
    REQUIRE(plan.equalities == eqs({}));
    REQUIRE(plan.term_indices.empty());
}

TEST_CASE("formula_join plan on p(x, y) && p(y, z)") {
    sort s{"s"};
    predicate p{"p", {s, s}};
    term x = "x", y = "y", z = "z";
    join_plan plan = formula_join_plan(p(x, y) && p(y, z));

    REQUIRE(plan.joined_row_size == 4);
    REQUIRE(plan.relations == rels{p, p});
    REQUIRE(plan.equalities == eqs{{1, 2}});
    REQUIRE(plan.term_indices == indices{
        {x, 0},
        {y, 1},
        {z, 3}
    });
}

TEST_CASE("formula_join_plan on p(x, y) && y % z") {
    sort s{"s"};
    predicate p{"p", {s, s}};
    term x = "x", y = "y", z = "z";
    join_plan plan = formula_join_plan(p(x, y) && y % z);

    REQUIRE(plan.joined_row_size == 2);
    REQUIRE(plan.relations == rels{p});
    REQUIRE(plan.equalities == eqs{});
    REQUIRE(plan.term_indices == indices{
        {x, 0},
        {y, 1},
        {z, 1}
    });
}

TEST_CASE("formula_join_plan on p(x, y) && z % y") {
    sort s{"s"};
    predicate p{"p", {s, s}};
    term x = "x", y = "y", z = "z";
    join_plan plan = formula_join_plan(p(x, y) && z % y);

    REQUIRE(plan.joined_row_size == 2);
    REQUIRE(plan.relations == rels{p});
    REQUIRE(plan.equalities == eqs{});
    REQUIRE(plan.term_indices == indices{
        {x, 0},
        {y, 1},
        {z, 1}
    });
}

TEST_CASE("formula_join_plan on y % z && p(x, y)") {
    sort s{"s"};
    predicate p{"p", {s, s}};
    term x = "x", y = "y", z = "z";
    join_plan plan = formula_join_plan(p(x, y) && z % y);

    REQUIRE(plan.joined_row_size == 2);
    REQUIRE(plan.relations == rels{p});
    REQUIRE(plan.equalities == eqs{});
    REQUIRE(plan.term_indices == indices{
        {x, 0},
        {y, 1},
        {z, 1}
    });
}

TEST_CASE("formula_join_plan on op(x, y) % op(y, x)") {
    sort s{"s"};
    operation op{"op", {s, s}, s};
    term x = "x", y = "y";
    join_plan plan = formula_join_plan(op(x, y) % op(y, x));

    REQUIRE(plan.joined_row_size == 6);
    REQUIRE(plan.relations == rels{op, op});
    REQUIRE(plan.equalities == eqs{
        {1, 3},
        {0, 4},
        {2, 5}
    });
    REQUIRE(plan.term_indices == indices{
        {x, 0},
        {y, 1},
        {op(x, y), 2},
        {op(y, x), 5}
    });
}

TEST_CASE("formula_join_plan on z = op1(x, op2(y, x))") {
    sort s{"s"};
    operation op1{"op1", {s, s}, s};
    operation op2{"op2", {s, s}, s};
    term x = "x", y = "y", z = "z";
    join_plan plan = formula_join_plan(z % op1(x, op2(y, x)));

    REQUIRE(plan.joined_row_size == 6);
    REQUIRE(plan.relations == rels{{op2, op1}});
    REQUIRE(plan.equalities == eqs{
        {1, 3},
        {2, 4}
    });
    REQUIRE(plan.term_indices == indices{
        {y, 0},
        {x, 1},
        {op2(y, x), 2},
        {op1(x, op2(y, x)), 5},
        {z, 5}
    });
}

TEST_CASE("formula_join_plan on p(x, op(x, y))") {
    sort s{"s"};
    operation op{"op", {s, s}, s};
    predicate p{"p", {s, s}};
    term x = "x", y = "y";
    join_plan plan = formula_join_plan(p(x, op(x, y)));

    REQUIRE(plan.joined_row_size == 5);
    REQUIRE(plan.relations == rels{op, p});
    REQUIRE(plan.equalities == eqs{
        {0, 3},
        {2, 4}
    });
    REQUIRE(plan.term_indices == indices{
        {x, 0},
        {y, 1},
        {op(x, y), 2}
    });
}

TEST_CASE("formula_join_plan on y % op(x, x)") {
    sort s{"s"};
    operation op{"op", {s, s}, s};
    term x = "x", y = "y";
    join_plan plan = formula_join_plan(y % op(x, x));

    REQUIRE(plan.joined_row_size == 3);
    REQUIRE(plan.relations == rels{op});
    REQUIRE(plan.equalities == eqs{{0, 1}});
    REQUIRE(plan.term_indices == indices{
        {x, 0},
        {op(x, x), 2},
        {y, 2}
    });
}

TEST_CASE("compute_join over p1(x, y) && p2(z, w)") {
    sort s{"s"};
    sort t{"t"};
    predicate p1{"p1", {s, t}};
    predicate p2{"p2", {s, t}};
    term x = "x", y = "y", z = "z", w = "w";
    join_plan plan = formula_join_plan(p1(x, y) && p2(z, w));

    partial_structure pstruct;
    pstruct.relations[p1] = {
        {0, 0},
        {0, 1},
    };
    pstruct.relations[p2] = {
        {0, 0},
        {0, 1},
        {1, 2},
    };

    REQUIRE(compute_join(plan, pstruct) == rows{
        {0, 0, 0, 0},
        {0, 0, 0, 1},
        {0, 0, 1, 2},
        {0, 1, 0, 0},
        {0, 1, 0, 1},
        {0, 1, 1, 2},
    });
}

TEST_CASE("compute_join over a diagonal") {
    sort s{"s"};
    sort t{"t"};
    predicate p{"p", {s, t}};
    term x = "x";
    join_plan plan = formula_join_plan(p(x, x));

    partial_structure pstruct;
    pstruct.relations[p] = {
        {0, 0},
        {0, 1},
        {1, 2},
        {2, 1},
        {3, 3}
    };

    REQUIRE(compute_join(plan, pstruct) == rows{
        {0, 0},
        {3, 3},
    });
}

TEST_CASE("compute_join over two p1(x, y) && p2(y, z)") {
    sort s{"s"};
    predicate p1{"p1", {s, s}};
    predicate p2{"p2", {s, s}};
    term x = "x", y = "y", z = "z";
    join_plan plan = formula_join_plan(p1(x, y) && p2(y, z));

    partial_structure pstruct;
    pstruct.relations[p1] = {
        {0, 0},
        {1, 1},
        {2, 1},
        {3, 3}
    };
    pstruct.relations[p2] = {
        {0, 0},
        {1, 3},
        {1, 4}
    };

    REQUIRE(compute_join(plan, pstruct) == rows{
        {0, 0, 0, 0},
        {1, 1, 1, 3},
        {1, 1, 1, 4},
        {2, 1, 1, 3},
        {2, 1, 1, 4}
    });
}

TEST_CASE("compute_join over two p1(x, y) && p2(z, x)") {
    sort s{"s"};
    predicate p1{"p1", {s, s}};
    predicate p2{"p2", {s, s}};
    term x = "x", y = "y", z = "z";
    join_plan plan = formula_join_plan(p1(x, y) && p2(z, x));

    partial_structure pstruct;
    pstruct.relations[p1] = {
        {0, 0},
        {1, 1},
        {2, 1},
        {3, 3}
    };
    pstruct.relations[p2] = {
        {0, 0},
        {1, 3},
        {1, 4}
    };

    REQUIRE(compute_join(plan, pstruct) == rows{
        {0, 0, 0, 0},
        {3, 3, 1, 3}
    });
}

TEST_CASE("plan_surjective_conclusion of p1(x, y) && p2(x, z) |= x % y && p1(x, z)") {
    sort s{"s"};
    predicate p1{"p1", {s, s}};
    predicate p2{"p2", {s, s}};
    term x = "x", y = "y", z = "z";

    join_plan premise_plan = formula_join_plan(p1(x, y) && p2(x, z));
    surjective_conclusion_plan conclusion_plan = plan_surjective_conclusion(premise_plan, x % y && p1(x, z));

    REQUIRE(premise_plan.joined_row_size == 4);
    REQUIRE(premise_plan.relations == rels{p1, p2});
    REQUIRE(premise_plan.equalities == eqs{{0, 2}});
    REQUIRE(premise_plan.term_indices == indices{
        {x, 0},
        {y, 1},
        {z, 3}
    });

    REQUIRE(conclusion_plan.concluded_equalities == eqs{
        {0, 1}
    });
    REQUIRE(conclusion_plan.concluded_predicates == vector<pair<predicate, vector<size_t>>>{
        {p1, {0, 3}}
    });
}

TEST_CASE("surjective_closure_step should work for transitivity") {
    sort s{"s"};
    predicate p{"p", {s, s}};
    term x = "x", y = "y", z = "z";
    join_plan premise_plan = formula_join_plan(p(x, y) && p(y, z));
    surjective_conclusion_plan conclusion_plan = plan_surjective_conclusion(premise_plan, p(x, z));
    
    partial_structure pstruct;
    pstruct.equality = {0, 1, 2, 3, 4};
    pstruct.carrier = {
        {0, s},
        {1, s},
        {2, s},
        {3, s},
        {4, s}
    };
    pstruct.relations[p] = {
        {0, 1},
        {1, 2},
        {2, 3},
        {3, 4}
    };

    surjective_delta delta;
    surjective_closure_step(premise_plan, conclusion_plan, pstruct, delta);
    REQUIRE(delta.equalities.size() == 0);
    REQUIRE(delta.relations[p] == rows{
        {0, 2},
        {1, 3},
        {2, 4},
    });
}

TEST_CASE("merge_into should work for predicates") {
    sort s{"s"};
    predicate p{"p", {s, s}};
    
    partial_structure pstruct;
    pstruct.equality = {0, 1, 2, 3, 4};
    pstruct.carrier = {
        {0, s},
        {1, s},
        {2, s},
        {3, s},
        {4, s}
    };
    pstruct.relations[p] = {
        {0, 1},
        {1, 2},
        {2, 3},
        {3, 4}
    };

    surjective_delta delta;
    delta.relations[p] = rows{
        {0, 2},
        {1, 3},
        {2, 4}
    };

    REQUIRE(merge_into(delta, pstruct) == true);
    REQUIRE(pstruct.relations[p] == rows{
        {0, 1},
        {1, 2},
        {2, 3},
        {3, 4},
        {0, 2},
        {1, 3},
        {2, 4}
    });
    partial_structure pstruct_ = pstruct;
    REQUIRE(merge_into(delta, pstruct_) == false);
    REQUIRE(pstruct_.relations == pstruct.relations);
    REQUIRE(pstruct_.equality == pstruct.equality);
}

TEST_CASE("surjective_closure should work for transitivity") {
    sort s{"s"};
    predicate p{"p", {s, s}};
    term x = "x", y = "y", z = "z";
    sequent transitivity = p(x, y) && p(y, z) |= p(x, z);
    
    partial_structure pstruct;
    pstruct.equality = {0, 1, 2, 3, 4};
    pstruct.carrier = {
        {0, s},
        {1, s},
        {2, s},
        {3, s},
        {4, s}
    };
    pstruct.relations[p] = {
        {0, 1},
        {1, 2},
        {2, 3},
        {3, 4}
    };

    partial_structure pstruct_ = pstruct;
    surjective_closure({transitivity}, pstruct);
    REQUIRE(pstruct.equality == pstruct_.equality);
    REQUIRE(pstruct.relations[p] == rows{
        {0, 1},
        {0, 2},
        {0, 3},
        {0, 4},
        {1, 2},
        {1, 3},
        {1, 4},
        {2, 3},
        {2, 4},
        {3, 4},
        {2, 4}
    });
}

TEST_CASE("surjective_closure should work for antisymmetry and two elements") {
    sort s{"s"};
    predicate p{"p", {s, s}};
    term x = "x", y = "y";
    sequent antisymmetry = p(x, y) && p(y, x) |= x % y;

    partial_structure pstruct;
    pstruct.equality = {0, 1};
    pstruct.carrier = {
        {0, s},
        {1, s},
    };
    pstruct.relations[p] = {
        {0, 1},
        {1, 0},
    };

    surjective_closure({antisymmetry}, pstruct);
    auto repr = [&](size_t i) {
        return get_representative(pstruct.equality, i);
    };

    REQUIRE(repr(0) == repr(1));
    REQUIRE(pstruct.relations[p] == rows{
        {repr(0), repr(0)}
    });
}

TEST_CASE("surjective_closure should work for antisymmetry requiring most likely 2 iterrations") {
    sort s{"s"};
    predicate p{"p", {s, s}};
    term x = "x", y = "y";
    sequent antisymmetry = p(x, y) && p(y, x) |= x % y;

    partial_structure pstruct;
    pstruct.equality = {0, 1, 2, 3};
    pstruct.carrier = {
        {0, s},
        {1, s},
        {2, s},
        {3, s},
    };
    pstruct.relations[p] = {
        {0, 1},
        {1, 0},
        {1, 2},
        {2, 0},
        {3, 3}
    };

    surjective_closure({antisymmetry}, pstruct);
    auto repr = [&](size_t i) {
        return get_representative(pstruct.equality, i);
    };

    REQUIRE(repr(0) == repr(1));
    REQUIRE(repr(0) == repr(2));
    REQUIRE(pstruct.relations[p] == rows{
        {repr(0), repr(0)},
        {repr(3), repr(3)}
    });
}

TEST_CASE("surjective_closure should work for free poset of a long cycle") {
    sort s{"s"};
    predicate p{"p", {s, s}};
    term x = "x", y = "y", z = "z";
    // I guess reflexivity is missing here
    sequent antisymmetry = p(x, y) && p(y, x) |= x % y;
    sequent transitivity = p(x, y) && p(y, z) |= p(x, z);

    partial_structure pstruct;
    size_t n = 10;
    for (size_t i = 0; i != n; ++i) {
        pstruct.equality.push_back(i);
    }
    for (size_t i = 0; i != n; ++i) {
        pstruct.carrier.insert({i, s});
    }
    for (size_t i = 0; i != n - 1; ++i) {
        pstruct.relations[p].insert({i, i + 1});
    }
    pstruct.relations[p].insert({n - 1, 0});

    surjective_closure({antisymmetry, transitivity}, pstruct);
    auto repr = [&](size_t i) {
        return get_representative(pstruct.equality, i);
    };

    for (size_t i = 0; i != n; ++i) {
        REQUIRE(repr(i) == repr(0));
    }
    REQUIRE(pstruct.relations[p] == rows{
        {repr(0), repr(0)}
    });
}
