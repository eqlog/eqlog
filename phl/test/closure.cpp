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
