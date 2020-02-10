#include "closure_impl.hpp"
#include <util.hpp>
#include <phl.hpp>
#include <partial_structure.hpp>
#include <cassert>

using std::vector;
using std::unordered_map;
using std::unordered_set;
using std::pair;
using std::swap;
using std::move;
using std::forward;
using std::size_t;
using std::visit;
using std::get_if;
using std::optional;
using std::nullopt;
using std::max;
using std::variant;

optional<size_t> lookup(const unordered_map<term, size_t>& indices, const term& t) {
    auto it = indices.find(t);
    if (it == indices.end()) {
        return nullopt;
    }
    return it->second;
}

// If t is not a fresh variable, adds t and its subterms recursively to the
// join plan. Returns the index of t in the join if it's not a fresh variable.
void add_subterm_to_plan(join_plan& plan, const term& t) {
    if (lookup(plan.term_indices, t)) {
        // t is already in join
        return;
    }

    // term is not in join yet
    visit(overloaded{
        [&](const variable&) -> void {}, // fresh variable, don't do anything
        [&](const applied_operation& app_op) -> void {
            // applied operation that is not in join already, so we should add it

            // add its subterms 
            for (const term& arg : app_op.args) {
                add_subterm_to_plan(plan, arg);
            }
            // all subterms that are not fresh variables are in the join now
            // the next section of the joined row will correspond to app_op
            const operation& op = app_op.op;
            plan.relations.push_back(op);
            // first index of the part of corresponding to app_op within joined row
            size_t op_begin = plan.joined_row_size;
            plan.joined_row_size += op.dom.size() + 1; // + 1 for result of operation

            // update term_indices and add equalities for args
            for (size_t i = 0; i != app_op.args.size(); ++i) {
                const term& arg = app_op.args[i];
                optional<size_t> arg_index = lookup(plan.term_indices, arg);
                if (arg_index) {
                    // arg already exists in join somwhere, add equality
                    plan.equalities.push_back({*arg_index, op_begin + i});
                } else {
                    // arg is not in join yet (it's necessarily a fresh
                    // variable), add its index to term_indices
                    assert(get_if<variable>(&arg) != nullptr);
                    plan.term_indices.insert({arg, op_begin + i});
                }
            }

            // add result of app_op to term_indices
            plan.term_indices.insert({app_op, op_begin + op.dom.size()});
        }
    }, t);
}

void add_applied_predicate_to_plan(join_plan& plan, const applied_predicate& app_pred) {
    // add arguments to join (unless they're fresh variables)
    for (const term& arg : app_pred.args) {
        add_subterm_to_plan(plan, arg);
    }

    const predicate& pred = app_pred.pred;
    plan.relations.push_back(pred);
    // first index of the part of corresponding to app_pred within joined row
    size_t pred_begin = plan.joined_row_size;
    plan.joined_row_size += pred.arity.size();

    // TODO: don't just copy paste the following from the app_op case of
    // add_subterms_to_plan
    // update term_indices and add equalities for args
    for (size_t i = 0; i != app_pred.args.size(); ++i) {
        const term& arg = app_pred.args[i];
        optional<size_t> arg_index = lookup(plan.term_indices, arg);
        if (arg_index) {
            // arg already exists in join somwhere, add equality
            plan.equalities.push_back({*arg_index, pred_begin + i});
        } else {
            // arg is not in join yet (it's necessarily a fresh
            // variable), add its index to term_indices
            assert(get_if<variable>(&arg) != nullptr);
            plan.term_indices.insert({arg, pred_begin + i});
        }
    }
}

void add_equality_to_plan(join_plan& plan, const equality& eq) {
    const auto& [lhs, rhs] = eq;
    
    add_subterm_to_plan(plan, lhs);
    add_subterm_to_plan(plan, rhs);
    optional<size_t> lhs_index = lookup(plan.term_indices, lhs);
    optional<size_t> rhs_index = lookup(plan.term_indices, rhs);
    assert(lhs_index || rhs_index); // TODO: proper error

    if (lhs_index && rhs_index) {
        plan.equalities.push_back({*lhs_index, *rhs_index});
    } else if (!lhs_index && rhs_index) {
        // lhs is a new variable, rhs a term
        plan.term_indices.insert({lhs, *rhs_index});
    } else {
        assert(lhs_index && !rhs_index);
        // lhs is a term, rhs a new variable
        plan.term_indices.insert({rhs, *lhs_index});
    }
}

join_plan formula_join_plan(const formula& f) {
    join_plan plan = {0, {}, {}, {}};

    // Do first round through atomic_formulas...
    for (const atomic_formula& atom : f) {
        if (const applied_predicate* app_pred = get_if<applied_predicate>(&atom)) {
            add_applied_predicate_to_plan(plan, *app_pred);
        }
    }
    // ...and add equalities now. This way, all variables will have already been added
    for (const atomic_formula& atom : f) {
        if (const equality* eq = get_if<equality>(&atom)) {
            add_equality_to_plan(plan, *eq);
        }
    }

    // make sure that each equality is in order
    for (pair<size_t, size_t>& eq : plan.equalities) {
        if (eq.first > eq.second) {
            swap(eq.first, eq.second);
        }
    }
    // and that the list of equalities is in order
    std::sort(plan.equalities.begin(), plan.equalities.end(), [](auto a, auto b) {
        return max(a.first, a.second) < max(b.first, b.second);
    });

    return plan;
}

size_t relation_arity(const variant<predicate, operation>& rel) {
    return visit(overloaded{
        [](const predicate& p) -> size_t {
            return p.arity.size();
        },
        [](const operation& o) -> size_t {
            return o.dom.size() + 1;
        }
    }, rel);
}

template<class F>
void visit_join_impl(
    F&& f,
    vector<size_t>& joined_row,
    vector<const unordered_set<vector<size_t>>*>::iterator rels_it,
    vector<vector<pair<size_t, size_t>>>::iterator eqs_it,
    size_t remaining_rels
) {
    if (remaining_rels == 0) {
        const vector<size_t>& const_joined_row  = joined_row;
        forward<F>(f)(const_joined_row);
    } else {
        size_t before_size = joined_row.size();
        for (const vector<size_t>& row : **rels_it) {
            joined_row.insert(joined_row.end(), row.begin(), row.end());
            bool is_good_row = true;
            for (auto [lhs, rhs] : *eqs_it) {
                if (joined_row[lhs] != joined_row[rhs]) {
                    is_good_row = false;
                    break;
                }
            }
            if (is_good_row) {
                visit_join_impl(
                    forward<F>(f),
                    joined_row,
                    rels_it + 1,
                    eqs_it + 1,
                    remaining_rels - 1
                );
            }
            joined_row.resize(before_size);
        }
    }
}

template<class F>
void visit_join(F&& f, const join_plan& plan, const partial_structure& pstruct) {
    vector<const unordered_set<vector<size_t>>*> rels;
    vector<vector<pair<size_t, size_t>>> partitioned_eqs;
    vector<pair<size_t, size_t>>::const_iterator eq_it = plan.equalities.begin();
    size_t current_join_size = 0;
    for (const relation& rel_sym : plan.relations) {
        const unordered_set<vector<size_t>>& rel = pstruct.relations.find(rel_sym)->second;
        rels.push_back(&rel);
        current_join_size += relation_arity(rel_sym);
        vector<pair<size_t, size_t>> new_eqs;
        while (
            eq_it != plan.equalities.end() &&
            max(eq_it->first, eq_it->second) < current_join_size
        ) {
            new_eqs.push_back(*eq_it);
            ++eq_it;
        }
        partitioned_eqs.push_back(move(new_eqs));
    }
    assert(rels.size() == plan.relations.size());
    assert(partitioned_eqs.size() == plan.relations.size());
    assert(current_join_size == plan.joined_row_size);
    assert(eq_it == plan.equalities.end());

    vector<size_t> joined_row;
    joined_row.reserve(plan.joined_row_size);

    visit_join_impl(
        forward<F>(f),
        joined_row,
        rels.begin(),
        partitioned_eqs.begin(),
        plan.relations.size()
    );
}

unordered_set<vector<size_t>> compute_join(
    const join_plan& plan,
    const partial_structure& pstruct
) {
    unordered_set<vector<size_t>> join;
    visit_join([&](const vector<size_t>& row) {
        join.insert(row);
    }, plan, pstruct);
    return join;
}

surjective_conclusion_plan plan_surjective_conclusion(
    const join_plan& premise_plan,
    const formula& conclusion
) {
    surjective_conclusion_plan concl_plan{{}, {}};

    for (const atomic_formula af : conclusion) {
        visit(overloaded{
            [&](const equality& eq) -> void {
                const auto& [lhs, rhs] = eq;
                optional<size_t> lhs_index = lookup(premise_plan.term_indices, lhs);
                optional<size_t> rhs_index = lookup(premise_plan.term_indices, rhs);
                assert(lhs_index && rhs_index); // otherwise it's not a surjective sequent
                concl_plan.concluded_equalities.push_back({*lhs_index, *rhs_index});
            },
            [&](const applied_predicate& app_pred) -> void {
                vector<size_t> arg_indices;
                for (const term& arg : app_pred.args) {
                    optional<size_t> arg_index = lookup(premise_plan.term_indices, arg);
                    assert(arg_index); // otherwise it's not a surjective sequent
                    arg_indices.push_back(*arg_index);
                }
                concl_plan.concluded_predicates.push_back({app_pred.pred, move(arg_indices)});
            }
        }, af);
    }

    return concl_plan;
}

void surjective_closure_step(
    const join_plan& premise_plan,
    const surjective_conclusion_plan& conclusion_plan,
    const partial_structure& pstruct,
    surjective_delta& delta
) {
    vector<unordered_set<vector<size_t>>*> delta_rels;
    for (const auto& [pred, _] : conclusion_plan.concluded_predicates) {
        delta_rels.push_back(&delta.relations[pred]);
    }

    visit_join([&](const vector<size_t>& row) {
        // take care of new equalities
        for (pair<size_t, size_t> eq : conclusion_plan.concluded_equalities) {
            delta.equalities.push_back({row[eq.first], row[eq.second]});
        }
        auto it = delta_rels.begin();
        for (const auto& [_, args] : conclusion_plan.concluded_predicates) {
            vector<size_t> substituted_args;
            substituted_args.reserve(args.size());
            for (size_t arg : args) {
                substituted_args.push_back(row[arg]);
            }
            (**it).insert(move(substituted_args));
            ++it;
        }
    }, premise_plan, pstruct);
}

bool merge_into(const surjective_delta& delta, partial_structure& pstruct) {
    bool change = false;
    bool equality_change = false;

    for (auto [lhs, rhs] : delta.equalities) {
        size_t lhs_repr = get_representative(pstruct.equality, lhs);
        size_t rhs_repr = get_representative(pstruct.equality, rhs);
        if (lhs_repr != rhs_repr) {
            merge_into(pstruct.equality, lhs_repr, rhs_repr);
            change = true;
            equality_change = true;
        }
    }

    for (const auto& [pred, delta_rows] : delta.relations) {
        unordered_set<vector<size_t>>& pstruct_rows = pstruct.relations[pred];
        size_t before_size = pstruct_rows.size();
        pstruct_rows.insert(delta_rows.begin(), delta_rows.end());
        if (before_size != pstruct_rows.size()) {
            change = true;
        }
    }

    if (equality_change) {
        // can't do this earlier because delta.relations might contain rows
        // with non-canonical representatives
        compact_relations(pstruct);
    }

    return change;
}


void surjective_closure(
    const std::vector<sequent>& surjections,
    partial_structure& pstruct
) {
    vector<pair<join_plan, surjective_conclusion_plan>> plans;
    for (const sequent& seq : surjections) {
        join_plan premise_plan = formula_join_plan(seq.premise);
        surjective_conclusion_plan conclusion_plan =
            plan_surjective_conclusion(premise_plan, seq.conclusion);
        plans.push_back({premise_plan, conclusion_plan});
    }
    for (const auto& [rel, _] : pstruct.relations) {
        if (const operation* op = get_if<operation>(&rel)) {
            size_t arg_num = op->dom.size();
            vector<pair<size_t, size_t>> equalities;
            for (size_t i = 0; i < arg_num; ++i) {
                equalities.push_back({i, i + arg_num + 1});
            }
            // equalities are not sorted according to max, but it's ok because
            // they're still sorted in order in which they can be checked
            join_plan premise_plan {
                2 * arg_num + 2,
                {rel, rel},
                {}, // careful, doesn't mention the two terms
                move(equalities) 
            };
            surjective_conclusion_plan conclusion_plan{
                {{arg_num, arg_num + 1 + arg_num}},
                {}
            };
            plans.push_back({premise_plan, conclusion_plan});
        }
    }

    surjective_delta delta;
    do {
        for (auto& [_, rows] : delta.relations) {
            rows.clear();
        }
        delta.equalities.clear();
        for (const auto& [premise_plan, conclusion_plan] : plans) {
            surjective_closure_step(premise_plan, conclusion_plan, pstruct, delta);
        }
    } while (merge_into(delta, pstruct));
}
