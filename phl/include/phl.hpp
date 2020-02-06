#pragma once

#include <util.hpp>
#include <variant>
#include <vector>
#include <string_view>

typedef std::string_view sort;
struct predicate;
struct operation;

struct applied_operation;
typedef std::string_view variable;
typedef std::variant<variable, applied_operation> term;

typedef std::pair<term, term> equality;
struct applied_predicate;
typedef std::variant<equality, applied_predicate> atomic_formula;
typedef std::vector<atomic_formula> formula;

struct sequent;

struct predicate {
    std::string_view name;
    std::vector<sort> arity;

    formula operator()(std::vector<term> args) const;
    formula operator()() const;
    formula operator()(term t0) const;
    formula operator()(term t0, term t1) const;
    formula operator()(term t0, term t1, term t2) const;
    formula operator()(term t0, term t1, term t2, term t3) const;
};

struct operation {
    std::string_view name;
    std::vector<sort> dom;
    sort cod;

    term operator()(std::vector<term> args) const;
    term operator()() const;
    term operator()(term t0) const;
    term operator()(term t0, term t1) const;
    term operator()(term t0, term t1, term t2) const;
    term operator()(term t0, term t1, term t2, term t3) const;
};

struct applied_operation {
    operation op;
    std::vector<term> args;
};

struct applied_predicate {
    predicate pred;
    std::vector<term> args;
};

struct sequent {
    formula premise;
    formula conclusion;
};


inline formula predicate::operator()(std::vector<term> args) const {
    return {applied_predicate{*this, std::move(args)}};
}
inline formula predicate::operator()() const {
    return this->operator()(std::vector<term>{});
}
inline formula predicate::operator()(term t0) const {
    return this->operator()(std::vector<term>{std::move(t0)});
}
inline formula predicate::operator()(term t0, term t1) const {
    return this->operator()(std::vector<term>{std::move(t0), std::move(t1)});
}
inline formula predicate::operator()(term t0, term t1, term t2) const {
    return this->operator()(std::vector<term>{std::move(t0), std::move(t1), std::move(t2)});
}
inline formula predicate::operator()(term t0, term t1, term t2, term t3) const {
    return this->operator()(std::vector<term>{std::move(t0), std::move(t1), std::move(t2), std::move(t3)});
}

inline term operation::operator()(std::vector<term> args) const {
    return applied_operation{*this, std::move(args)};
}
inline term operation::operator()() const {
    return this->operator()(std::vector<term>{});
}
inline term operation::operator()(term t0) const {
    return this->operator()(std::vector<term>{std::move(t0)});
}
inline term operation::operator()(term t0, term t1) const {
    return this->operator()(std::vector<term>{std::move(t0), std::move(t1)});
}
inline term operation::operator()(term t0, term t1, term t2) const {
    return this->operator()(std::vector<term>{std::move(t0), std::move(t1), std::move(t2)});
}
inline term operation::operator()(term t0, term t1, term t2, term t3) const {
    return this->operator()(std::vector<term>{std::move(t0), std::move(t1), std::move(t2), std::move(t3)});
}

inline term operator "" _v(const char* cs, std::size_t size) {
    return std::string_view{cs, size};
}

inline formula operator%(term lhs, term rhs) {
    return {equality{std::move(lhs), std::move(rhs)}};
}

inline formula operator&&(formula lhs, const formula& rhs) {
    lhs.insert(lhs.end(), rhs.begin(), rhs.end());
    return lhs;
}

inline sequent operator|=(formula premise, formula conclusion) {
    return {std::move(premise), std::move(conclusion)};
}


struct phl_signature {
    std::vector<sort> sorts;
    std::vector<predicate> predicates;
    std::vector<operation> operations;
};

struct phl_theory {
    phl_signature signature;
    std::vector<sequent> injective_axioms;
    std::vector<sequent> surjective_axioms;
};

inline bool operator==(const predicate& pred1, const predicate& pred2) {
    return
        pred1.name == pred2.name &&
        pred1.arity == pred2.arity;
}
inline bool operator==(const operation& op1, const operation& op2) {
    return
        op1.name == op2.name && 
        op1.dom == op2.dom &&
        op1.cod == op2.cod;
}
inline bool operator==(const applied_operation& app_op1, const applied_operation& app_op2) {
    return
        app_op1.op == app_op2.op &&
        app_op1.args == app_op2.args;
}
inline bool operator==(const applied_predicate& app_pred1, const applied_predicate& app_pred2) {
    return
        app_pred1.pred == app_pred2.pred &&
        app_pred1.args == app_pred2.args;
}
inline bool operator==(const sequent& seq1, const sequent& seq2) {
    return
        seq1.premise == seq2.premise &&
        seq1.conclusion == seq2.conclusion;
}


namespace std {
    template<>
    struct hash<predicate> {
        size_t operator()(const predicate& pred) const {
            return combined_hash(pred.name, pred.arity);
        }
    };
    template<>
    struct hash<operation> {
        size_t operator()(const operation& op) const {
            return combined_hash(op.name, op.dom, op.cod);
        }
    };
    template<>
    struct hash<applied_operation> {
        size_t operator()(const applied_operation& app_op) const {
            return combined_hash(app_op.op, app_op.args);
        }
    };
    template<>
    struct hash<equality> {
        size_t operator()(const equality& eq) const {
            return combined_hash(eq.first, eq.second);
        }
    };
    template<>
    struct hash<applied_predicate> {
        size_t operator()(const applied_predicate& app_pred) const {
            return combined_hash(app_pred.pred, app_pred.args);
        }
    };
    template<>
    struct hash<sequent> {
        size_t operator()(const sequent& seq) const {
            return combined_hash(seq.premise, seq.conclusion);
        }
    };
}
