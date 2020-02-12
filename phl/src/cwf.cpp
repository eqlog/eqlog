#include <cassert>
#include <closure.hpp>
#include <cwf.hpp>
#include <partial_structure.hpp>
#include <phl.hpp>
#include <util.hpp>

extern "C" partial_structure* create_cwf() {
    return new partial_structure(cwf::cwf_signature);
}

extern "C" void destroy_cwf(partial_structure* pstruct) {
    delete pstruct;
}

extern "C" const sort* get_sort(const char* name) {
    return &*std::find_if(
        cwf::cwf_signature.sorts.begin(),
        cwf::cwf_signature.sorts.end(),
        [&](auto& sort) {
            return sort == name;
        });
}

extern "C" const operation* get_operation(const char* name) {
    return &*std::find_if(
        cwf::cwf_signature.operations.begin(),
        cwf::cwf_signature.operations.end(),
        [&](auto& op) { return op.name == name; }
    );
}

extern "C" size_t get_operation_arity(const operation* op) {
    return op->dom.size();
}

extern "C" const predicate* get_predicate(const char* name) {
    return &*std::find_if(
        cwf::cwf_signature.predicates.begin(),
        cwf::cwf_signature.predicates.end(),
        [&](auto& pred) { return pred.name == name; }
    );
}

extern "C" bool are_equal(partial_structure* pstruct, size_t l, size_t r) {
    return get_representative(pstruct->equality, l) ==
           get_representative(pstruct->equality, r);
}

extern "C" size_t define_operation(partial_structure* pstruct, const operation* op, const size_t* args) {
    size_t new_id = pstruct->carrier.size();
    pstruct->carrier[new_id] = op->cod;
    size_t uf_id = add_element(pstruct->equality);
    assert(uf_id == new_id);

    std::vector<size_t> vec;
    vec.reserve(op->dom.size() + 1);
    vec.insert(vec.begin(), args, args + op->dom.size());
    vec.push_back(new_id);
    pstruct->relations[*op].insert(std::move(vec));
    return new_id;
}

extern "C" void define_predicate(partial_structure* pstruct, const predicate* pred, const size_t* args) {
    std::vector<size_t> vec(args, args + pred->arity.size());
    pstruct->relations[*pred].insert(vec);
}

extern "C" void compute_fixpoint(partial_structure* pstruct) {
    surjective_closure(cwf::cwf.surjective_axioms, *pstruct);
}