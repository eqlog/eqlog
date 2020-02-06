#include <union_find.hpp>

using std::vector;
using std::size_t;

size_t add_element(union_find& uf) {
    size_t new_element = uf.size();
    uf.push_back(new_element);
    return new_element;
}
size_t get_representative(union_find& uf, size_t el) {
    if (uf[el] == el) {
        return el;
    }

    // poor man's path compression via recursion
    size_t repr = get_representative(uf, uf[el]);
    uf[el] = repr;
    return repr;
}
void merge_into(union_find& uf, size_t a, size_t b) {
    size_t repr_a = get_representative(uf, a);
    uf[repr_a] = b;
}
