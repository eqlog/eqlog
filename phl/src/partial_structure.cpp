#include <partial_structure.hpp>

using std::vector;
using std::size_t;
using std::find;
using std::move;

void compact_relations(partial_structure& pstruct) {
    vector<vector<size_t>> changed_rows;
    for (auto& [_, rows] : pstruct.relations) {
        changed_rows.clear();
        auto it = rows.begin();
        while (it != rows.end()) {
            bool contains_changes = find_if(it->begin(), it->end(), [&](size_t arg) -> bool {
                return get_representative(pstruct.equality, arg) != arg;
            }) != it->end();

            if (contains_changes) {
                vector<size_t> changed_row;
                changed_row.reserve(it->size());
                for (size_t arg : *it) {
                    changed_row.push_back(get_representative(pstruct.equality, arg));
                }
                changed_rows.push_back(move(changed_row));
                it = rows.erase(it);
            } else {
                ++it;
            }
        }

        for (vector<size_t>& changed_row : changed_rows) {
            rows.insert(move(changed_row));
        }
    }
}
