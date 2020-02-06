#pragma once

#include <vector>

using union_find = std::vector<std::size_t>;

std::size_t add_element(union_find&);
std::size_t get_representative(union_find&, std::size_t);
void merge_into(union_find&, std::size_t, std::size_t);

