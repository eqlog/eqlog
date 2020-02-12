cmake_minimum_required(VERSION 3.10)
project(phl)

set(CMAKE_CXX_STANDARD 17)
add_compile_options(-Wall -Wextra -pedantic -Werror -Wno-unused-variable)

add_library(phl src/closure.cpp src/cwf.cpp src/partial_structure.cpp src/union_find.cpp)
target_include_directories(phl PUBLIC include)

install(TARGETS phl DESTINATION .) 

enable_testing()
add_subdirectory(dep/doctest)
add_executable(closure-test test/closure.cpp)
target_link_libraries(closure-test PRIVATE doctest::doctest)
target_link_libraries(closure-test PRIVATE phl)
target_include_directories(closure-test PRIVATE src)
add_test(NAME closure-test COMMAND closure-test)
