cmake_minimum_required(VERSION 3.10)
project(rhl)

set(CMAKE_CXX_STANDARD 17)
add_compile_options(-Wall -Wextra -pedantic -Werror)

add_library(rhl src/closure.cpp)
target_include_directories(rhl PUBLIC include)

add_subdirectory(dep/doctest)

add_executable(closure-test test/closure.cpp)
target_link_libraries(closure-test PRIVATE doctest::doctest)
target_link_libraries(closure-test PRIVATE rhl)
target_include_directories(closure-test PRIVATE src)
