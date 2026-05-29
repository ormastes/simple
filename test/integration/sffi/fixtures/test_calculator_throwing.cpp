/*
 * C++ consumer test for the optional exception facade.
 * Compiles against the generated calculator.hpp header with
 * SIMPLE_SFFI_ENABLE_CPP_EXCEPTIONS enabled.
 */
#include <cassert>
#include <iostream>
#include <stdexcept>
#define SIMPLE_SFFI_ENABLE_CPP_EXCEPTIONS 1
#include "calculator.hpp"

int main() {
    spl::Library lib;

    assert(spl::calculator_checked_divide_or_throw(9, 3) == 3);

    bool threw = false;
    try {
        (void)spl::calculator_checked_divide_or_throw(9, 0);
    } catch (const std::runtime_error& err) {
        threw = true;
        assert(std::string(err.what()) == "divide by zero");
    }

    assert(threw);
    std::cout << "PASS: optional C++ exception facade works" << std::endl;
    return 0;
}
