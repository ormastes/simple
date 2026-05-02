/*
 * C++ consumer test for SFFI round-trip verification.
 * Compiles against the generated calculator.hpp header and links
 * with the shared library produced from calculator.spl.
 * Verifies RAII lifecycle, move semantics, and noexcept guarantees.
 */
#include <iostream>
#include <cassert>
#include <utility>
#include "calculator.hpp"

int main() {
    spl::Library lib;  // RAII init/shutdown

    // Test standalone exported functions
    assert(spl::calculator_square(5) == 25);
    assert(spl::calculator_square(0) == 0);
    assert(spl::calculator_add(3, 4) == 7);
    assert(spl::calculator_add(-1, 1) == 0);

    // Test class RAII lifecycle
    {
        spl::Calculator calc = spl::Calculator::create();
        calc.add(10);
        assert(calc.get_accumulator() == 10);
        calc.multiply(3);
        assert(calc.get_accumulator() == 30);
    }  // destructor called here -- must not crash

    // Test move semantics
    {
        spl::Calculator calc1 = spl::Calculator::create();
        calc1.add(42);
        assert(calc1.get_accumulator() == 42);

        // Move construct -- calc1 should be moved-from
        spl::Calculator calc2 = std::move(calc1);
        assert(calc2.get_accumulator() == 42);
    }  // only calc2 destructor fires, calc1 was moved-from

    // Test noexcept move constructor (compile-time check)
    static_assert(std::is_nothrow_move_constructible<spl::Calculator>::value,
                  "Calculator move constructor must be noexcept");

    std::cout << "PASS: all C++ round-trip tests passed" << std::endl;
    return 0;
}
