#pragma once

#include "empty.h"

// This is just an empty propagator and does nothing more than sending a few
// messages to stdout.
class user_propagator : public z3::user_propagator_base {

public:
    user_propagator(z3::context &c) : user_propagator_base(c) {
        this->register_fixed();
        this->register_final();
    }
    ~user_propagator() = default;

    void final() override {
        std::cout << "Final: " << std::endl;
    }

    void fixed(z3::expr const &ast, z3::expr const &value) override {
        std::cout << "Fixed: " << ast << " = " << value << std::endl;
    }

    void push() override {
        std::cout << "Push! " << std::endl;
    }

    void pop(unsigned num_scopes) override {
        std::cout << "Pop! " << std::endl;
    }

    user_propagator_base *fresh(z3::context &) override {
        return this;
    }
};