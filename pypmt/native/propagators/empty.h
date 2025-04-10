#include <z3++.h>
#include <iostream>

// This is just an empty propagator and does nothing more than sending a few
// messages to stdout.
class user_propagator : public z3::user_propagator_base {
public:
    user_propagator(z3::context &c);
    ~user_propagator();

    void final() override;
    void fixed(z3::expr const &ast, z3::expr const &value) override;
    void push() override;
    void pop(unsigned num_scopes) override;
    user_propagator_base *fresh(z3::context &) override;
};
