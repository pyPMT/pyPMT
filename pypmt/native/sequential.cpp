#include <z3++.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <iostream>
#include <vector>
#include <string>
#include <unordered_map>

namespace py = pybind11;


class SequentialPlanner {

private:
    py::object encoder;        // Instance of EncoderSequentialNative from Python
    std::vector<int> schedule; // Schedule for the planner
    z3::context ctx;           // Z3 context
    z3::solver solver;         // Z3 solver
    
    // Maps to store metadata.
    // var_metadata goes from var_name (without timestep) to a dict of metadata
    // This dict includes "name", "time", "sort" and "kind".
    // e.g., "a_foo" -> {"name": "a_foo_0", "time": 0, "sort": "Bool", "kind": "action"}
    // e.g., "at_truck" -> {"name": "at_truck_1", "time": 1, "sort": "Int", "kind": "fluent"}
    std::unordered_map<std::string, std::unordered_map<std::string, std::string>> var_metadata;

    // formula_metadata is a map of formula "kinds" to their string representations.
    // these kinds include "init", "goal", "actions", ... etc.
    std::unordered_map<std::string, std::string> formula_metadata;

    // Time-based storage of instantiated formulas
    // each element of the vector is a given step. The map goes from
    // formula kind to the z3 expression that represents it.
    // e.g., "init" -> z3 expression for the initial state,
    //       "goal" -> z3 expression for the goal state,
    std::vector<std::unordered_map<std::string, z3::expr>> formulas;

    // Time-based storage of instantiated variables
    // each element of the vector is a given step. The map goes from
    // variable name to the z3 expression that represents it.
    // e.g., "a_foo" -> z3 expression for the action at timestep t,
    // Note that the name that indexes the variable does not have the timestep
    // and therefore we can use the var metadata to check its attributes.
    std::vector<std::unordered_map<std::string, z3::expr>> variables;

    // Set of formula kinds
    std::set<std::string> kinds;

public:
    // Constructor
    /**
     * @brief Constructs a SequentialPlanner instance
     * 
     * This constructor initializes a sequential planner by processing encoded variables and formulas from a Python encoder.
     * 
     * The initialization happens in three main steps:
     * 1. Retrieves and stores variable metadata from the encoder's encode_variables_native() method
     * 2. Retrieves and stores formula definitions from the encoder's encode_formulas_native() method
     * 3. Extracts formula kinds from the formula metadata
     * 
     * @param encoder_instance Python object representing the encoder that provides variables and formulas
     * @param schedule Vector of integers defining the execution schedule for planning
     */
    SequentialPlanner(py::object encoder_instance, const std::vector<int>& schedule)
        : encoder(encoder_instance), schedule(schedule), solver(ctx) {

        // 1) Call and store variables map
        py::dict var_map = encoder
            .attr("encode_variables_native")()
            .cast<py::dict>();

        for (auto &item : var_map) {
            std::string key = item.first.cast<std::string>();
            py::dict meta = item.second.cast<py::dict>();
            // Temporary metadata map for this variable
            std::unordered_map<std::string, std::string> metadata;
            for (auto &kv : meta) {
                std::string mkey = kv.first.cast<std::string>();
                std::string mval = kv.second.cast<std::string>();
                metadata[mkey] = mval; // Store metadata in the map
            }
            var_metadata[key] = metadata; // Store the metadata map of this var
        }

        // 2) Call and store formulas map
        py::dict formula_py_map = encoder
            .attr("encode_formulas_native")()
            .cast<py::dict>();
        for (auto &item : formula_py_map) {
            std::string key     = item.first.cast<std::string>();
            std::string formula = item.second.cast<std::string>();
            formula_metadata[key] = formula; // Store the formula
        }
        
        // 3) extract formula kinds
        for (auto &pair : formula_metadata) {
            kinds.insert(pair.first);
        }
        print_templates(); // debug
    }


    /**
     * @brief Performs sequential planning search using the Z3 solver
     * 
     * This method executes the main planning search by:
     * 1. Instantiating formulas at each timestep according to the defined schedule
     * 2. Checking satisfiability using the Z3 solver
     * 3. Collecting the resulting plan or determining that no solution exists
     * 
     * The search follows the schedule defined during planner initialization,
     * creating and solving constraints for each planning step.
     * 
     * @return A Python dictionary containing the search results, which may include:
     *         - The solution plan if found
     *         - Status information about the search process
     *         - Performance metrics or other relevant search data
     */
    py::dict search() {
        // this is the main search method that will be called from Python.
        // It will call the instantiate_step method for each timestep in the
        // schedule and then call the Z3 solver to check for satisfiability.
        py::dict result;
        return result;
    }

private:

    void instantiate_step(int t){
        // This method is called to instantiate the variables and formulas
        // for a given timestep t. These "instantiations" are basically
        // creating the z3 expressions or variables that are in the metadata
        // and storing them in the variables and formulas vectors.

        // Pre: We are going to assume we are incrementally going from 0 to n.
        // Therefore when we have a given t, the search method will already
        // have called instantiate_step from 0 to t-1.

        // It goes as follows:
        // if t == 0:
        //    instantiate the variables at step 0
        //    instantiate only the initial state and the goal

        // else:
        //   instantiate the variables at step t
        //   instantiate the full set of constraints for this step (from t-1 to t)

        // Note the goal should be reified so it can be then used as an
        // assumption in the solver. This should be a new variable added into
        // the metadata
    }

    void create_variables_for_step(int t) {
        // This method creates the variables for a given timestep t.
        // It will create the z3 expressions or variables that are in the metadata
        // and store them in the variables vector.

        // Ensure variables vector is large enough for current time t and next time t+1
        if (variables.size() <= static_cast<size_t>(t + 1)) {
            variables.resize(t + 2); // Access up to index t+1
        }

        // Iterate over the variable metadata to create the z3 expressions
        // for each variable, retrieve the name (the key) and the metadata
        for (const auto& pair : var_metadata) {
            const std::string& base_name = pair.first;
            const std::unordered_map<std::string, std::string>& meta = pair.second;

            const std::string& sort_str = meta.at("sort");
            const std::string& kind_str = meta.at("kind");

            //if (variables[t].find(base_name) == variables[t].end()) {
            // attach the timestep to the name, retrieve the sort and instantiate it
            std::string var_name_t = base_name + "_" + std::to_string(t);
            // Create variable for current timestep t if it doesn't exist
            // and add it to the variables vector in the corresponding timestep
            if (sort_str == "Bool") {
                variables[t][base_name] = ctx.bool_const(var_name_t.c_str());
            } else if (sort_str == "Int") {
                variables[t][base_name] = ctx.int_const(var_name_t.c_str());
            } else if (sort_str == "Real") {
                variables[t][base_name] = ctx.real_const(var_name_t.c_str());
            } else {
                // Handle unknown sort error, e.g., throw an exception or log
                std::cerr << "Error: Unknown sort '" << sort_str << "' for variable " << base_name << std::endl;
            }
            //}
        }
    }

    void create_formulas_for_step(const std::string&, int t) {
        // This method creates the formulas for a given timestep t.
        // It will create the z3 expressions or variables that are in the metadata
        // and store them in the formulas vector.

        // Iterate over the formula metadata and create the z3 expressions
        // for each formula, retrieve the name (the key) and the metadata
        // attach the timestep to the name, retrieve the sort and instantiate it
        // finally, add it to the formulas vector in the corresponding timestep
    }



    // Extract plan from the Z3 model
    py::list extract_plan(const z3::model& model, int horizon) {
        py::list plan;
        py::list actions = encoder.attr("__iter__")().cast<py::list>();

        for (int t = 0; t <= horizon; ++t) {
            for (auto action : actions) {
                py::object action_var = encoder.attr("get_action_var")(action, t);
                if (z3::eq(model.eval(action_var.cast<z3::expr>(), true), ctx.bool_val(true))) {
                    plan.append(action);
                }
            }
        }

        return plan;
    }

    // Method to print variables map for debugging
    void print_templates() {
        std::cout << "Variables:" << std::endl;
        for (auto &pair : var_metadata) {
            std::cout << "  Key: " << pair.first << std::endl;
            for (auto &meta : pair.second) {
                std::cout << "    " << meta.first << " : " << meta.second << std::endl;
            }
        }

        std::cout << "Formulas:" << std::endl;
        for (auto &pair : formula_metadata) {
            std::cout << "  Key: " << pair.first
                      << " -> " << pair.second
                      << std::endl;
        }
    }


};

// Module definition for pybind11
PYBIND11_MODULE(nativeZ3Planner, m) {
    m.doc() = "A Python wrapper for a Sequential Planner using Z3";

    py::class_<SequentialPlanner>(m, "SequentialPlanner")
        .def(py::init<py::object, const std::vector<int>&>(), 
             py::arg("encoder"), py::arg("schedule"))
        .def("search", &SequentialPlanner::search, "Search for a solution");
}