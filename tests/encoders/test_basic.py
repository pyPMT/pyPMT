
import unified_planning
import unified_planning.model
from unified_planning.shortcuts import UserType, BoolType

import pytest

def create_robot_planning_task():
    """!
    The goal here is to create a dummy planning task such that we know its encodings.
    Then we use this task to check that the encoders are working correctly.
    """
    # Step one create a problem's objects.
    Location = UserType('Location')
    robot_at = unified_planning.model.Fluent('robot_at', BoolType(), l=Location)
    
    # Step two create the actions.
    move = unified_planning.model.InstantaneousAction('move', l_from=Location, l_to=Location)
    l_from = move.parameter('l_from')
    l_to = move.parameter('l_to')
    move.add_precondition(robot_at(l_from))
    move.add_effect(robot_at(l_from), False)
    move.add_effect(robot_at(l_to), True)
    
    # Step three create the task.
    problem = unified_planning.model.Problem('robot')
    problem.add_fluent(robot_at, default_initial_value=False)
    problem.add_action(move)

    NLOC = 2
    locations = [unified_planning.model.Object('l%s' % i, Location) for i in range(NLOC)]
    problem.add_objects(locations)

    # Set the initial state.
    problem.set_initial_value(robot_at(locations[0]), True)

    # Set the goal state.
    problem.add_goal(robot_at(locations[-1]))
    return problem


# TODO: This a template function to test the encodings only.
# def test_EncoderSequential():
#     problem = create_robot_planning_task()
#     encoder = EncoderSequential(problem)
#     # Encode the first step of the problem.
#     formula = encoder.encode(0)
#     # Then we need to check the values of the formula.
#     # pytest.fail("The test is not yet implemented.")