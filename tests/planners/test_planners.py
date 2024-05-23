
import os
import pytest
from collections import defaultdict
from timeit import default_timer as timer

from pypmt.apis import solve
from pypmt.shortcuts import *

from .utilities import read_tasks_files

def run_planner(name, pddldir):
    tasks = read_tasks_files(pddldir)
    tasks_results = defaultdict(bool)
    for domainname, domainfile, problemfile in tasks:
        plan = solve(domainfile, problemfile, name, validate_plan=True)
        tasks_results[domainname] = (plan.isvalid, plan.validation_fail_reason)

    failed_domains = []
    for domainname, (result, validation_fail_reason) in tasks_results.items():
        if not result:
            failed_domains.append(f"{domainname}: plan is invalid due to {validation_fail_reason}")
    
    if len(failed_domains) > 0:
        pytest.fail('\n'.join(failed_domains))

def test_planner_seq():
    # First read the planning tasks.
    pddldir = os.path.join(os.path.dirname(__file__), "pddl")
    run_planner("seq", pddldir)

def test_planner_forall():
    pddldir = os.path.join(os.path.dirname(__file__), "pddl")
    run_planner("forall", pddldir)

def test_planner_r2e():
    pddldir = os.path.join(os.path.dirname(__file__), "pddl")
    run_planner("r2e", pddldir)

# MA342: I'm skipping this one since it fails to solve the plans.
def test_planner_qfuf():
    pddldir = os.path.join(os.path.dirname(__file__), "pddl")
    run_planner("qfuf", pddldir)