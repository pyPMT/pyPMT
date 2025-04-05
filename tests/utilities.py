
import os

def read_tasks_files(pddldir: str):
    """
    Returns a list of all planning tasks in the pddl test directory.
    """
    tasks = list()
    for root, dirs, files in os.walk(pddldir):
        for dir_name in dirs:
            planningtask_dir = os.path.join(root, dir_name)
            domainfile       = os.path.join(planningtask_dir, "domain.pddl")
            problemfile      = os.path.join(planningtask_dir, "problem.pddl")
            domainname       = os.path.basename(planningtask_dir)
            if "__pycache__" in domainfile: continue
            tasks.append((domainname, domainfile, problemfile))
    return tasks


