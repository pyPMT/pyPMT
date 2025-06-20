from collections import defaultdict

import z3


class FramePropagator(z3.UserPropagateBase):
    def __init__(self, s, ctx=None, e=None):
        z3.UserPropagateBase.__init__(self, s, ctx)
        self.add_fixed(lambda x, v: self._fixed(x, v))
        self.encoder = e
        self.mutexes = 0
        self.name = ""
        self.true = defaultdict(set)
        self.false = defaultdict(set)
        self.f_trail = []
        self.t_trail = []
        self.f_levels = []
        self.t_levels = []
        self.unchangable  = set()
        # Two watched literals implementation
        self.ids = defaultdict(dict)
        self.watches = defaultdict(dict)
        self.watched_literals = defaultdict(dict)

    # Do we need to add FINAL() to check that all clauses have at least one true in them??

    def push(self):
        self.f_levels.append(len(self.f_trail))
        self.t_levels.append(len(self.t_trail))

    def pop(self, n):
        for _ in range(n):
            if self.f_levels:
                # Find the start of the current decision level
                level_start = self.f_levels.pop()
                # Undo all changes recorded after this level
                while len(self.f_trail) > level_start:
                    step, action = self.f_trail.pop()
                    self.false[step].remove(action)
            if self.t_levels:
                # Find the start of the current decision level
                level_start = self.t_levels.pop()
                # Undo all changes recorded after this level
                while len(self.t_trail) > level_start:
                    step, action = self.t_trail.pop()
                    self.true[step].remove(action)

    def add_clause(self, clause, action, step):
        if not clause:
            # Empty Or clause means that the value cannot changer therefore must conflict
            if action not in self.unchangable:
                self.conflict(deps=[action], eqs=[])
                self.unchangable.add(action)
            return
        if step in self.true and self.true[step] & set(clause):
            # Clause already contains a True action, so we don't need to do anything (already satisfied)
            return
        if all(lit in self.false[step] for lit in clause):
            self.conflict(deps=[action], eqs=[])
            return
        elif len(clause) == 1:
            # If clause only has one literal it must be true for the clause to be satisfied
            lit = self.encoder.up_actions_to_z3[clause[0]][step]
            self.propagate(e=lit, ids=[action])
        else:
            # THIS WILL BE REPLACED BY TWO-WATCHED-LITERALS
            # Propagate an or clauses so that eventually one action must happen to cause the change
            # toProp = set()
            # for o in clause:
            #     toProp.add(self.encoder.get_action_var(o, step))
            # self.propagate(e=z3.Or(toProp), ids=[action])
            id = len(self.ids[step])
            self.ids[step][id] = clause
            self.watched_literals[step][id] = [clause[0], clause[1]]
            self.watches[step].get(clause[0], []).append(id)
            self.watches[step].get(clause[1], []).append(id)


    def _fixed(self, action, value):
        action_str = str(action)
        if ':' in action_str:
            if not value:
                variables = action_str.split(':')
                actions = str(variables[0]).split('_')
                step = int(actions[-1])
                action_name = '_'.join(actions[:-1])
                clause = (
                        self.encoder.frame_add[action_name] +
                        self.encoder.frame_del[action_name] +
                        self.encoder.frame_num[action_name]
                )
                clause = [item[1] for item in clause]
                self.add_clause(clause, action, step)
        else:
            actions = str(action_str).split('_')
            step = int(actions[-1])
            action_name = '_'.join(actions[:-1])
            if value:
                # Add a value set to true to validate OR actions
                self.true[step].add(action_name)
                # Need to track what is true at what step at each decision level (similar to interferenece graph in lazy interference)
                self.t_trail.append((step, action_name))

            else:
                # Update tracking
                if step not in self.false:
                    self.false[step] = set()
                self.false[step].add(action_name)
                self.f_trail.append((step, action_name))
                if action_name not in self.watches[step]:
                    return
                for id in self.watches[step][action_name]:
                    clause = self.ids[step][id]
                    l1, l2 = self.watched_literals[step][id]
                    other = l2 if action == l1 else l1
                    print(l1, l2)
                    if other in self.true[step]:
                        continue
                    # Move to next unassigned literal
                    found_new_watch = False
                    for l in clause:
                        if l not in (l1, l2) and l not in self.false[step]:
                            # Found a new literal to watch
                            self.watched_literals[step][id] = [l, other]
                            self.watches[step][l].append(id)
                            self.watches[step][action].remove(id)
                            found_new_watch = True
                            break
                    if not found_new_watch:
                        # Clause is unit or conflicting
                        if other not in self.true[step] and other not in self.false[step]:
                            self.propagate(e=other, ids=[action])
                        else:
                            self.conflict(deps=[action], eqs=[])
        return
