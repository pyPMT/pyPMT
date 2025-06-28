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
        # ----Two watched literals implementation---------

        # Step N {0 -> [a v b v c], 1 -> [b v d v b e]}
        self.ids = defaultdict(dict)
        # Step N {a -> [0,1,2], b ->[2]}
        self.watches = defaultdict(dict)
        # Step N {3 -> [a,b], 5 -> a,c]}
        self.watched_literals = defaultdict(dict)
        # Step N {0 -> fuel_1:fuel_2, 1 -> battery_2:battery_3}
        self.id_change = defaultdict(dict)

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

    def add_clause(self, clause, change_state_variable, step):
        if not clause:
            # Empty Or clause means that the value cannot change therefore must conflict
            self.conflict(deps=[change_state_variable], eqs=[])
            return
        if step in self.true and self.true[step] & set(clause):
            # Clause already contains a True action, so we don't need to do anything (already satisfied)
            return
        if all(lit in self.false[step] for lit in clause):
            # Ideally never executes, but good failsafe
            self.conflict(deps=[change_state_variable], eqs=[])
            return
        elif len(clause) == 1:
            # If clause only has one literal it must be true for the clause to be satisfied
            lit = self.encoder.up_actions_to_z3[clause[0]][step]
            self.propagate(e=lit, ids=[change_state_variable])
        else:
            # New clause seen, need to assign it two watched literals and update datastructures to match
            clause_id = len(self.ids[step])
            self.ids[step][clause_id] = clause
            self.watched_literals[step][clause_id] = [clause[0], clause[1]] #TODO: Should check if unassigned?
            self.watches[step].setdefault(clause[0], []).append(clause_id)
            self.watches[step].setdefault(clause[1], []).append(clause_id)
            self.id_change[step][clause_id] = change_state_variable


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
                # Need to track what is true at what step at each decision level
                # (similar to interference graph in lazy interference)
                self.t_trail.append((step, action_name))
                #
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
                    other = l2 if action_name == l1 else l1
                    if other in self.true[step]:
                        continue
                    # # Move to next unassigned literal
                    found_new_watch = False
                    for l in clause:
                        # Check if ever in True
                        # TODO: Write assert() check if anything unexpected happens
                        if l not in (l1, l2) and l not in self.false[step]:
                            # Found a new literal to watch
                            self.watched_literals[step][id] = [l, other]
                            self.watches[step].setdefault(l, []).append(id)
                            if id in self.watches[step][action_name]:
                                self.watches[step][action_name].remove(id)
                            found_new_watch = True
                            break

                    if not found_new_watch:
                        # TODO: Ensure propagating correct thing
                        # Clause is unit or conflicting
                        if other not in self.true[step] and other not in self.false[step]:
                            # If not all not(OTHER) in clause ->  2nd Watched literal = true
                            # Need to make sure that the changing variable is also enforced
                            conflict = []
                            for l in clause:
                                if l != other and l != action_name:
                                    conflict.append(self.encoder.up_actions_to_z3[l][step])
                            conflict.append(self.id_change[step][id])
                            other_encoded = self.encoder.up_actions_to_z3[other][step]
                            self.propagate(e=other_encoded, ids=conflict)
                        else:
                            # TODO: Create ASCII visualisation of how clauses are added/checked
                            # TODO: Check edge cases (e.g. already assigned false)
                            # All set to false, need to conflict!
                            # All or actions set to False and the variable changed
                            conflicting_lits = []
                            for l in clause:
                                conflicting_lits.append(self.encoder.up_actions_to_z3[l][step])
                            conflicting_lits.append(self.id_change[step][id])
                            self.conflict(deps=conflicting_lits, eqs=[])
                            pass
        return
