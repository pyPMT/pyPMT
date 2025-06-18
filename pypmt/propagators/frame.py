import z3


class FramePropagator(z3.UserPropagateBase):
    def __init__(self, s, ctx=None, e=None):
        z3.UserPropagateBase.__init__(self, s, ctx)
        self.add_fixed(lambda x, v: self._fixed(x, v))
        self.encoder = e
        self.mutexes = 0
        self.name = ""
        self.true = {}
        self.t_trail = []
        self.t_levels = []
        self.unchangable  = set()

    def push(self):
        self.t_levels.append(len(self.t_trail))

    def pop(self, n):
        for _ in range(n):
            if self.t_levels:
                # Find the start of the current decision level
                level_start = self.t_levels.pop()
                # Undo all changes recorded after this level
                while len(self.t_trail) > level_start:
                    step, action = self.t_trail.pop()
                    self.true[step].remove(action)

    def _fixed(self, action, value):
        action_str = str(action)
        if ':' in action_str:
            if not value:
                variables = action_str.split(':')
                actions = str(variables[0]).split('_')
                step = int(actions[-1])
                action_name = '_'.join(actions[:-1])
                ors = (
                        self.encoder.frame_add[action_name] +
                        self.encoder.frame_del[action_name] +
                        self.encoder.frame_num[action_name]
                )
                ors = [item[1] for item in ors]
                # print(ors)
                if not ors:
                    # Empty Or clause means that the value cannot changer therefore must conflict
                    if action not in self.unchangable:
                        self.conflict(deps=[action], eqs=[])
                        self.unchangable.add(action)
                    return
                if step in self.true and self.true[step] & set(ors):
                    # Clause already contains a True action, so we don't need to do anything (already satisfied)
                    return
                elif len(ors) == 1:
                    # print("PROPAGATING")
                    # If clause only has one literal it must be true for the clause to be satisfied
                    lit = self.encoder.up_actions_to_z3[ors[0]][step]
                    self.propagate(e=lit, ids=[action])
                else:
                    # THIS WILL BE REPLACED BY TWO-WATCHED-LITERALS
                    # Propagate an or cluases so that that eventually one action must happen to cause the change
                    toProp = set()
                    for o in ors:
                        toProp.add(self.encoder.get_action_var(o, step))
                    self.propagate(e=z3.Or(toProp), ids=[action])
        else:
            actions = str(action_str).split('_')
            step = int(actions[-1])
            action_name = '_'.join(actions[:-1])
            if value:
                # Add a value set to true to validate OR actions
                if step not in self.true:
                    self.true[step] = set()
                self.true[step].add(action_name)
                # Need to track what is true at what step at each decision level (similar to interferenece graph in lazy interference)
                self.t_trail.append((step, action_name))
        return
