import z3


class FramePropagator(z3.UserPropagateBase):
    def __init__(self, s, ctx=None, e=None):
        z3.UserPropagateBase.__init__(self, s, ctx)
        self.add_fixed(lambda x, v: self._fixed(x, v))
        self.encoder = e
        self.mutexes = 0
        self.false = [set()]
        self.true = [set()]
        self.clauses = set()
        self.name = ""
        self.f_trail = []
        self.t_trail = []
        self.f_levels = []
        self.t_levels = []
        self.watched_literals = {}
        self.ors = {}

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

    def _fixed(self, action, value):

        action_str = str(action)

        if ':' in action_str and not value:
            variables = action_str.split(':')
            key, step = self.extract_key_step(variables[0])
            if key not in self.ors:
                self.ors[key] = (
                        self.encoder.frame_add[key] +
                        self.encoder.frame_del[key] +
                        self.encoder.frame_num[key]
                )
            or_actions = self.ors[key]
            self.ensure_false_size(step)
            if not or_actions:
                # Clause is empty -> Unsatisfiable
                self.conflict(deps=[action], eqs=[])
                return
            if self.true[step] & set(or_actions):
                # Clause already contains a True action
                return
            if len(or_actions) == 1:
                # If clause contains only one literal, it must be true
                if or_actions[0] not in self.true:
                    lit = self.encoder.up_actions_to_z3[or_actions[0]][step]
                    self.propagate(e=lit, ids=[action, action])
                return
            self.false[step].add(action)
            self.f_trail.append((step, action))
            self.update_pointers(or_actions[0], or_actions, or_actions[1], action)
            self.update_pointers(or_actions[1], or_actions, or_actions[0], action)

            false = [self.encoder.up_actions_to_z3[a][step] for a in or_actions if a in self.false[step]]

            if len(false) == len(or_actions):
                false.append(action)
                self.conflict(deps=false, eqs=[])
            else:
                false.append(action)
                false.append(action)
                true = [self.encoder.up_actions_to_z3[a][step] for a in or_actions if a not in self.false[step]]
                self.propagate(e=z3.Or(true), ids=false)
            return

        action_name, step = self.extract_key_step(action_str)
        if value:
            # Set to True so no longer need to track clauses associated with it
            self.watched_literals.pop(action, None)
            self.ensure_true_size(step)
            self.true[step].add(action_name)
            self.t_trail.append((step, action_name))
        else:
            # Remove any current pointers to clause
            self.watched_literals.pop(action, None)
            self.ensure_false_size(step)
            self.false[step].add(action_name)
            self.f_trail.append((step, action_name))
            if action_name in self.watched_literals:
                for l, p, c in self.watched_literals[action_name]:
                    self.move_pointer(step, action_name, l, p, c)

    def move_pointer(self, step, action, clause, pointer, change):
        if action not in self.false[step]:
            return
        start_index = clause.index(action)
        list_length = len(clause)
        # Start searching from the next position
        index = (start_index + 1) % list_length
        while index != start_index:
            # Find next unassigned literal
            if clause[index] not in self.false and clause[index] != pointer:
                # Update new pointer to the clause
                self.update_pointers(clause[index], clause, pointer, change)
                return
            index = (index + 1) % list_length
        # If no remaining literals to point to
        if change in self.false[step]:
            ids = [change, change]
            for n in clause:
                if n != pointer:
                    ids.append(self.encoder.up_actions_to_z3[n][step])
            self.propagate(e=self.encoder.up_actions_to_z3[pointer][step], ids=ids)

    def update_pointers(self, pointer, clause, other, change):
        if pointer in self.watched_literals:
            self.watched_literals[pointer].append((clause, other, change))
        else:
            self.watched_literals[pointer] = [(clause, other, change)]


    def extract_key_step(self, action_str):
        parts = action_str.split('_')
        step = int(parts[-1])
        key = '_'.join(parts[:-1])
        return key, step

    def ensure_false_size(self, step):
        while step >= len(self.false):
            self.false.append(set())

    def ensure_true_size(self, step):
        while step >= len(self.true):
            self.true.append(set())
