from typing import Callable, IO, Optional
import unified_planning as up

from pypmt.apis import valid_configs, generate_schedule_for

# We have to args: linear, upper_bound
class SMTPlanner(up.engines.Engine, up.engines.mixins.OneshotPlannerMixin):
    def __init__(self, **options):
        # Read known user-options and store them for using in the `solve` method
        up.engines.Engine.__init__(self)
        up.engines.mixins.OneshotPlannerMixin.__init__(self)

        # Get the planner configuration.
        self.configuration = options.get('configuration', None)
        if self.configuration is None:
            # This means that we need to check the validity of the configuration.
            self.encoder  = eval(options.get('encoder', 'None'))
            self.search_strategy = eval(options.get('search-strategy', 'None'))

            assert self.encoder is not None, "Encoder is not defined."
            assert self.search_strategy is not None, "Search strategy is not defined."

            # Check if this is a valid configuration.
            for (_encoder, _search) in valid_configs.values():
                if _encoder == self.encoder and _search == self.search_strategy:
                    self.configuration = (_encoder, _search)
                    break
        else:
            self.configuration = valid_configs[self.configuration]
        
        assert self.configuration is not None, "Invalid configuration pass."

        # Construct the shcedule.
        self.upper_bound = options.get('upper-bound', None)
        assert self.upper_bound is not None, "Upper bound is not defined."
        
        self.schedule = generate_schedule_for(self.configuration[0], self.upper_bound)
        self.run_validation = options.get('run-validation', False)

    @property
    def name(self) -> str:
        return "SMTPlanner"

    # TODO: We need to revist this.
    @staticmethod
    def supported_kind():
        # For this demo we limit ourselves to numeric planning.
        # Other kinds of problems can be modeled in the UP library,
        # see unified_planning.model.problem_kind.
        supported_kind = up.model.ProblemKind()
        supported_kind.set_problem_class("ACTION_BASED")
        supported_kind.set_problem_type("GENERAL_NUMERIC_PLANNING")
        supported_kind.set_typing('FLAT_TYPING')
        supported_kind.set_typing('HIERARCHICAL_TYPING')
        supported_kind.set_numbers('CONTINUOUS_NUMBERS')
        supported_kind.set_numbers('DISCRETE_NUMBERS')
        supported_kind.set_fluents_type('NUMERIC_FLUENTS')
        supported_kind.set_numbers('BOUNDED_TYPES')
        supported_kind.set_fluents_type('OBJECT_FLUENTS')
        supported_kind.set_conditions_kind('NEGATIVE_CONDITIONS')
        supported_kind.set_conditions_kind('DISJUNCTIVE_CONDITIONS')
        supported_kind.set_conditions_kind('EQUALITIES')
        supported_kind.set_conditions_kind('EXISTENTIAL_CONDITIONS')
        supported_kind.set_conditions_kind('UNIVERSAL_CONDITIONS')
        supported_kind.set_effects_kind('CONDITIONAL_EFFECTS')
        supported_kind.set_effects_kind('INCREASE_EFFECTS')
        supported_kind.set_effects_kind('DECREASE_EFFECTS')
        supported_kind.set_effects_kind('FLUENTS_IN_NUMERIC_ASSIGNMENTS')

        return supported_kind

    @staticmethod
    def supports(problem_kind):
        return problem_kind <= SMTPlanner.supported_kind()

    def _solve(self, problem: 'up.model.Problem',
              callback: Optional[Callable[['up.engines.PlanGenerationResult'], None]] = None,
              timeout: Optional[float] = None,
              output_stream: Optional[IO[str]] = None) -> 'up.engines.PlanGenerationResult':
        
        encoder_instance = self.configuration[0](problem)
        search_strategy  = self.configuration[1]
        plan = search_strategy(encoder_instance, self.schedule, run_validation=self.run_validation).search()
        
        if not plan.validate():
            return up.engines.PlanGenerationResult(up.engines.PlanGenerationResultStatus.UNSOLVABLE_INCOMPLETELY, None, self.name, log_messages=[f'failure reason {plan.validation_fail_reason}'])
        return up.engines.PlanGenerationResult(up.engines.PlanGenerationResultStatus.SOLVED_SATISFICING, plan.plan, self.name)

    def destroy(self):
        pass