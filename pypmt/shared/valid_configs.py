from pypmt.encoders.R2E import EncoderRelaxed2Exists
from pypmt.encoders.basic import EncoderForall, EncoderSequential
from pypmt.encoders.OMT import EncoderSequentialOMT, EncoderParallelOMT
from pypmt.encoders.SequentialLifted import EncoderSequentialLifted
from pypmt.encoders.SequentialQFUF import EncoderSequentialQFUF

from pypmt.planner.SMT import SMTSearch
from pypmt.planner.lifted import LiftedSearch
from pypmt.planner.QFUF import QFUFSearch

# valid configs that the library is able to operate with
valid_configs = {
    "seq":     (EncoderSequential, SMTSearch),
    "forall":  (EncoderForall, SMTSearch),
    "r2e":     (EncoderRelaxed2Exists, SMTSearch),
    "omt":     (EncoderSequentialOMT, SMTSearch),       # TODO: has to be fixed
    "pomt":    (EncoderParallelOMT, SMTSearch),         # TODO: has to be fixed
    "uf":      (EncoderSequentialLifted, LiftedSearch), # TODO: has to be tested and too slow
    "qfuf":    (EncoderSequentialQFUF, QFUFSearch),
}