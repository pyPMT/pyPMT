
from typing import Tuple, Union

VERSION: Tuple[Union[int, str], ...] = (1, 0, 0)
__version__ = ".".join(str(x) for x in VERSION)
