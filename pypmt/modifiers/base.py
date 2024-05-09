
class Modifier:
    """
    Modifier class.
    """
    def __init__(self, name):
        self.name = name
        #self.use_serial_mutexes = use_serial_mutexes
        self.mutexes = []

    def encode(self, encoder, variables):
        raise NotImplementedError('Modifier.encode() not implemented.')
