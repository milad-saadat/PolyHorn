import os

ABS_PATH = os.path.dirname(os.path.abspath(__file__))

class Theorem:
    Farkas = 'farkas'
    Handelman = 'handelman'
    Putinar = 'putinar'


class Constant:
    """This class consist of some constant dictionaries which are used for configuration of the solvers.

    """
    options = {
        'z3': '(set-option :print-success false)\n' + \
              '(set-option :produce-models true)\n'
        ,
        'mathsat': '(set-option :print-success false)\n' + \
                   '(set-option :produce-models true)\n'
        ,
        'default': ''

    }

    default_path = {
        'z3': os.path.join(ABS_PATH, '..', 'solver', 'z3'),
        'mathsat': os.path.join(ABS_PATH, '..', 'solver', 'mathsat'),
        'default': ''
    }

    command = {
        'z3': '',
        'mathsat': '',
        'default': ''
    }
