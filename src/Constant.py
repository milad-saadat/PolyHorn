
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
        'z3': 'solver/z3',
        'mathsat': 'solver/mathsat',
        'default': ''
    }

    command = {
        'z3': '',
        'mathsat': '',
        'default': ''
    }
