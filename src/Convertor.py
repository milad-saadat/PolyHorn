from .Polynomial import Polynomial
from lark import Lark
import lark
from .UnknownVariable import UnknownVariable
from .Solver import Solver
from .Polynomial import Monomial


def find_index_of_variable(name: str, all_variable: [UnknownVariable]) -> int:
    """ returns the index of a variable in a list.

    :param name: name of the variable that should be find.
    :param all_variable: list of all variables.
    :return: index of the variable.
    """
    all_variable.sort()
    for i in range(len(all_variable)):
        if name == all_variable[i].name:
            return i
    print(f'no such var declared with name : {name}')
    return -1


def traverse(parse_tree, all_variables: [UnknownVariable]) -> Polynomial:
    """ This function traverse the parse tree generated by lark and return a polynomial.

    :param parse_tree: a node in parse tree.(starting from root)
    :param all_variables: list of variables in the polynomial.
    :return: Polynomial that the parse tree represents.
    """
    if parse_tree.data == 'start':
        return traverse(parse_tree.children[0], all_variables)
    elif parse_tree.data == 'expression':
        if len(parse_tree.children) == 1:
            return traverse(parse_tree.children[0], all_variables)
        elif parse_tree.children[1] == '+':
            return traverse(parse_tree.children[0], all_variables) + traverse(parse_tree.children[2], all_variables)
        elif parse_tree.children[1] == '-':
            return traverse(parse_tree.children[0], all_variables) - traverse(parse_tree.children[2], all_variables)

    elif parse_tree.data == 'term':
        if len(parse_tree.children) == 1:
            return traverse(parse_tree.children[0], all_variables)
        else:
            return traverse(parse_tree.children[0], all_variables) * traverse(parse_tree.children[1], all_variables)

    elif parse_tree.data == 'factor':
        if len(parse_tree.children) == 1:
            return traverse(parse_tree.children[0], all_variables)
        elif parse_tree.children[0] == '-':
            return -traverse(parse_tree.children[1], all_variables)
        elif parse_tree.children[0] == '+':
            return traverse(parse_tree.children[1], all_variables)

    elif parse_tree.data == 'primary':
        if not parse_tree.children[0].__class__ is lark.Token:
            return traverse(parse_tree.children[0], all_variables)
        elif parse_tree.children[0].type == 'RATIONALNUMBER':
            return Solver.get_constant_polynomial(all_variables, str(parse_tree.children[0]))
        else:
            deg = 1
            if len(parse_tree.children) > 1:
                deg = int(parse_tree.children[1])
            degrees = [0] * len(all_variables)
            degrees[find_index_of_variable(str(parse_tree.children[0]), all_variables)] = deg
            return Solver.get_degree_polynomial(all_variables, degrees)


def convert_to_desired_poly(poly: Polynomial, program_variables: [UnknownVariable]) -> Polynomial:
    """ This function separates program variables from template variables and put template variables in Coefficient.

    :param poly: input Polynomial.
    :param program_variables: list of program variables in polynomial.
    :return: new Polynomial with separated program variables from template variables.
    """
    monomials = []
    for monomial in poly.monomials:
        coef = monomial.coefficient
        degrees = [0] * len(program_variables)
        for i, var in enumerate(monomial.variables):
            if var in program_variables:
                degrees[find_index_of_variable(var.name, program_variables)] = monomial.degrees[i]
            else:
                for _ in range(monomial.degrees[i]):
                    coef.elements[0].variables.append(var)
        monomials.append(Monomial(program_variables, degrees, coef))
    return Polynomial(program_variables, monomials).revise()


def convert_general_string_to_poly(poly_text: str, all_variables: [UnknownVariable],
                                   program_variables: [UnknownVariable]) -> Polynomial:
    """ This function convert a string to Polynomial.\n It uses Lark to parse the string.

    :param poly_text: text that should be converted to the Polynomial.
    :param all_variables: list of all variables in the text.
    :param program_variables: list of program variables.
    :return: polynomial that the input string represents.
    """
    parser = Lark(r"""
            start : expression

            expression : term | expression SIGN term 

            term : factor | term "*" factor

            factor : primary | SIGN factor

            primary : VAR | RATIONALNUMBER | VAR "^" RATIONALNUMBER  | "(" expression ")"
            
            SIGN : "+" | "-" 
            VAR: /\w/+
            RATIONALNUMBER : /[+-]?/ NUMBER ("/" NUMBER)?


            %import common.NUMBER
            %import common.NEWLINE -> _NL
            %import common.WS_INLINE
            %ignore WS_INLINE
        """, parser="lalr")

    parse_tree = parser.parse(poly_text)
    return convert_to_desired_poly(traverse(parse_tree, all_variables), program_variables)
