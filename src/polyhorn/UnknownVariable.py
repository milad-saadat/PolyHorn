class UnknownVariable:
    """this class is for unknown variable each unknown.

        Attributes:
            id (int): unique number assigned to each new generated variable
            name (str): the given name to each variable
            type (str): the type of the variable it can be referred as the reason why the variable is generated. for example is it a template variable or it is generated by farkas algorithm.
            number_of_variables (int): the number of generated variables to find new id for the recently generated variable

    """
    number_of_variables = 0

    @staticmethod
    def get_new_id() -> int:
        """ get new id for the newest variable

        :return: a number to assign to the latest created variable
        """
        UnknownVariable.number_of_variables += 1
        return UnknownVariable.number_of_variables

    def __init__(self, name: str = None, type_of_var: str = None):
        """
        Args:
            name (str): the given name to each variable
            type_of_var (str): the type of the variable it can be referred as the reason why the variable is generated.
            for example is it a template variable, or it is generated by farkas algorithm.

        """
        self.name = name
        self.type = type_of_var
        self.id = UnknownVariable.get_new_id()

    def __str__(self) -> str:
        """Convert variable to string by putting name and id together.
                """
        if self.type == 'template_var' or self.type == 'program_var':
            return self.name
        if self.name is not None:
            return self.name + f'_{self.id}'
        return str(f'var_{self.id}[{self.name}]')

    def __lt__(self, other) -> bool:
        """Compare variables based on their id.
                """
        return self.id < other.id

    def __eq__(self, other) -> bool:
        """Compare variables based on their id.
                        """
        return self.id == other.id

    def __hash__(self) -> int:
        """Hash variables based on their id.
                        """
        return hash(self.id)

    def convert_to_preorder(self) -> str:
        """Convert variables into preorder format of a fraction.
                        """
        return f'(/ {self.name}_num {self.name}_den)'