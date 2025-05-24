from __future__ import annotations

import logging
from itertools import product

from anytree import NodeMixin, PostOrderIter
from prettytable import PLAIN_COLUMNS, PrettyTable

from mathesis import forms

_logger = logging.getLogger(__name__)
_logger.addHandler(logging.NullHandler())


class ConnectiveClause:
    column_names: list[str]
    table: dict
    truth_value_symbols: None

    def __init__(self, truth_value_symbols=None) -> None:
        self.truth_value_symbols = truth_value_symbols

    def __str__(self):
        return self.to_string()

    def apply(self, *values):
        if None in values:
            return None
        return self.table[values]

    def to_table(self):
        table = PrettyTable()
        table.align = "c"
        table.format = True

        places = len(list(self.table.keys())[0])

        table.field_names = self.column_names

        for values_from, value_to in self.table.items():
            if self.truth_value_symbols:
                values_from = tuple(
                    self.truth_value_symbols.get(v, v) for v in values_from
                )
                value_to = self.truth_value_symbols.get(value_to, value_to)
            table.add_row(values_from + (value_to,))

        return table

    def to_string(self, style=PLAIN_COLUMNS):
        table = self.to_table()
        table.set_style(style)
        return str(table)

    def _repr_html_(self):
        table = self.to_table()
        return table.get_html_string(format=False)


class AssignedNodeBase:
    pass


class AssignedNode(AssignedNodeBase, NodeMixin):
    def __init__(self, name, fml, parent=None, children=[]):
        self.name = name
        self.fml = fml
        self.parent = parent
        self.children = children
        self._truth_value = None

    @property
    def truth_value(self):
        # NOTE: Make sure to specify `is not None`: _truth_value can be 0 and accidentally return False
        if self._truth_value is not None:
            return self._truth_value
        else:
            raise Exception("Truth value not assigned")

    @truth_value.setter
    def truth_value(self, value):
        self._truth_value = value

    def assign_atom_values(self, atom_assignments):
        if isinstance(self.fml, forms.Atom):
            self._truth_value = atom_assignments.get(str(self.fml), None)
        else:
            for child in self.children:
                child.assign_atom_values(atom_assignments)

    def __repr__(self):
        return f"{repr(self.fml)} = {self.truth_value}"

    def __str__(self):
        return f"{str(self.fml)} = {self.truth_value}"


class TruthTable:
    """Base class for truth tables.

    Args:
        formula_or_formulas: A single formula or a list of formulas.
        conclusions: A list of formulas.
    """

    truth_values: set = set()
    designated_values: set = set()
    clauses = {}

    def __init__(
        self,
        formula_or_formulas: list[forms.Formula] | forms.Formula,
        conclusions: list[forms.Formula] = [],  # TODO: Distinction between [] and None
    ):
        if isinstance(formula_or_formulas, list):
            # raise NotImplementedError()
            self.premises = formula_or_formulas
        else:
            self.premises = [formula_or_formulas]

        self.conclusions = conclusions

    def __str__(self):
        return self.to_string()

    @property
    def atom_columns(self):
        atom_symbols = self.atom_symbols
        return atom_symbols

    @property
    def atom_symbols(self):
        atom_symbols = set()
        # Extract all atomic symbols in the formulas
        for fml in self.premises + self.conclusions:
            atom_symbols.update(fml.atoms.keys())
        atom_symbols = sorted(tuple(atom_symbols))
        return atom_symbols

    def assignments(self):
        """Generate all possible truth assignments for the atomic symbols in the formulas."""

        atom_symbols = self.atom_symbols

        assignments = []
        for tv in product(self.truth_values, repeat=len(atom_symbols)):
            assignment = dict(zip(atom_symbols, tv))
            assignments.append(assignment)

        return assignments

    @property
    def columns(self):
        atom_columns = [self.atom_columns]
        nonatom_columns = []

        for fml in self.premises + self.conclusions:
            tree = self._wrap_fml(fml)
            fml_columns = []

            for node in PostOrderIter(tree):
                if str(node.fml) not in map(str, fml_columns):
                    if isinstance(node.fml, forms.Atom):
                        pass
                    else:
                        fml_columns.append(node.fml)

            nonatom_columns.append(fml_columns)

        columns = atom_columns + nonatom_columns

        # TODO: Allow flexible stringification
        return [tuple(map(str, column)) for column in columns]

    @property
    def rows(self):
        rows = []

        for assignment in self.assignments():
            row = []
            atom_tvs = [value for value in assignment.values()]
            atom_segment = []
            for value in atom_tvs:
                if hasattr(self, "truth_value_symbols"):
                    atom_segment.append(
                        getattr(self, "truth_value_symbols").get(value, value)
                    )
                else:
                    atom_segment.append(value)

            row.append(tuple(atom_segment))

            for fml in self.premises + self.conclusions:
                tree = self._wrap_fml(fml)
                tree.assign_atom_values(assignment)
                atom_value_pairs = []
                nonatom_value_pairs = []
                field_names = []

                for node in PostOrderIter(tree):
                    self.compute_truth_value(node)
                    # print(str(node.fml), node.truth_value)
                    if str(node.fml) not in field_names:
                        field_names.append(str(node.fml))
                        if hasattr(self, "truth_value_symbols"):
                            truth_value = getattr(self, "truth_value_symbols").get(
                                node.truth_value, node.truth_value
                            )
                        else:
                            truth_value = node.truth_value
                        if isinstance(node.fml, forms.Atom):
                            atom_value_pairs.append((node.fml, truth_value))
                        else:
                            nonatom_value_pairs.append((node.fml, truth_value))
                        # row.append(truth_value)

                # print(atom_value_pairs, nonatom_value_pairs)
                # field_names = [str(fml) for fml, value in atom_value_pairs + nonatom_value_pairs]
                row_segment = tuple(value for fml, value in nonatom_value_pairs)
                row.append(row_segment)

            rows.append(row)

        return rows

        # formula_row_segments.append(nonatom_value_pairs)

    def compute_truth_value(self, assigned_node):
        if isinstance(assigned_node.fml, forms.Top):
            assigned_node.truth_value = 1
        elif isinstance(assigned_node.fml, forms.Bottom):
            assigned_node.truth_value = 0
        elif isinstance(assigned_node.fml, forms.Atom):
            # assigned_node.truth_value = assigned_node._truth_value
            pass
        elif isinstance(assigned_node.fml, forms.Negation):
            if forms.Negation not in self.clauses:
                raise NotImplementedError("Negation clause not implemented")
            assigned_node.truth_value = self.clauses[forms.Negation].apply(
                assigned_node.children[0].truth_value
            )
        elif isinstance(assigned_node.fml, forms.Conjunction):
            if forms.Conjunction not in self.clauses:
                raise NotImplementedError("Conjunction clause not implemented")
            assigned_node.truth_value = self.clauses[forms.Conjunction].apply(
                *tuple(child.truth_value for child in assigned_node.children)
            )
        elif isinstance(assigned_node.fml, forms.Disjunction):
            if forms.Disjunction not in self.clauses:
                raise NotImplementedError("Disjunction clause not implemented")
            assigned_node.truth_value = self.clauses[forms.Disjunction].apply(
                *tuple(child.truth_value for child in assigned_node.children)
            )
        elif isinstance(assigned_node.fml, forms.Conditional):
            if forms.Conditional not in self.clauses:
                raise NotImplementedError("Conditional clause not implemented")
            assigned_node.truth_value = self.clauses[forms.Conditional].apply(
                *tuple(child.truth_value for child in assigned_node.children)
            )
        else:
            raise NotImplementedError(
                f"Clause for {type(assigned_node.fml)} not implemented"
            )

    def _wrap_fml(self, fml):
        def transformer(fml):
            node = AssignedNode(str(fml), fml=fml)
            if isinstance(fml, forms.Binary):
                node.children = [transformer(subfml) for subfml in fml.subs]
            elif isinstance(fml, forms.Unary):
                node.children = [transformer(fml.sub)]
            # NOTE: No truth table for quantifiers
            # elif isinstance(fml, forms.Quantifier):
            #     node.children = [transformer(fml.sub)]
            return node

        wrapped_fml = fml.transform(transformer)
        return wrapped_fml

    def is_valid(self):
        atom_symbols = set()
        # Extract all atomic symbols in the formulas
        for fml in self.premises + self.conclusions:
            atom_symbols.update(fml.atoms.keys())
        atom_symbols = sorted(list(atom_symbols))

        premise_values = []
        conclusion_values = []

        for tv in product(self.truth_values, repeat=len(atom_symbols)):
            for fml in self.premises:
                assignments = dict(zip(atom_symbols, tv))
                tv_fml = self._wrap_fml(fml)
                tv_fml.assign_atom_values(assignments)
                for node in PostOrderIter(tv_fml):
                    self.compute_truth_value(node)
                premise_values.append(tv_fml.truth_value)

            for fml in self.conclusions:
                assignments = dict(zip(atom_symbols, tv))
                tv_fml = self._wrap_fml(fml)
                tv_fml.assign_atom_values(assignments)
                for node in PostOrderIter(tv_fml):
                    self.compute_truth_value(node)
                conclusion_values.append(tv_fml.truth_value)

        # print(premise_values)

        if not self.conclusions:
            if all([value in self.designated_values for value in premise_values]):
                return True
            else:
                return False
        else:
            # TODO: Implement for inference validity
            raise NotImplementedError()

    # def is_valid(self):
    #     for fml in self.premises + self.conclusions:
    #         atom_symbols = fml.atoms.keys()
    #         atom_symbols = sorted(atom_symbols)
    #         values = []
    #         for tv in product(self.truth_values, repeat=len(atom_symbols)):
    #             assignments = dict(zip(atom_symbols, tv))
    #             tv_fml = self._wrap_fml(fml)
    #             tv_fml.assign_atom_values(assignments)
    #             for node in PostOrderIter(tv_fml):
    #                 self.compute_truth_value(node)
    #             values.append(tv_fml.truth_value)
    #         if all([value in self.designated_values for value in values]):
    #             return True
    #         else:
    #             return False

    def counterexample(self):
        pass

    def to_table(self):
        table = PrettyTable()
        table.align = "c"
        table.format = True

        for assignment in self.assignments():
            formula_row_segments = []
            for fml in self.premises + self.conclusions:
                tree = self._wrap_fml(fml)
                # print(RenderTree(tree))
                tree.assign_atom_values(assignment)
                # print(tree.truth_value)
                # print(RenderTree(tree))
                atom_value_pairs = []
                nonatom_value_pairs = []
                field_names = []
                row = []

                for node in PostOrderIter(tree):
                    self.compute_truth_value(node)
                    # print(str(node.fml), node.truth_value)
                    if str(node.fml) not in field_names:
                        field_names.append(str(node.fml))
                        if hasattr(self, "truth_value_symbols"):
                            truth_value = getattr(self, "truth_value_symbols").get(
                                node.truth_value, node.truth_value
                            )
                        else:
                            truth_value = node.truth_value
                        if isinstance(node.fml, forms.Atom):
                            atom_value_pairs.append((node.fml, truth_value))
                        else:
                            nonatom_value_pairs.append((node.fml, truth_value))
                        # row.append(truth_value)

                # print(atom_value_pairs, nonatom_value_pairs)
                field_names = [str(fml) for fml, value in nonatom_value_pairs]
                row = [value for fml, value in nonatom_value_pairs]
                # print(field_names, row)

                formula_row_segments.append(nonatom_value_pairs)

            # print(assignment)
            # print(formula_row_segments)

            field_names = []
            row = []

            for atom, value in assignment.items():
                truth_value = getattr(self, "truth_value_symbols", {}).get(value, value)
                field_names.append(str(atom))
                row.append(truth_value)

            i = 0
            for nonatom_value_pairs in formula_row_segments:
                # TODO: Fix hacky way to satisfy PrettyTable's unique field_names requirement
                field_names += [
                    str(fml) + " " * i for fml, value in nonatom_value_pairs
                ]
                row += [value for fml, value in nonatom_value_pairs]
                i += 1

            if not table.field_names:
                # Create field_names from fml of each nonatom_value_pairs of formula_row_segments
                table.field_names = field_names

            table.add_row(row)

        return table

    def to_string(self, style=PLAIN_COLUMNS):
        table = self.to_table()
        table.set_style(style)
        return str(table)

    def _repr_html_(self):
        table = self.to_table()
        return table.get_html_string(format=False)
