# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """

    if is_variable(formula.root):
        return Formula(formula.root)
    
    if formula.root == 'T':
        p = Formula('p')
        return Formula('|', p, Formula('~', p))
    
    if formula.root == 'F':
        p = Formula('p')
        return Formula('&', p, Formula('~', p))
    
    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))
    
    if formula.root in {'&', '|'}:
        return Formula(formula.root, to_not_and_or(formula.first), to_not_and_or(formula.second))
    
    if formula.root == '->':
        return Formula('|', Formula('~', to_not_and_or(formula.first)), to_not_and_or(formula.second))
    
    if formula.root == '+':
        p = to_not_and_or(formula.first)
        q = to_not_and_or(formula.second)
        return Formula('&', Formula('|', p, q), Formula('~', Formula('&', p, q)))
    
    if formula.root == '<->':
        p = to_not_and_or(formula.first)
        q = to_not_and_or(formula.second)
        return Formula('&', Formula('|', Formula('~', p), q), Formula('|', Formula('~', q), p))
    
    if formula.root == '-&':
        return Formula('~', Formula('&', to_not_and_or(formula.first), to_not_and_or(formula.second)))
    
    if formula.root == '-|':
        return Formula('~', Formula('|', to_not_and_or(formula.first), to_not_and_or(formula.second)))

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    f = to_not_and_or(formula)

    def func(f):
        if is_variable(f.root):
            return f
        if f.root == '~':
            return Formula('~', func(f.first))
        if f.root == '&':
            return Formula('&', func(f.first), func(f.second))
        if f.root == '|':
            p = func(f.first)
            q = func(f.second)
            return Formula('~', Formula('&', Formula('~', p), Formula('~', q)))
        raise ValueError(f"Unexpected operator: {f.root}")
    
    return func(f)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    f = to_not_and(formula)
    
    def func(f):
        if is_variable(f.root):
            return f
        if f.root == '~':
            p = func(f.first)
            return Formula('-&', p, p)
        if f.root == '&':
            p = func(f.first)
            q = func(f.second)
            nand_pq = Formula('-&', p, q)
            return Formula('-&', nand_pq, nand_pq)
    
    return func(f)


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    f = to_not_and_or(formula)
    
    def func(f):
        if is_variable(f.root):
            return f
        if f.root == '~':
            return Formula('~', func(f.first))
        if f.root == '&':
            p = func(f.first)
            q = func(f.second)
            return Formula('~', Formula('->', p, Formula('~', q)))
        if f.root == '|':
            p = func(f.first)
            q = func(f.second)
            return Formula('->', Formula('~', p), q) 
        
    return func(f)


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    f = to_implies_not(formula)
    
    def func(f):
        if is_variable(f.root):
            return f
        if f.root == 'F':
            return Formula('F')
        if f.root == '~':
            p = func(f.first)
            return Formula('->', p, Formula('F'))
        if f.root == '->':
            return Formula('->',func(f.first), func(f.second))
        
    return func(f)