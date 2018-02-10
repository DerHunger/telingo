"""
TODO: document
"""

import clingo
import clingo.ast as ast

# Base for Formulas {{{1

def make_equal(backend, a, b):
    """
    Generates clauses for a <-> b.

    Arguments:
    backend -- Backend to add clauses to.
    a       -- first literal
    b       -- second literal
    """
    backend.add_rule([], [ a, -b])
    backend.add_rule([], [-a,  b])

def make_disjunction(backend, e, a, b):
    """
    Generates clauses for e <-> a | b.

    Arguments:
    backend -- Backend to add clauses to.
    e       -- equivalent literal
    a       -- first literal of disjunction
    b       -- second literal of disjunction
    """
    backend.add_rule([], [ e, -a, -b])
    backend.add_rule([], [-e, a])
    backend.add_rule([], [-e, b])

class StepData:
    def __init__(self):
        self.literal  = None
        self.literals = set()
        self.todo     = []
        self.done     = True

    def add_literal(self, backend):
        assert(self.literal is None)
        if len(self.literals) > 0:
            self.literal = min(self.literals)
            self.literals.remove(self.literal)
        else:
            self.literal = backend.add_atom()
            backend.add_rule([self.literal], [], True)
        return self.literal

class Context:
    def __init__(self, backend, symbols, add_todo, false_literal, horizon):
        self.add_todo        = add_todo
        self.backend         = backend
        self.symbols         = symbols
        self.horizon         = horizon
        self.__false_literal = false_literal

    @property
    def false_literal(self):
        return self.__false_literal(self.backend)

class Formula:
    def __init__(self, rep):
        self.__rep  = rep
        self.__data = {}

    @property
    def _rep(self):
        return self.__rep

    def translate(self, ctx, step):
        data = self.__data.setdefault(step, StepData())
        self.do_translate(ctx, step, data)
        if len(data.todo) > 0:
            for atom in data.todo:
                make_equal(ctx.backend, atom, data.literal)
            del data.todo[:]
        return data.literal

    def add_atom(self, atom, step):
        data = self.__data.setdefault(step, StepData())
        if atom not in data.literals:
            data.literals.add(atom)
            data.todo.append(atom)

# Boolean Formulas {{{1

class Atom(Formula):
    def __init__(self, name, arguments=[], positive=True):
        rep = "({}{}({}))".format("" if positive else "-", name, ",".join([str(a) for a in arguments]))
        if name.startswith("'"):
            raise RuntimeError("temporal formulas use < instead of leading primes: ".format(rep))
        if name.endswith("'"):
            raise RuntimeError("temporal formulas use > instead of trailing primes: ".format(rep))
        Formula.__init__(self, rep)
        self.__name      = name
        self.__arguments = arguments
        self.__positive  = positive

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            sym = clingo.Function(self.__name, self.__arguments + [step], self.__positive)
            sym_atom = ctx.symbols[sym]
            data.literal = sym_atom.literal if sym_atom is not None else ctx.false_literal

class BooleanConstant(Formula):
    def __init__(self, value):
        Formula.__init__(self, "(&true)" if value else "(&false)")
        self.__value = value

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            data.literal = -ctx.false_literal if self.__value else ctx.false_literal

class Negation(Formula):
    def __init__(self, arg):
        Formula.__init__(self, "(~{})".format(arg._rep))
        self.__arg = arg

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            data.literal = -self.__arg.translate(ctx, step)

class BooleanFormula(Formula):
    And = 0
    Or  = 1
    Eq  = 2
    Li  = 3
    Ri  = 4
    Ops = {
        And: "&",
        Or: "|",
        Eq: "<>",
        Li: "<-",
        Ri: "->"}

    def __init__(self, operator, lhs, rhs):
        rep = "({}{}{})".format(lhs._rep, BooleanFormula.Ops[operator], rhs._rep)
        Formula.__init__(self, rep)
        self.__operator = operator
        self.__lhs      = lhs
        self.__rhs      = rhs

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            lhs = self.__lhs.translate(ctx, step)
            rhs = self.__rhs.translate(ctx, step)
            lit = data.add_literal(ctx.backend)
            if self.__operator != BooleanFormula.Eq:
                if self.__operator == BooleanFormula.And:
                    lit, lhs, rhs = -lit, -lhs, -rhs
                elif self.__operator == BooleanFormula.Li:
                    rhs = -rhs
                elif self.__operator == BooleanFormula.Ri:
                    lhs = -lhs
                make_disjunction(ctx.backend, lit, lhs, rhs)
            elif self.__operator == BooleanFormula.Eq:
                ctx.backend.add_rule([], [ lit,  rhs,  lhs])
                ctx.backend.add_rule([], [ lit, -rhs, -lhs])
                ctx.backend.add_rule([], [-lit,  rhs, -lhs])
                ctx.backend.add_rule([], [-lit, -rhs,  lhs])

_binary_operators = {
    "&": BooleanFormula.And,
    "|": BooleanFormula.Or,
    "<>": BooleanFormula.Eq,
    "<-": BooleanFormula.Li,
    "->": BooleanFormula.Ri}

_unary_operators = {"~"}

# Temporal Formulas {{{1

class Previous(Formula):
    def __init__(self, arg, weak):
        Formula.__init__(self, "(<{})".format(arg._rep))
        self.__arg  = arg
        self.__weak = weak

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            if step > 0:
                data.literal = self.__arg.translate(ctx, step-1)
            else:
                data.literal = ctx.false_literal
                if self.__weak and step == 0:
                    data.literal = -data.literal

class Initially(Formula):
    def __init__(self, arg):
        Formula.__init__(self, "(<<{})".format(arg._rep))
        self.__arg  = arg

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            data.literal = self.__arg.translate(ctx, 0)

class Next(Formula):
    def __init__(self, arg, weak):
        Formula.__init__(self, "(>{})".format(arg._rep))
        self.__arg  = arg
        self.__weak = weak

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            if step < ctx.horizon:
                data.literal = self.__arg.translate(ctx, step+1)
                data.done = True
            else:
                data.literal = ctx.backend.add_atom()
                ctx.backend.add_external(data.literal, clingo.TruthValue._True if self.__weak else clingo.TruthValue._False)
                ctx.add_todo(self._rep, self, step)
                data.done = False
        elif not data.done:
            assert(step in range(0, ctx.horizon + 1))
            if step < ctx.horizon:
                arg = self.__arg.translate(ctx, step+1)
                make_equal(ctx.backend, data.literal, arg)
                ctx.backend.add_external(data.literal, clingo.TruthValue.Free)
                data.done = True

class TelFormula(Formula):
    Since   = 0
    Trigger = 1

    def __init__(self, rep, op, lhs, rhs):
        Formula.__init__(self, rep)
        self._op  = op
        self._lhs = lhs
        self._rhs = rhs

    def _translate(self, ctx, step, data, pre):
        lhs = None if self._lhs is None else self._lhs.translate(ctx, step)
        rhs = self._rhs.translate(ctx, step)
        lit = data.add_literal(ctx.backend)
        if self._op == TelFormulaP.Trigger:
            lit, rhs, pre = -lit, -rhs, -pre
            if lhs is not None:
                lhs = -lhs
        ctx.backend.add_rule([], [-lit, rhs])
        ctx.backend.add_rule([], [-rhs, -pre, lit])
        if lhs is not None:
            ctx.backend.add_rule([], [-lit,  lhs, pre])
            ctx.backend.add_rule([], [-rhs, -lhs, lit])
        else:
            ctx.backend.add_rule([], [-lit, pre])


class TelFormulaP(TelFormula):
    def __init__(self, op, lhs, rhs):
        rep = "({}{}{})".format("" if lhs is None else lhs._rep, "<?" if op == TelFormula.Since else "<*", rhs._rep)
        TelFormula.__init__(self, rep, op, lhs, rhs)

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            if step == 0:
                data.literal = self._rhs.translate(ctx, step)
            else:
                pre = self.translate(ctx, step - 1)
                self._translate(ctx, step, data, pre)

class TelFormulaN(TelFormula):
    def __init__(self, op, lhs, rhs):
        rep = "({}{}{})".format("" if lhs is None else lhs._rep, ">?" if op == TelFormula.Since else ">*", rhs._rep)
        TelFormula.__init__(self, rep, op, lhs, rhs)
        self.__future = None

    def set_future(self, future):
        self.__future = future

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            fut = self.__future.translate(ctx, step)
            self._translate(ctx, step, data, fut)

_tel_operators = {"<", ">", "<:", ">:", "<*", ">*", ">?", "<?", ">>", "<<"}

# Theory of Formulas {{{1

def create_symbol(rep):
    if rep.type == clingo.TheoryTermType.Number:
        return clingo.Number(rep.number)
    elif rep.type in [clingo.TheoryTermType.List, clingo.TheoryTermType.Set]:
        raise RuntimeError("invalid symbol: {}".format(rep))
    else:
        name = "" if rep.type == clingo.TheoryTermType.Tuple else rep.name
        if name in _binary_operators or name in _unary_operators or name in _tel_operators:
            raise RuntimeError("invalid symbol: {}".format(rep))
        args = [] if rep.type == clingo.TheoryTermType.Symbol else rep.arguments
        if len(args) == 0:
            if name == "#inf":
                return clingo.Infimum
            elif name == "#sup":
                return clingo.Supremum
            elif len(name) > 1 and name.startswith('"') and name.endswith('"'):
                return clingo.String(name[1:-1])
        return clingo.Function(name, [create_symbol(arg) for arg in args])

def create_atom(rep, theory, positive):
    if rep.type == clingo.TheoryTermType.Symbol:
        return theory.add_formula(Atom(rep.name, [], positive))
    elif rep.type == clingo.TheoryTermType.Function:
        if rep.name == "-":
            return create_atom(rep.arguments[0], theory, not positive)
        elif rep.name not in _binary_operators and rep.name not in _unary_operators and rep.name not in _tel_operators:
            return theory.add_formula(Atom(rep.name, [create_symbol(arg) for arg in rep.arguments], positive))
    raise RuntimeError("invalid atom: ".format(rep))

def create_formula(rep, theory):
    if rep.type == clingo.TheoryTermType.Symbol:
        return create_atom(rep, theory, True)
    elif rep.type == clingo.TheoryTermType.Function:
        args = rep.arguments
        if rep.name in _binary_operators and len(args) == 2:
            lhs = create_formula(args[0], theory)
            rhs = create_formula(args[1], theory)
            return theory.add_formula(BooleanFormula(_binary_operators[rep.name], lhs, rhs))
        elif rep.name in _unary_operators and len(args) == 1:
            arg = create_formula(args[0], theory)
            return theory.add_formula(Negation(arg))
        elif rep.name in _tel_operators:
            lhs = None if len(args) == 1 else create_formula(args[0], theory)
            rhs = create_formula(args[-1], theory)
            if rep.name == "<" or rep.name == "<:":
                return theory.add_formula(Previous(rhs, rep.name == "<:"))
            elif rep.name == "<*":
                return theory.add_formula(TelFormulaP(TelFormula.Trigger, lhs, rhs))
            elif rep.name == "<?":
                return theory.add_formula(TelFormulaP(TelFormula.Since, lhs, rhs))
            elif rep.name == "<<":
                return theory.add_formula(Initially(rhs))
            elif rep.name == ">" or rep.name == ">:":
                return theory.add_formula(Next(rhs, rep.name == ">:"))
            elif rep.name == ">*":
                formula = theory.add_formula(TelFormulaN(TelFormula.Trigger, lhs, rhs))
                formula.set_future(theory.add_formula(Next(formula, True)))
                return formula
            elif rep.name == ">?":
                formula = theory.add_formula(TelFormulaN(TelFormula.Since, lhs, rhs))
                formula.set_future(theory.add_formula(Next(formula, False)))
                return formula
            else:
                assert(rep.name == ">>")
                rhs = theory.add_formula(BooleanFormula(BooleanFormula.Or, theory.add_formula(Negation(theory.add_formula(Atom("__final", [], True)))), rhs))
                formula = theory.add_formula(TelFormulaN(TelFormula.Trigger, None, rhs))
                formula.set_future(theory.add_formula(Next(formula, True)))
                return formula
        elif rep.name == "&":
            arg = rep.arguments[0]
            if arg.type == clingo.TheoryTermType.Symbol:
                if arg.name == "initial" or arg.name == "final":
                    name = "__{}".format(arg.name)
                    return theory.add_formula(Atom(name, [], True))
                elif arg.name == "true" or arg.name == "false":
                    return theory.add_formula(BooleanConstant(arg.name == "true"))
                else:
                    raise RuntimeError("unknown identifier: ".format(rep))
            else:
                raise RuntimeError("invalid temporal formula: ".format(rep))
        else:
            return create_atom(rep, theory, True)
    else:
        raise RuntimeError("invalid temporal formula: ".format(rep))

class Theory:
    def __init__(self):
        self.__formulas = {}
        self.__todo_keys = set()
        self.__todo = []
        self.__false_literal = None

    def add_formula(self, formula):
        formula = self.__formulas.setdefault(formula._rep, formula)
        return formula

    def add_todo(self, key, formula, step):
        key = (step, key)
        if key not in self.__todo_keys:
            self.__todo_keys.add(key)
            self.__todo.append((step, formula))

    def false_literal(self, backend):
        if self.__false_literal is None:
            self.__false_literal = backend.add_atom()
        return self.__false_literal

    def translate(self, horizon, prg):
        for atom in prg.theory_atoms:
            if atom.term.name == "tel" and len(atom.term.arguments) == 1:
                step    = atom.term.arguments[0].number
                rep     = atom.elements[0].terms[0]
                formula = create_formula(rep, self)
                formula.add_atom(atom.literal, step)
                self.add_todo(str(rep), formula, step)

        if len(self.__todo) > 0:
            todo, self.__todo, self.__todo_keys = self.__todo, [], set()
            with prg.backend() as b:
                ctx = Context(b, prg.symbolic_atoms, self.add_todo, self.false_literal, horizon)
                for step, formula in todo:
                    formula.translate(ctx, step)
