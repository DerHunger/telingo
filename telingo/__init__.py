"""
The telingo module contains functions to translate and solve temporal logic
programs.

Classes:
Solver      -- Solver class.
Application -- Main application class.

Functions:
imain -- Function to run the incremetal solving loop.
smain -- Function to run the incremetal solving loop scheduled.
main  -- Main function starting an extended clingo application.
"""

from . import transformers as _tf
from . import theory as _ty
from . import scheduler as _sd

import sys as _sys
import clingo as _clingo
import textwrap as _textwrap

from time import clock

class Solver:
    """
    Solver object containing the logic to ground and solve scheduled lengths.
    """

    def __init__(self, ctl, theory, restarts_per_solve, conflicts_per_restart, move_final, verbose):
        """
        Initializes the solver.

        Arguments:
        ctl                     -- Control object holding the program.
        theory                  -- telingo theory.
        restarts_per_solve      -- restarts per solve iteration.
        conflicts_per_restart   -- number of conflicts before restart.
        move_final              -- move final to current solving length, instead of maximum.
        verbose                 -- verbosity level.
        """
        self.__ctl         = ctl
        self.__length      = 0
        self.__last_length = 0
        self.__verbose     = verbose
        self.__result      = None
        self.__theory      = theory
        self.__time0       = clock()

        # set solving and restart policy
        self.__ctl.configuration.solve.solve_limit = "umax,"+str(restarts_per_solve)
        if int(conflicts_per_restart) != 0:
            self.__ctl.configuration.solver[0].restarts = "F,"+str(conflicts_per_restart)

        self.__move_final = move_final


    def __verbose_start(self):
        """
        Starts the verbose timer.
        """
        self.__time0 = clock()


    def __verbose_end(self, string):
        """
        Ends the verbose timer and prints the time with a given string.

        Arguments:
        string          -- Output prefix.
        """
        _sys.stdout.write(string+" Time:\t {:.2f}s\n".format(clock()-self.__time0))


    def solve(self, length, future_sigs, program_parts, on_model):
        """
        Grounds and solves the scheduler length.

        Arguments:
        length          -- length to ground and solve.
        program_parts   -- program parts to ground and solve.
        on_model        -- callback for intercepting models.
        """
        if self.__verbose: _sys.stdout.write("Grounded Until:\t {}\n".format(self.__length))
        # previous length < new length
        if self.__length < length:
            parts = []
            for t in range(self.__length+1, length+1):
                for root_name, part_name, rng in program_parts:
                    for i in rng:
                        if ((t - i >= 0 and root_name == "always") or
                            (t - i  > 0 and root_name == "dynamic") or
                            (t - i == 0 and root_name == "initial")):
                            parts.append((part_name, [t - i, t]))
            if length > 0:
                if not self.__move_final:
                    self.__ctl.release_external(_clingo.Function("__final", [self.__length]))
                    self.__ctl.cleanup()

            if self.__verbose:
                _sys.stdout.write("Grounding...\t "+str(parts)+"\n")
                self.__verbose_start()

            self.__ctl.ground(parts)
            if self.__verbose: self.__verbose_end("Grounding")

            self.__theory.translate(length, self.__ctl)
            if not self.__move_final:
                self.__ctl.assign_external(_clingo.Function("__final", [length]), True)

            self.__length = length


        # blocking or unblocking actions
        if length < self.__last_length:
            if self.__verbose: _sys.stdout.write("Blocking actions...\n")
            for t in range(length+1, self.__last_length+1):
                self.__ctl.assign_external(_clingo.Function("skip", [t]), True)
        elif self.__last_length < length:
            if self.__verbose: _sys.stdout.write("Unblocking actions...\n")
            for t in range(self.__last_length+1, length+1):
                self.__ctl.assign_external(_clingo.Function("skip", [t]), False)

        # solve
        if self.__verbose: self.__verbose_start()

        if self.__move_final:
            if length > 0:
                self.__ctl.assign_external(_clingo.Function("__final", [self.__last_length]), False)
            self.__ctl.assign_external(_clingo.Function("__final", [length]), True)

        assumptions = []
        for name, arity, positive in future_sigs:
            for atom in self.__ctl.symbolic_atoms.by_signature(name, arity, positive):
                if atom.symbol.arguments[-1].number > length:
                    assumptions.append(-atom.literal)

        self.__result = self.__ctl.solve(on_model=on_model, assumptions=assumptions)
        if self.__verbose:
            self.__verbose_end("Solving")
            _sys.stdout.write(str(self.__result)+"\n\n")
        self.__last_length = length

        # return
        return self.__result



def imain(prg, future_sigs, program_parts, on_model, imin = 0, imax = None, istop = "SAT"):
    """
    Take a program object and runs the incremental main solving loop.

    For each pair (name, arity) in future_sigs all atoms in the program base
    with the time parameter referring to the future are set to false. For
    example, given (p, 2) and atoms  p(x,1) in step 0, the atom would p(x,1)
    would be set to false via an assumption. In the following time steps, it
    would not be set to False.

    The list program_parts contains all program parts appearing in the program
    in form of triples (root, name, range) where root is either "initial" (time
    step 0), "always" (time steps >= 0), or "dynamic" (time steps > 0) and
    range is a list of integers for which the part has to be grounded
    backwards. Given range [0, 1] and root "always", at each iteration the
    program part would be grounded at horizon and horizon-1. The latter only if
    the horizon is greater than 0.

    Arguments:
    prg           -- Control object holding the program.
    future_sigs   -- Signatures of predicates whose future incarnations have to
                     be set to False.
    program_parts -- Program parts to ground.
    imin          -- Minimum number of iterations.
    imax          -- Maximum number of iterations.
    istop         -- When to stop.
    """
    f = _ty.Theory()
    step, ret = 0, None
    while ((imax is None or step < imax) and
           (step == 0 or step < imin or (
              (istop == "SAT"     and not ret.satisfiable) or
              (istop == "UNSAT"   and not ret.unsatisfiable) or
              (istop == "UNKNOWN" and not ret.unknown)))):
        parts = []
        for root_name, part_name, rng in program_parts:
            for i in rng:
                if ((step - i >= 0 and root_name == "always") or
                    (step - i  > 0 and root_name == "dynamic") or
                    (step - i == 0 and root_name == "initial")):
                    parts.append((part_name, [step - i, step]))
        if step > 0:
            prg.release_external(_clingo.Function("__final", [step-1]))
            prg.cleanup()

        prg.ground(parts)
        f.translate(step, prg)
        prg.assign_external(_clingo.Function("__final", [step]), True)
        assumptions = []
        for name, arity, positive in future_sigs:
            for atom in prg.symbolic_atoms.by_signature(name, arity, positive):
                if atom.symbol.arguments[-1].number > step:
                    assumptions.append(-atom.literal)
        ret, step = prg.solve(on_model=lambda m: on_model(m, step), assumptions=assumptions), step+1


def smain(prg, future_sigs, program_parts, on_model, imin=0, imax=None, istop="SAT", scheduler_options=_sd.Scheduler_Config()):
    """
    Take a program object and runs the incremental scheduled main solving loop.

    For each pair (name, arity) in future_sigs all atoms in the program base
    with the time parameter referring to the future are set to false. For
    example, given (p, 2) and atoms  p(x,1) in step 0, the atom would p(x,1)
    would be set to false via an assumption. In the following time steps, it
    would not be set to False.

    The list program_parts contains all program parts appearing in the program
    in form of triples (root, name, range) where root is either "initial" (time
    step 0), "always" (time steps >= 0), or "dynamic" (time steps > 0) and
    range is a list of integers for which the part has to be grounded
    backwards. Given range [0, 1] and root "always", at each iteration the
    program part would be grounded at horizon and horizon-1. The latter only if
    the horizon is greater than 0.

    Arguments:
    prg                 -- Control object holding the program.
    future_sigs         -- Signatures of predicates whose future incarnations have to
                        be set to False.
    program_parts       -- Program parts to ground.
    imin                -- Minimum number of iterations.
    imax                -- Maximum number of iterations.
    istop               -- When to stop.
    scheduler_options   -- options of the schedule to use.
    """
    theory = _ty.Theory()
    step, ret = 0, None

    # ground initial
    parts = []
    for root_name, part_name, rng in program_parts:
        for i in rng:
            if ((step - i >= 0 and root_name == "always") or
                (step - i  > 0 and root_name == "dynamic") or
                (step - i == 0 and root_name == "initial")):
                parts.append((part_name, [step - i, step]))
    prg.ground(parts)
    theory.translate(step, prg)
    prg.assign_external(_clingo.Function("__final", [step]), True)

    #solver
    solver = Solver(prg, theory, scheduler_options.restarts_per_solve, scheduler_options.conflicts_per_restart, scheduler_options.move_final, scheduler_options.verbose)

    #scheduler
    scheduler = scheduler_options.build_scheduler()

    # incremental scheduled main solving loop
    max_length = 0
    print_length = 0
    length = 0
    i = 1
    while ((imax is None or step < imax) and
           (step == 0 or step < imin or (
               (istop == "SAT"     and not ret.satisfiable) or
               (istop == "UNSAT"   and not ret.unsatisfiable) or
               (istop == "UNKNOWN" and not ret.unknown)))):
        if scheduler_options.verbose:
            _sys.stdout.write("Iteration "+str(i)+"\n")
            time0 = clock()
        i += 1
        # get current solve length from scheduler
        length = scheduler.next(ret)
        if length is None:
            _sys.stdout.write("PLAN NOT FOUND\n")
            break
        # solve given length
        if scheduler_options.move_final or length > print_length: print_length = length
        ret, step = solver.solve(length, future_sigs, program_parts, on_model=lambda m: on_model(m, print_length)), step+1
        if ret is not None and length > max_length: max_length = length
        if ret is not None and ret.satisfiable and step >= imin: break
        if scheduler_options.verbose: _sys.stdout.write("Iteration Time:\t {:.2f}s\n".format(clock()-time0)+"\n")

class Application:
    """
    Application object as accepted by clingo.clingo_main().

    Rewrites the incoming temporal logic programs into incremental ASP programs
    and solves them.
    """
    def __init__(self, name):
        """
        Initializes the application setting the program name.

        See clingo.clingo_main().
        """
        self.program_name = name
        self.version = "1.0.1"

        self.__imin = 0
        self.__imax = None
        self.__istop = "SAT"
        self.__horizon = 0
        self.__scheduler_config = _sd.Scheduler_Config()

    def __on_model(self, model, horizon):
        """
        Prints the atoms in a model grouped by state.

        Arguments:
        model -- The model to print.
        horizon -- The number of states.
        """
        self.__horizon = horizon

    def __parse_imin(self, value):
        """
        Parse imin argument.
        """
        self.__imin = int(value)
        return self.__imin >= 0

    def __parse_imax(self, value):
        """
        Parse imax argument.
        """
        if len(value) > 0:
            self.__imax = int(value)
            return self.__imax >= 0
        else:
            self.__imax = None
            return True

    def __parse_istop(self, value):
        """
        Parse istop argument.
        """
        self.__istop = value.upper()
        return self.__istop in ["SAT", "UNSAT", "UNKNOWN"]

    def __parse_scheduler_greater_equal(self, value, argument, minimum=0):
        """
        Parse argument with value greater than a minimum.
        """
        setattr(self.__scheduler_config, argument, int(value))
        return getattr(self.__scheduler_config, argument) >= minimum

    def __parse_scheduler_boolean(self, value, argument):
        """
        Parse argument with boolean value.
        """
        if value.upper() in ['TRUE', '1', 'T', 'Y', 'YES']:
            setattr(self.__scheduler_config, argument, True)
            return True
        elif value.upper() in ['FALSE', '0', 'F', 'N', 'NO']:
            setattr(self.__scheduler_config, argument, False)
            return True
        else:
            return False

    def __parse_scheduler(self, value):
        """
        Parse propagate-unsat argument.
        """
        # select scheduler
        arg = value.split(",")
        if arg[0] == 'A':
            if int(arg[1]) >= 0 and int(arg[1]) <= 50:
                self.__scheduler_config.A = int(arg[1])
            else: return False
        elif arg[0] == 'B':
            if float(arg[1]) >= 0.1 and float(arg[1]) <= 0.9999:
                self.__scheduler_config.B = float(arg[1])
            else: return False
        elif arg[0] == 'C':
            if float(arg[1]) >= 1.0 and float(arg[1]) <= 2.0:
                self.__scheduler_config.C = float(arg[1])
                self.__scheduler_config.inc = 1
            else: return False
        else:
            _sys.stdout.write("First scheduler parameter is wrong!\n")
            return False

        if len(arg) > 2 and (arg[0] == 'A' or arg[0] == 'B'):
            if int(arg[2]) > 0:
                self.__scheduler_config.inc = int(arg[2])
            else:
                return False

        if len(arg) > 3 and arg[0] == 'B':
            if int(arg[3]) >= 1:
                self.__scheduler_config.processes = int(arg[3])
            else:
                return False
        return True

    def print_model(self, model, printer):
        table = {}
        for sym in model.symbols(shown=True):
            if sym.type == _clingo.SymbolType.Function and len(sym.arguments) > 0:
                table.setdefault(sym.arguments[-1].number, []).append(_clingo.Function(sym.name, sym.arguments[:-1], sym.positive))
        for step in range(self.__horizon+1):
            symbols = table.get(step, [])
            _sys.stdout.write(" State {}:".format(step))
            sig = None
            for sym in sorted(symbols):
                if not sym.name.startswith('__'):
                    if (sym.name, len(sym.arguments), sym.positive) != sig:
                        _sys.stdout.write("\n ")
                        sig = (sym.name, len(sym.arguments), sym.positive)
                    _sys.stdout.write(" {}".format(sym))
            _sys.stdout.write("\n")
        return True

    def register_options(self, options):
        """
        See clingo.clingo_main().
        """
        group = "Telingo Options"
        options.add(group, "imin", "Minimum number of solving steps [0]", self.__parse_imin, argument="<n>")
        options.add(group, "imax", "Maximum number of solving steps []", self.__parse_imax, argument="<n>")
        options.add(group, "istop", _textwrap.dedent("""\
            Stop criterion [sat]
                  <arg>: {sat|unsat|unknown}"""), self.__parse_istop)

        # Scheduler algorithms
        group = "Scheduler Options"
        options.add(group, "scheduler", _textwrap.dedent("""\
            Configure scheduler settings
                  <sched>: <type {A,B,C}>,<n>[,<S {1..umax}>][,<M {1..umax}>]
                    A,<n>    : Run algorithm A with parameter <n>{1..50}
                    B,<n>    : Run algorithm B with parameter <n>{0.1..0.9999}
                    C,<n>    : Run algorithm C with parameter <n>{1.0..2.0}
                    ...,<S>  : Increase horizon lengths 0, <S>, 2<S>, 3<S>, ... [5] (A and B only)
                    ...,<M>  : Maximum number of processes [20] (B only)""")
        , self.__parse_scheduler, argument="<sched>")

        # Scheduler options
        options.add(group, "scheduler-start,F", "Starting horizon length [0]", lambda val: self.__parse_scheduler_greater_equal(val, "start"), argument="<n>")
        options.add(group, "scheduler-end,T", "Ending horizon length [3000]", lambda val: self.__parse_scheduler_greater_equal(val, "limit"), argument="<n>")
        options.add(group, "scheduler-verbose", "Set verbosity level to <n>", lambda val: self.__parse_scheduler_greater_equal(val, "verbose"), argument="<n>")
        options.add(group, "conflicts-per-restart,i", "Short for -r F,<n> (see restarts)", lambda val: self.__parse_scheduler_greater_equal(val, "conflicts_per_restart"), argument="<n>")
        options.add(group, "keep-after-unsat", "After finding n to be UNSAT, do keep runs with m<n [t]", lambda val: self.__parse_scheduler_boolean(val, "propagate_unsat"), argument="<b>")


        # Solving options
        options.add(group, "final-at-last", "Fix query always at the last (grounded) time point [t]", lambda val: self.__parse_scheduler_boolean(val, "move_final"), argument="<b>")
        options.add(group, "forbid-actions", _textwrap.dedent("""Forbid actions at time points after current plan length,
                                  using the predicate occurs/1 [f]""")
        , lambda val: self.__parse_scheduler_boolean(val, "forbid_actions"), argument="<b>")
        options.add(group, "force-actions", _textwrap.dedent("""Force at least one action at time points before current plan length,
                                  using the predicate occurs/1 [f]""")
        , lambda val: self.__parse_scheduler_boolean(val, "force_actions"), argument="<b>")

    def main(self, prg, files):
        """
        Implements the incremental solving loop.

        This function implements the Application.main() function as required by
        clingo.clingo_main().
        """
        is_scheduler = self.__scheduler_config.single_scheduler()
        with prg.builder() as b:
            files = [open(f) for f in files]
            if len(files) == 0:
                files.append(_sys.stdin)

            program = [f.read() for f in files]

            # additional programs for scheduler
            if is_scheduler:
                externals_program = """
                #program dynamic.  #external skip(t).
                """
                forbid_actions_program = """
                #program dynamic.
                :-     occurs(A),     skip(t). % no action
                """
                force_actions_program = """
                #program dynamic.
                :- not occurs(_), not skip(t). % some action
                """
                program.append(externals_program)
                if getattr(self.__scheduler_config, "forbid_actions", False):
                    program.append(forbid_actions_program)
                if getattr(self.__scheduler_config, "force_actions", False):
                    program.append(force_actions_program)

            future_sigs, program_parts = _tf.transform(program, b.add)

        if is_scheduler:
            smain(prg, future_sigs, program_parts, self.__on_model, self.__imin, self.__imax, self.__istop, self.__scheduler_config)
        else:
            imain(prg, future_sigs, program_parts, self.__on_model, self.__imin, self.__imax, self.__istop)


def main():
    """
    Run the telingo application.
    """
    _sys.exit(int(_clingo.clingo_main(Application("telingo"), _sys.argv[1:])))
