"""
The telingo module contains functions to translate and solve temporal logic
programs.

Classes:
Scheduler   -- Scheduler interface.
A_Scheduler -- Scheduler class for algorithm A.
B_Scheduler -- Scheduler class for algorithm B.
C_Scheduler -- Scheduler class for algorithm C.
Solver      -- Solver class.
Application -- Main application class.

Functions:
imain -- Function to run the incremetal solving loop.
smain -- Function to run the incremetal solving loop scheduled.
main  -- Main function starting an extended clingo application.
"""

from . import transformers as _tf
from . import theory as _ty

import sys as _sys
import clingo as _clingo
import textwrap as _textwrap

from time import clock

class Scheduler:
    """
    Scheduler object contains the minimum functions for a scheduler.
    """

    def __init__(self):
        """
        Initializes the scheduler object.
        """
        pass


    def next(self,result):
        """
        returns the next length to solve of the schedule.
        """
        return 0


class A_Scheduler(Scheduler):
    """
    A_scheduler object contains the algorithm A to schedule solve steps.

    Algorithm A uses a fixed sized list of linear increasing lengths beginning from a start value.
    The result of the solving process of a length determines how the scheduler handles the length:
    NONE:   the length gets moved to the end of the list to be solved later again
    UNSAT:  the length and all smaller lengths get removed from the list and a new length gets added at the end of the list
    """


    def __init__(self,start,inc,limit,size,propagate_unsat,verbose):
        """
        Initializes the A scheduler object.

        Arguments:
        start           -- start number of steps.
        inc             -- step increase number
        limit           -- maximum number of steps
        size            -- number of simultaneous length to solve.
        propagate_unsat -- keep runs with m<n
        verbose         -- verbosity level.
        """
        self.__length          = start
        self.__inc             = inc
        self.__limit           = limit
        self.__size            = size
        self.__propagate_unsat = propagate_unsat
        self.__runs            = []
        self.__first           = True
        self.__nones           = 0
        self.__verbose         = verbose

    def next(self,result):
        """
        Creates and manages the schedule with the given result and returns the next length to solve.

        Arguments:
        result          -- result of the last solved length.
        """

        # START: add all runs
        if self.__first:
            self.__first  = False
            self.__runs   = [ self.__length+(i*self.__inc) for i in range(self.__size) ]
            self.__runs   = [ i for i in self.__runs if i<=self.__limit ]
            if len(self.__runs) > 0: self.__length = self.__runs[-1]
            self.__nones  = set()

        # NONE: check if all Nones, enqueue, and pop
        elif result is None:
            current_length = self.__runs[0]
            self.__nones.add(current_length)
            if len(self.__nones) == len(self.__runs): return None
            self.__runs.append(current_length)
            self.__runs = self.__runs[1:]

        # not NONE
        else:
            current_length = self.__runs[0]
            if current_length in self.__nones:
                self.__nones.remove(current_length)

            # UNKNOWN: enqueue and pop
            if result.unknown:
                self.__runs.append(current_length)

            # UNSAT
            else:
                if self.__propagate_unsat:                            # propagate unsat
                    self.__runs = [ i for i in self.__runs if i>=current_length ]
                next_length = self.__length + self.__inc
                if next_length <= self.__limit and not self.__nones:  # if inside the limit and mem: enqueue next
                    self.__length = next_length
                    self.__runs.append(self.__length)

            self.__runs = self.__runs[1:]                             # pop

        # log and return
        if self.__verbose: _sys.stdout.write("Queue:\t\t " + str(self.__runs) + "\n")
        return self.__runs[0] if len(self.__runs)>0 else None


class B_Scheduler(Scheduler):
    """
    B_scheduler object containing the algorithm B to schedule solve steps.

    Algorithm B uses a list Q of linear increasing lengths to solve beginning from a start value.
    The result of the solving process of a length determines how the scheduler handles the length:
    NONE: the length gets moved from Q to a list W of waiting lengths for the next iteration
    UNSAT: the length and all smaller lengths get removed from Q and W

    If Q is empty: new increasing length and elements from W get added/moved to Q if they are greater than a threshold.

    The threshold depends on the number of solving attempts for the smallest and current length and a given scheduler parameter:
    If length n (smallest length) had t solving attempts, then length n+i (every other length) has to be solved for t * r^i attempts, where i ≥ 1 and r lies between 0 and 1.
    """

    class Run:
        """
        Run object containing details about a length.
        """

        def __init__(self,index,length,effort,solve):
            """
            Initializes the run object.

            Arguments:
            index           -- index number of the length.
            length          -- length value.
            effort          -- number of times the length has been tried to solved.
            solve           -- value if the length should be solved in the current cycle.
            """
            self.index  = index
            self.length = length
            self.effort = effort
            self.solve  = solve


        def __repr__(self):
            """
            Representes the run object.
            """
            return "("+",".join([str(i) for i in [self.index,self.length,self.effort,self.solve]])+")"


    def __init__(self,start,inc,limit,size,propagate_unsat,gamma,verbose):
        """
        Initializes the B scheduler object.

        Arguments:
        start           -- start number of steps.
        inc             -- step increase number.
        limit           -- maximum number of steps.
        size            -- number of simultaneous length to solve.
        propagate_unsat -- keep runs with m<n.
        gamma           -- number affecting the threshold.
        verbose         -- verbosity level.
        """
        self.__index           = 0
        self.__start           = start
        self.__inc             = inc
        self.__limit           = limit
        self.__size            = size
        self.__propagate_unsat = propagate_unsat
        self.__gamma           = gamma
        self.__runs            = []
        self.__next_runs       = []
        self.__first           = True
        self.__nones           = set()
        self.__verbose         = verbose


    def next(self,result):
        """
        Creates and manages the schedule with the given result and returns the next length to solve.

        Arguments:
        result          -- result of the last solved length.
        """

        # if not first time
        if not self.__first:

            current = self.__runs[0]

            # NONE: append to __next_runs
            if result is None:
                self.__nones.add(current)
                self.__next_runs.append(current)

            # not NONE
            else:
                if current in self.__nones:
                    self.__nones.remove(current)
                # UNKNOWN: effort++, and append to __next_runs
                if result.unknown:
                    current.effort += 1
                    self.__next_runs.append(current)
                # UNSAT and propagate: reset __next_runs
                elif result.unsatisfiable and self.__propagate_unsat:
                    self.__next_runs = []

            # NONE, UNKNOWN or UNSAT: pop __runs
            self.__runs = self.__runs[1:]
            # move to __next_runs while not solve
            while self.__runs != [] and not self.__runs[0].solve:
                self.__next_runs.append(self.__runs[0])
                self.__runs = self.__runs[1:]

        self.__first = False

        # if no more runs
        if self.__runs == []:

            # if __next_runs is not empty: add to __runs
            if self.__next_runs != []:
                if len(self.__nones) == len(self.__next_runs): return None
                first = self.__next_runs[0]
                first.solve = True
                self.__runs = [ first ]
                for i in self.__next_runs[1:]:
                    i.solve = True if (i.effort < (((first.effort+1) * (self.__gamma ** (i.index - first.index)))+0.5)) else False
                    self.__runs.append(i)

            # else: add new to __runs
            else:
                self.__runs = [ self.Run(self.__index,self.__start+(self.__inc*self.__index),0,True) ]
                self.__index += 1
                first = self.__runs[0]
                if first.length > self.__limit: return None

            # reset __next_runs
            self.__next_runs = []

            # add next runs
            while (0.5 < ((first.effort+1) * (self.__gamma ** (self.__index - first.index)))) and not self.__nones:
                if len(self.__runs)>= self.__size: break
                next_length = self.__start+(self.__inc*self.__index)
                if next_length > self.__limit: break
                self.__runs.append(self.Run(self.__index,next_length,0,True))
                self.__index += 1

        # log and return
        if self.__verbose:
            _sys.stdout.write("Queue:\t\t " + str(self.__runs) + "\n")
            _sys.stdout.write("Pending:\t " + str(self.__next_runs) + "\n")
        #log("Queue:\t\t " + str(self.__runs))
        return self.__runs[0].length


class C_Scheduler(Scheduler):
    """
    C_scheduler object containing the algorithm C to schedule solve steps.

    Algorithm C uses a list of lengths beginning with a start value.
    Regardless the result of the solving process a new length is added at the end of the list.
    If the the result of the solving process is NONE, the length is moved to the end of the list, if UNSAT all length smaller equal to the length get removed from the list.
    A new length is calculated from the maximum length handled by the scheduler multiplied with the given increase value.
    """

    def __init__(self,start,inc,limit,propagate_unsat,verbose):
        """
        Initializes the C scheduler object.

        Arguments:
        start           -- start number of steps.
        inc             -- increase factor
        limit           -- maximum number of steps
        propagate_unsat -- keep runs with m<n
        verbose         -- verbosity level.
        """
        self.__length          = start
        self.__inc             = float(inc)
        self.__limit           = limit
        self.__propagate_unsat = propagate_unsat
        self.__runs            = []
        self.__first           = True
        self.__nones           = set()
        self.__verbose         = verbose


    def next(self,result):
        """
        Creates and manages the schedule with the given result and returns the next length to solve.

        Arguments:
        result          -- result of the last solved length.
        """

        # START: add first run
        if self.__first:
            self.__runs   = [ self.__length ]
            if self.__length == 0: self.__length = 1
            self.__first  = False

        # NONE: check if all Nones, append and pop
        elif result is None:
            self.__nones.add(self.__runs[0])
            if len(self.__nones) == len(self.__runs): return None
            self.__runs.append(self.__runs[0])
            self.__runs = self.__runs[1:]

        # ELSE: add new and handle last
        else:
            current_length = self.__runs[0]
            if current_length in self.__nones:
                self.__nones.remove(current_length)
            next_length = self.__length * self.__inc
            if int(next_length) == int(self.__length): next_length = self.__length + 1
            if int(next_length) <= self.__limit and not self.__nones:
                self.__runs.append(int(next_length))
                self.__length = next_length
            # UNKNOWN: append
            if result.unknown:
                self.__runs.append(current_length)
            # UNSAT: propagate_unsat
            elif self.__propagate_unsat:
                self.__runs = [ i for i in self.__runs if i>=current_length ]
            # pop
            self.__runs = self.__runs[1:]

        # log and return
        if self.__verbose:_sys.stdout.write("Queue:\t\t " + str(self.__runs) + "\n")
        return self.__runs[0] if len(self.__runs)>0 else None


class Solver:
    """
    Solver object containing the logic to ground and solve scheduled lengths.
    """

    def __init__(self, ctl, options):
        """
        Initializes the solver.

        Arguments:
        ctl             -- Control object holding the program.
        options         -- solver options.
        """
        self.__ctl         = ctl
        self.__length      = 0
        self.__last_length = 0
        self.__options     = options
        self.__verbose     = options['verbose']
        self.__result      = None

        # set solving and restart policy
        self.__ctl.configuration.solve.solve_limit = "umax,"+str(options['restarts_per_solve'])
        if int(options['conflicts_per_restart']) != 0:
            self.__ctl.configuration.solver[0].restarts="F,"+str(options['conflicts_per_restart'])


    def __verbose_start(self):
        """
        Starts the verbose timer.
        """
        self.__time0 = clock()


    def __verbose_end(self,string):
        """
        Ends the verbose timer and prints the time with a given string.

        Arguments:
        string          -- clingo application.
        """
        _sys.stdout.write(string+" Time:\t {:.2f}s\n".format(clock()-self.__time0))


    def solve(self,length, program_parts, on_model):
        """
        Grounds and solves the scheduler length.

        Arguments:
        length          -- length to ground and solve.
        program_parts   -- program parts to ground and solve.
        on_model        -- callback for intercepting models.
        """
        if self.__verbose:_sys.stdout.write("Grounded Until:\t {}\n".format(self.__length))
        # ground if necessary
        grounded = 0
        f = _ty.Theory()
        if self.__length < length:
            parts = []
            for t in range(self.__length+1,length+1):
                for root_name, part_name, rng in program_parts:
                    for i in rng:
                        if ((t - i >= 0 and root_name == "always") or
                            (t - i  > 0 and root_name == "dynamic") or
                            (t - i == 0 and root_name == "initial")):
                            parts.append((part_name, [t - i, t]))

            if length > 0:
                self.__ctl.release_external(_clingo.Function("__final", [self.__length]))

            if self.__verbose:
                _sys.stdout.write("Grounding...\t "+str(parts)+"\n")
                self.__verbose_start()

            self.__ctl.ground(parts)
            if self.__verbose: self.__verbose_end("Grounding")
            self.__ctl.cleanup()

            f.translate(length, self.__ctl)
            self.__ctl.assign_external(_clingo.Function("__final", [length]), True)

            grounded      = length - self.__length
            self.__length = length


        # blocking or unblocking actions
        if length < self.__last_length:
            if self.__verbose: _sys.stdout.write("Blocking actions...\n")
            for t in range(length+1,self.__last_length+1):
                self.__ctl.assign_external(_clingo.Function("skip",[t]),True)
        elif self.__last_length < length:
            if self.__verbose: _sys.stdout.write("Unblocking actions...\n")
            for t in range(self.__last_length+1,length+1):
                self.__ctl.assign_external(_clingo.Function("skip",[t]),False)

        # solve
        if self.__verbose: self.__verbose_start()
        self.__result = self.__ctl.solve(on_model=on_model)
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

def smain(prg, future_sigs, program_parts, on_model, imin = 0, imax = None, istop = "SAT", scheduler_options={}):
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
    f = _ty.Theory()
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
    f.translate(step, prg)
    prg.assign_external(_clingo.Function("__final", [step]), True)

    #solver
    solver = Solver(prg,scheduler_options)

    #scheduler
    if scheduler_options.get('A'):
        scheduler = A_Scheduler(scheduler_options['start'],scheduler_options['inc'],scheduler_options['limit'],scheduler_options['A'],scheduler_options['propagate_unsat'],scheduler_options['verbose'])
    elif scheduler_options.get('B'):
        scheduler = B_Scheduler(scheduler_options['start'],scheduler_options['inc'],scheduler_options['limit'],scheduler_options['processes'],scheduler_options['propagate_unsat'],scheduler_options['B'],scheduler_options['verbose'])
    elif scheduler_options.get('C'):
        scheduler = C_Scheduler(scheduler_options['start'],scheduler_options['C'],scheduler_options['limit'],scheduler_options['propagate_unsat'],scheduler_options['verbose'])
    else:
        scheduler = A_Scheduler(scheduler_options['start'],scheduler_options['inc'],scheduler_options['limit'],5,scheduler_options['propagate_unsat'],scheduler_options['verbose'])

    # incremental scheduled main solving loop
    max_length = 0
    sol_length = 0
    i = 1
    while ((imax is None or step < imax) and
           (step == 0 or step < imin or (
              (istop == "SAT"     and not ret.satisfiable) or
              (istop == "UNSAT"   and not ret.unsatisfiable) or
              (istop == "UNKNOWN" and not ret.unknown)))):
        if scheduler_options['verbose']:
            _sys.stdout.write("Iteration "+str(i)+"\n")
            time0 = clock()
        i += 1
        # get current solve length from scheduler
        length = scheduler.next(ret)
        if length == None:
            _sys.stdout.write("PLAN NOT FOUND")
            break
        # solve the given solve length
        ret = solver.solve(length, program_parts, on_model=lambda m: on_model(m, length))
        if ret is not None and length > max_length: max_length = length
        if ret is not None and ret.satisfiable:
            sol_length = length
            break
        if scheduler_options['verbose']: _sys.stdout.write("Iteration Time:\t {:.2f}s\n".format(clock()-time0)+"\n")
        step +=scheduler_options["inc"]

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
        self.__scheduler = {
            "start":0,
            "inc":5,
            "limit":3000,
            "restarts_per_solve":100,
            "conflicts_per_restart":60,
            "propagate_unsat":True,
            "verbose":0,
            "processes":20,
            "forbid_actions":False,
            "force_actions":False
        }

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

    def __parse_scheduler_A(self, value):
        """
        Parse scheduler A argument.
        """
        if (int(value) >= 0 and int(value) <= 50):
            self.__scheduler["A"]= int(value)
            return True
        else:
            return False

    def __parse_scheduler_B(self, value):
        """
        Parse scheduler B argument.
        """
        if (float(value) >= 0.1 and float(value) <= 0.9999):
            self.__scheduler["B"]= float(value)
            return True
        else:
            return False

    def __parse_scheduler_C(self, value):
        """
        Parse scheduler C argument.
        """
        if (float(value) >= 0.2 and float(value) <= 2.0):
            self.__scheduler["C"]= float(value)
            return True
        else:
            return False

    def __parse_start(self, value):
        """
        Parse scheduler starting argument.
        """
        self.__scheduler["start"] = int(value)
        return self.__scheduler["start"] >= 0

    def __parse_increment(self, value):
        """
        Parse scheduler increment argument.
        """
        self.__scheduler["inc"] = int(value)
        return self.__scheduler["inc"] >= 0

    def __parse_limit(self, value):
        """
        Parse scheduler limit argument.
        """
        self.__scheduler["limit"] = int(value)
        return self.__scheduler["limit"] >= 0

    def __parse_conflicts_per_restart(self, value):
        """
        Parse scheduler limit argument.
        """
        self.__scheduler["conflicts_per_restart"] = int(value)
        return self.__scheduler["conflicts_per_restart"] >= 0

    def __parse_processes(self, value):
        """
        Parse scheduler processes argument.
        """
        self.__scheduler["processes"] = int(value)
        return self.__scheduler["processes"] >= 0

    def __parse_verbose_scheduler(self, value):
        """
        Parse verbose-scheduler argument.
        """
        self.__scheduler["verbose"] = int(value)
        return self.__scheduler["verbose"] >= 0

    def __parse_forbid_actions(self, value):
        """
        Parse forbid-actions argument.
        """
        self.__scheduler["forbid_actions"] = True
        return True

    def __parse_force_actions(self, value):
        """
        Parse forbid-actions argument.
        """
        self.__scheduler["force_actions"] = True
        return True

    def __parse_propagate_unsat(self, value):
        """
        Parse propagate-unsat argument.
        """
        self.__scheduler["propagate_unsat"] = True
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
            _sys.stdout.write("\n".format(step))
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

        group = "Scheduler Options"
        # Scheduler algorithms
        options.add(group, "scheduler-A,A", "Run algorithm A with parameter n (range 1 to 50)", self.__parse_scheduler_A, argument="<n>")
        options.add(group, "scheduler-B,B", "Run algorithm B with parameter r (range 0.1 to 0.9999)", self.__parse_scheduler_B, argument="<r>")
        options.add(group, "scheduler-C,C", "Run algorithm C with parameter r (range 0.2 to 2.0)", self.__parse_scheduler_C, argument="<r>")

        # Scheduler options
        options.add(group, "scheduler-start,F", "Starting horizon length (default -F 0)", self.__parse_start, argument="<n>")
        options.add(group, "scheduler-step,S", "Step for horizon lengths 0, n, 2n, 3n, ... (default -S 5, algorithms A and B only)", self.__parse_increment, argument="<n>")
        options.add(group, "scheduler-end,T", "Ending horizon length (default -T 3000)", self.__parse_limit, argument="<n>")
        options.add(group, "scheduler-verbose", "Set verbosity level to <n>", self.__parse_verbose_scheduler, argument="<n>")
        options.add(group, "processes,M","With algorithm B, use maximum n processes (default -M 20)", self.__parse_processes, argument="<n>")
        options.add(group, "conflicts-per-restart,i", "Restart interval is n (default -i 60, use 0 for leaving open the restart policy)", self.__parse_conflicts_per_restart, argument="<n>")
        options.add(group, "keep-after-unsat", "After finding n to be UNSAT, do keep runs with m<n", self.__parse_propagate_unsat, argument="<n>")


        # Solving options
        options.add(group, "forbid-actions", "Forbid actions at time points after current plan length, using the predicate occurs/1", self.__parse_forbid_actions, argument="n")
        options.add(group, "force-actions", "Force at least one action at time points before current plan length, using the predicate occurs/1", self.__parse_force_actions, argument="n")


    def main(self, prg, files):
        """
        Implements the incremental solving loop.

        This function implements the Application.main() function as required by
        clingo.clingo_main().
        """
        schedulers = len({option : self.__scheduler[option] for option in ['A','B','C'] if option in self.__scheduler})
        with prg.builder() as b:
            files = [open(f) for f in files]
            if len(files) == 0:
                files.append(_sys.stdin)

            program = [f.read() for f in files]

            # additional programs for scheduler
            if schedulers != 0:
                EXTERNALS_PROGRAM  = """
                #program dynamic.  #external skip(t).
                """
                FORBID_ACTIONS_PROGRAM = """
                #program dynamic.
                :-     occurs(A),     skip(t). % no action
                """
                FORCE_ACTIONS_PROGRAM = """
                #program dynamic.
                :- not occurs(_), not skip(t). % some action
                """
                program.append(EXTERNALS_PROGRAM)
                if self.__scheduler['forbid_actions']:program.append(FORBID_ACTIONS_PROGRAM)
                if self.__scheduler['force_actions']:program.append(FORCE_ACTIONS_PROGRAM)

            future_sigs, program_parts = _tf.transform(program, b.add)

        if(schedulers > 1):
            raise Exception("Please, choose only one Scheduler: A, B, or C")
        elif(schedulers == 1):
            smain(prg, future_sigs, program_parts, self.__on_model, self.__imin, self.__imax, self.__istop, self.__scheduler)
        else:
            imain(prg, future_sigs, program_parts, self.__on_model, self.__imin, self.__imax, self.__istop)


def main():
    """
    Run the telingo application.
    """
    _sys.exit(int(_clingo.clingo_main(Application("telingo"), _sys.argv[1:])))
