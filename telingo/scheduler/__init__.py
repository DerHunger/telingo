"""
This module contains functions to schedule solving lengths.

Classes:
Scheduler   -- Scheduler interface.
A_Scheduler -- Scheduler class for algorithm A.
B_Scheduler -- Scheduler class for algorithm B.
C_Scheduler -- Scheduler class for algorithm C.
"""

import sys as _sys

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
    UNKNOWN:    the length gets moved to the end of the list to be solved later again
    UNSAT/SAT:  the length and all smaller lengths get removed from the list and a new length gets added at the end of the list
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
        self.__nones           = set()
        self.__verbose         = verbose

    def next(self,result):
        """
        Creates and manages the schedule with the given result and returns the next length to solve.

        Arguments:
        result          -- result of the last solved length.
        """
        # START: add all runs
        if self.__first:
            if self.__length < 0 or self.__limit < self.__length or self.__inc <= 0: return None
            self.__first  = False
            self.__runs   = [ self.__length+(i*self.__inc) for i in range(self.__size) ]
            self.__runs   = [ i for i in self.__runs if (i<=self.__limit and i >= self.__length) ]
            if len(self.__runs) > 0: self.__length = self.__runs[-1]
        # No more runs left
        elif len(self.__runs) == 0: return None
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
                if self.__propagate_unsat:
                    self.__runs = [ i for i in self.__runs if i>=current_length ]
                next_length = self.__length + self.__inc
                if next_length <= self.__limit and not self.__nones:
                    self.__length = next_length
                    self.__runs.append(self.__length)
                if self.__propagate_unsat:
                    tmp = next_length
                    while len(self.__runs) <= self.__size:
                        tmp +=self.__inc
                        if tmp > self.__limit : break
                        self.__runs.append(tmp)
                    self.__length = tmp

            self.__runs = self.__runs[1:]

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
        size            -- max number of simultaneous length to solve.
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
        if self.__first:
            if self.__start < 0 or self.__inc <= 0 or self.__start > self.__limit: return None
            self.__first = False
        else:
            # No more runs left
            if len(self.__runs) == 0: return None
            current = self.__runs[0]

            # NONE: append to __next_runs
            if result is None:
                self.__nones.add(current)
                if len(self.__nones) == len(self.__runs): return None
                self.__next_runs.append(current)

            # not NONE
            else:
                if current in self.__nones:
                    self.__nones.remove(current)
                # UNKNOWN: increase effort and append to __next_runs
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


        # if no more runs
        if self.__runs == []:

            # move pending runs to current runs
            if self.__next_runs != []:
                if len(self.__nones) == len(self.__next_runs): return None
                first = self.__next_runs[0]
                first.solve = True
                self.__runs = [ first ]
                # append runs, set solve if threshold is big enough
                for i in self.__next_runs[1:]:
                    i.solve = True if (i.effort < (((first.effort+1) * (self.__gamma ** (i.index - first.index)))+0.5)) else False
                    self.__runs.append(i)

            # else: add new runs
            else:
                if len(self.__runs)>= self.__size: return None
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
            if self.__length < 0 or self.__limit < 0 or self.__inc < 1 or self.__length > self.__limit: return None
            self.__runs = [self.__length]
            #if self.__length == 0: self.__length = 1
            self.__first  = False

        # NONE: check if all are None, append and pop
        elif result is None:
            self.__nones.add(self.__runs[0])
            if len(self.__nones) == len(self.__runs): return None
            self.__runs.append(self.__runs[0])
            self.__runs = self.__runs[1:]

        # ELSE: add new and handle last
        else:
            if len(self.__runs) == 0: return None
            current_length = self.__runs[0]
            if current_length in self.__nones:
                self.__nones.remove(current_length)
            next_length = self.__length * self.__inc
            if int(next_length) == int(self.__length):
                next_length = self.__length + 1
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


class Scheduler_Config:
    """
    Scheduler_Config object contains the configuration for a scheduler to build.

    A						- algorithm A parameter
    B						- algorithm B parameter
    C						- algorithm C parameter
    inc						- horizon increase length (A,B only) [5]
    processes				- Maximum number of processes (B only) [20]
    start					- starting horizon length [0]
    limit					- ending horizon length [3000]
    restarts_per_solve		- number of restarts per solve [100]
    conflicts_per_restart	- number of conflicts per restarts [60]
    propagate-unsat			- after finding n to be UNSAT, do keep runs with m<n [t]
    move_final				- move final to current solving length, instead of maximum [t]
    forbid-actions			- forbid actions at time points after current plan length, using the predicate occurs/1 [f]
    force-actions			- force at least one action at time points before current plan length, using the predicate occurs/1 [f]
    verbose					- set verbosity level [0]
    """
    # scheduler
    A = None
    B = None
    C = None
    inc = 5
    processes = 20
    # options
    start = 0
    limit = 3000
    restarts_per_solve = 100
    conflicts_per_restart = 60
    propagate_unsat = True
    forbid_actions = False
    force_actions = False
    move_final = True # True - move final to current length, False - keep final at highest length
    verbose = 0

    def __init__(self):
        pass

    def __str__(self):
        string = "\n"
        string += "\tA: {}\n".format(self.A)
        string += "\tB: {}\n".format(self.B)
        string += "\tC: {}\n".format(self.C)
        string += "\tinc: {}\n".format(self.inc)
        string += "\tstart: {}\n".format(self.start)
        string += "\tlimit: {}\n".format(self.limit)
        string += "\trestarts_per_solve: {}\n".format(self.restarts_per_solve)
        string += "\tconflicts_per_restart: {}\n".format(self.conflicts_per_restart)
        string += "\tpropagate_unsat: {}\n".format(self.propagate_unsat)
        string += "\tforbid_actions: {}\n".format(self.forbid_actions)
        string += "\tforce_actions: {}\n".format(self.force_actions)
        string += "\tmove_final: {}\n".format(self.move_final)
        string += "\tverbose: {}\n".format(self.verbose)
        return string

    def build_scheduler(self):
        """
        Builds a scheduler with the current configuration.

        If no algorithm is defined, the scheduler will use algorithm A with the parameter 5.
        """
        scheduler = None
        if self.single_scheduler():
            if self.A:
                scheduler = A_Scheduler(self.start,self.inc,self.limit,self.A,self.propagate_unsat,self.verbose)
            elif self.B:
                scheduler = B_Scheduler(self.start,self.inc,self.limit,self.processes,self.propagate_unsat,self.B,self.verbose)
            elif self.C:
                scheduler = C_Scheduler(self.start,self.C,self.limit,self.propagate_unsat,self.verbose)
        if scheduler is None:
            scheduler = A_Scheduler(self.start,self.inc,self.limit,5,self.propagate_unsat,self.verbose)
        return scheduler

    def single_scheduler(self):
        """
        Checks if there is only one algorithm defined for the scheduler.
        """
        number = sum([1 for i in ['A','B','C'] if getattr(self,i,None) is not None])
        if number >1: # check argument error
            raise Exception("Please, choose only one Scheduler: A, B, or C")
            return False
        elif number == 1:
            return True
        else:
            return False
