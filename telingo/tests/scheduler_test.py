import unittest
import sys
import copy
import scheduler as _sd

class TestCase(unittest.TestCase):
    def assertRaisesRegex(self, *args, **kwargs):
        return (self.assertRaisesRegexp(*args, **kwargs)
            if sys.version_info[0] < 3
            else unittest.TestCase.assertRaisesRegex(self, *args, **kwargs))

class SolveResult():
    """mock clingo SolveResult. """
    def __init__(self):
        self.unknown = False
        self.satisfiable = False
        self.unsatisfiable = False
    def set_unknown(self):
        """ set SolveResult to unknown. """
        self.unknown = True
        self.satisfiable = False
        self.unsatisfiable = False
    def set_satisfiable(self):
        """ set SolveResult to SAT. """
        self.unknown = False
        self.satisfiable = True
        self.unsatisfiable = False
    def set_unsatisfiable(self):
        """ set SolveResult to UNSAT. """
        self.unknown = False
        self.satisfiable = False
        self.unsatisfiable = True
    def __str__(self):
        ret = "error"
        if self.unknown:
            ret = "UNKNOWN"
        elif self.satisfiable:
            ret = "SAT"
        elif self.unsatisfiable:
            ret = "UNSAT"
        return ret

def string_to_result(s="NONE"):
    """ convert a string to a SolveResult. """
    ret = SolveResult()
    if s.upper() == "SAT":
        ret.set_satisfiable()
    elif s.upper() == "UNSAT":
        ret.set_unsatisfiable()
    elif s.upper() == "UKN" or s.upper() == "UNKNOWN":
        ret.set_unknown()
    elif s.upper() == "NONE":
        ret = None
    else:
        sys.stdout.write("wrong result string given\n")
    return ret

def list_exp(s):
    """ expand array of strings by multiplying the strings with the leading number. """
    ret = []
    i = 0
    while i < len(s):
        for j in range(0, s[i]):
            ret.append(s[i+1])
        i += 2
    return ret

def schedule(scheduler, results, repeat=True, imax=10):
    """ mock schedule part of the smain function. """
    scheduler = copy.deepcopy(scheduler)
    iteration = 1
    ret = []
    n = scheduler.next(string_to_result("None"))
    if n is None:
        return ret
    ret.append(n)
    while True:
        for r in results:
            n = scheduler.next(string_to_result(r))
            if iteration >= imax or n is None:
                repeat = False
                break
            ret.append(n)
            iteration += 1
        if not repeat:
            break
    return ret

class TestSchedulerA(TestCase):
    """ class containing all tests for scheduler A. """
    def test_A_result(self):
        """ test for result parameter. """
        start, inc, limit, size, propagate_unsat, verbose = 0, 5, 30, 4, True, 0
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 5, 10, 15, 0, 5, 10, 15, 0, 5])
        self.assertEqual(schedule(scheduler, ["NONE"]), [0, 5, 10, 15])

    def test_A_start_inc_limit(self):
        """ tests for start, inc and limit parameters. """
        size, propagate_unsat, verbose = 4, True, 0
        start, inc, limit = 0, 5, 30
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 5, 10, 15, 0, 5, 10, 15, 0, 5])

        start, inc, limit = 30, 5, 30
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [30, 30, 30, 30, 30, 30, 30, 30, 30, 30])

        start, inc, limit = 25, 5, 30
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [25, 30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [25, 30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [25, 30, 25, 30, 25, 30, 25, 30, 25, 30])

        start, inc, limit = -5, 5, 30
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 35, 5, 30
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, 5, 0
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

        start, inc, limit = 0, 5, 5
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 5])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 5])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 5, 0, 5, 0, 5, 0, 5, 0, 5])

        start, inc, limit = 0, 5, -5
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, 0, 5
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, 11, 30
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 11, 22])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 11, 22])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 11, 22, 0, 11, 22, 0, 11, 22, 0])

        start, inc, limit = 0, -11, 30
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, -11, -30
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

    def test_A_size(self):
        """ test for the size parameter. """
        start, inc, propagate_unsat, verbose = 0, 5, True, 0

        limit, size = 30, 4
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 5, 10, 15, 0, 5, 10, 15, 0, 5])

        limit, size = 30, 0
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        limit, size = 30, -4
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        limit, size = 10, 4
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 5, 10])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 5, 10])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 5, 10, 0, 5, 10, 0, 5, 10, 0])

    def test_A_propagate_unsat(self):
        """ tests for the propagate_unsat parameter. """
        start, inc, limit, size, verbose = 0, 1, 30, 4, 0

        propagate_unsat = True
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["UKN", "UNSAT"]), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
        self.assertEqual(schedule(scheduler, list_exp([3, "UKN", 1, "UNSAT", 9, "UKN"]), imax=13),
                         [0, 1, 2, 3, 4, 5, 6, 7, 4, 5, 6, 7, 4])
        self.assertEqual(schedule(scheduler, list_exp([5, "UKN", 1, "UNSAT"]), imax=17),
                         [0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 2, 3, 4, 5, 6, 7, 4])

        propagate_unsat = False
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["UKN", "UNSAT"]), [0, 1, 2, 3, 0, 4, 2, 5, 0, 6])
        self.assertEqual(schedule(scheduler, list_exp([3, "UKN", 1, "UNSAT", 9, "UKN"]), imax=13),
                         [0, 1, 2, 3, 0, 1, 2, 4, 0, 1, 2, 4, 0])

        start, inc, limit, size, verbose = 0, 5, 30, 4, 0
        propagate_unsat = True
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, list_exp([3, "UKN", 1, "UNSAT", 8, "UKN"])),
                         [0, 5, 10, 15, 20, 25, 30, 20, 25, 30])

        start, inc, limit, size, verbose = 0, 5, 10, 4, 0
        propagate_unsat = True
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["UKN", "UKN", "UNSAT"]), [0, 5, 10])
        propagate_unsat = False
        scheduler = _sd.A_Scheduler(start, inc, limit, size, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, list_exp([2, "UKN", 1, "UNSAT", 7, "UKN"])),
                         [0, 5, 10, 0, 5, 0, 5, 0, 5, 0])
        self.assertEqual(schedule(scheduler, ["UKN", "UKN", "UNSAT"]), [0, 5, 10, 0, 5, 0, 5, 5, 5])

class TestSchedulerB(TestCase):
    """ class containing all tests for scheduler B. """
    def test_B_result(self):
        """ test for result parameter. """
        start, inc, limit, processes, propagate_unsat, gamma, verbose = 0, 5, 30, 5, True, 0.5, 0
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 0, 5, 0, 5, 10, 0, 5, 10, 0, 15, 0, 5, 15, 0])
        self.assertEqual(schedule(scheduler, ["NONE"]), [0])

    def test_B_start_inc_limit(self):
        """ test for start, inc and limit parameters. """
        processes, propagate_unsat, gamma, verbose = 4, True, 0.5, 0

        start, inc, limit = 0, 5, 30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 0, 5, 0, 5, 10, 0, 5, 10, 0])

        start, inc, limit = 30, 5, 30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [30, 30, 30, 30, 30, 30, 30, 30, 30, 30])

        start, inc, limit = 25, 5, 30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [25, 30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [25, 30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [25, 25, 30, 25, 30, 25, 30, 25, 25, 30])

        start, inc, limit = -5, 5, 30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 35, 5, 30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, 5, 0
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

        start, inc, limit = 0, 5, 5
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 5])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 5])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 0, 5, 0, 5, 0, 5, 0, 0, 5])

        start, inc, limit = 0, 5, -5
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, 0, 5
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, 11, 30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 11, 22])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 11, 22])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 0, 11, 0, 11, 22, 0, 11, 22, 0])

        start, inc, limit = 0, -11, 30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, -11, -30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

    def test_B_processes(self):
        """ tests for processes parameter. """
        start, inc, propagate_unsat, gamma, verbose = 0, 5, True, 0.5, 0

        processes, limit = 4, 30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 5, 10, 15, 20, 25, 30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 0, 5, 0, 5, 10, 0, 5, 10, 0])

        processes, limit = 0, 30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        processes, limit = -4, 30
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        processes, limit = 4, 10
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 5, 10])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 5, 10])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 0, 5, 0, 5, 10, 0, 5, 10, 0, 0, 5, 0, 10, 0])

    def test_B_gamma(self):
        """ tests for gamma parameter. """
        start, inc, limit, processes, propagate_unsat, verbose = 0, 5, 30, 5, True, 0

        gamma = -2
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

        gamma = -0.5
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

        gamma = 0
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

        gamma = 0.1
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 0, 0, 0, 0, 0, 5, 0, 5, 0, 0, 0, 0, 0, 0])

        gamma = 0.5
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 0, 5, 0, 5, 10, 0, 5, 10, 0, 15, 0, 5, 15, 0])

        gamma = 0.25
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 0, 0, 5, 0, 5, 0, 0, 0, 5, 0, 0, 10, 0, 10])

        gamma = 0.75
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 5, 10, 0, 5, 10, 15, 20, 0, 5, 10, 15, 20, 0, 5])

        gamma = 1
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 5, 10, 15, 20, 0, 5, 10, 15, 20, 0, 5, 10, 15, 20])

        processes, limit = 10, 100

        gamma = 1
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 0, 5, 10, 15, 20])

        gamma = 2
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UNKNOWN"], imax=15),
                         [0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 0, 5, 10, 15, 20])

    def test_B_propagate_unsat(self):
        """ tests for propagate_unsat parameter. """
        start, inc, limit, processes, gamma, verbose = 0, 1, 30, 4, 0.5, 0

        propagate_unsat = True
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UKN", "UNSAT"]), [0, 0, 1, 1, 2, 2, 3, 3, 4, 4])
        self.assertEqual(schedule(scheduler, ["UKN", "UKN", "UNSAT"]), [0, 0, 1, 2, 2, 3, 4, 4, 5, 6])
        self.assertEqual(schedule(scheduler, list_exp([5, "UKN", 1, "UNSAT", 6, "UKN"]), imax=12),
                         [0, 0, 1, 0, 1, 2, 3, 3, 4, 3, 4, 5])
        self.assertEqual(schedule(scheduler, list_exp([11, "UKN", 1, "UNSAT", 8, "UKN"]), imax=20),
                         [0, 0, 1, 0, 1, 2, 0, 1, 2, 0, 3, 0, 1, 3, 1, 2, 4, 1, 2, 4])

        propagate_unsat = False
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, ["UKN", "UNSAT"]), [0, 0, 1, 1, 2, 2, 3, 3, 4, 4])
        self.assertEqual(schedule(scheduler, ["UKN", "UKN", "UNSAT"]), [0, 0, 1, 0, 2, 0, 2, 2, 3, 4])
        self.assertEqual(schedule(scheduler, list_exp([5, "UKN", 1, "UNSAT", 6, "UKN"]), imax=12),
                         [0, 0, 1, 0, 1, 2, 0, 1, 0, 3, 0, 1])
        self.assertEqual(schedule(scheduler, list_exp([11, "UKN", 1, "UNSAT", 8, "UKN"]), imax=20),
                         [0, 0, 1, 0, 1, 2, 0, 1, 2, 0, 3, 0, 1, 3, 1, 2, 4, 1, 2, 4])

        inc, limit = 5, 10
        propagate_unsat = True
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, list_exp([5, "UKN", 1, "UNSAT"])), [0, 0, 5, 0, 5, 10])
        propagate_unsat = False
        scheduler = _sd.B_Scheduler(start, inc, limit, processes, propagate_unsat, gamma, verbose)
        self.assertEqual(schedule(scheduler, list_exp([5, "UKN", 1, "UNSAT"])),
                         [0, 0, 5, 0, 5, 10, 0, 5, 0, 0])
        self.assertEqual(schedule(scheduler, list_exp([5, "UKN", 2, "UNSAT"])),
                         [0, 0, 5, 0, 5, 10, 0, 5, 5, 5])

class TestSchedulerC(TestCase):
    """ class containing all tests for scheduler C. """
    def test_C_result(self):
        """ tests for result parameter. """
        start, inc, limit, propagate_unsat, verbose = 0, 1.5, 30, True, 0
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 1, 2, 3, 4, 6, 10, 15, 22])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 1, 2, 3, 4, 6, 10, 15, 22])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 1, 0, 2, 1, 3, 0, 4, 2, 6])
        self.assertEqual(schedule(scheduler, ["NONE"]), [0])

    def test_C_start_inc_limit(self):
        """ tests for start, inc and limit parameters. """
        propagate_unsat, verbose = True, 0

        start, inc, limit = 0, 1.5, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 1, 2, 3, 4, 6, 10, 15, 22])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 1, 2, 3, 4, 6, 10, 15, 22])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 1, 0, 2, 1, 3, 0, 4, 2, 6])

        start, inc, limit = 4, 1.5, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [4, 6, 9, 13, 20, 30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [4, 6, 9, 13, 20, 30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [4, 6, 4, 9, 6, 13, 4, 20, 9, 30])

        start, inc, limit = 30, 1.5, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [30])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [30])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [30, 30, 30, 30, 30, 30, 30, 30, 30, 30])

        start, inc, limit = -5, 1.5, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 35, 1.5, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, 1.5, 0
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

        start, inc, limit = 0, 1.5, 5
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 1, 2, 3, 4])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 1, 2, 3, 4])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 1, 0, 2, 1, 3, 0, 4, 2, 1])

        start, inc, limit = 0, 1.5, 1
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 1])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 1])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 1, 0, 1, 0, 1, 0, 1, 0, 1])

        start, inc, limit = 0, 1.5, -5
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, 1, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 1, 0, 2, 1, 3, 0, 4, 2, 5])

        start, inc, limit = 0, 1, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 1, 0, 2, 1, 3, 0, 4, 2, 5])

        start, inc, limit = 4, 1, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [4, 5, 6, 7, 8, 9, 10, 11, 12, 13])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [4, 5, 6, 7, 8, 9, 10, 11, 12, 13])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [4, 5, 4, 6, 5, 7, 4, 8, 6, 9])

        start, inc, limit = 0, 11, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [0, 1, 11])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [0, 1, 11])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [0, 1, 0, 11, 1, 0, 11, 1, 0, 11])

        start, inc, limit = 0, 11, -30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, -11, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, -11, -30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, 0.5, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

        start, inc, limit = 0, 0, 30
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["SAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNSAT"]), [])
        self.assertEqual(schedule(scheduler, ["UNKNOWN"]), [])

    def test_C_propagate_unsat(self):
        """ tests for propagate_unsat parameter. """
        start, inc, limit, verbose = 0, 1.5, 30, 0

        propagate_unsat = True
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["UKN", "UNSAT"], imax=11),
                         [0, 1, 2, 3, 4, 6, 10, 15, 22, 22])
        self.assertEqual(schedule(scheduler, ["UKN", "UKN", "UNSAT"]),
                         [0, 1, 0, 2, 1, 3, 4, 6, 10, 15])
        self.assertEqual(schedule(scheduler, list_exp([5, "UKN", 1, "UNSAT"]), imax=12),
                         [0, 1, 0, 2, 1, 3, 4, 6, 10, 15, 4, 22])

        propagate_unsat = False
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, ["UKN", "UNSAT"], imax=11),
                         [0, 1, 0, 2, 3, 0, 4, 6, 3, 10, 15])
        self.assertEqual(schedule(scheduler, ["UKN", "UKN", "UNSAT"]),
                         [0, 1, 0, 2, 1, 3, 4, 2, 6, 1])
        self.assertEqual(schedule(scheduler, list_exp([5, "UKN", 1, "UNSAT"]), imax=12),
                         [0, 1, 0, 2, 1, 3, 0, 4, 2, 6, 1, 10])


        start, inc, limit, verbose = 0, 1.5, 3, 0
        propagate_unsat = True
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, list_exp([5, "UKN", 1, "UNSAT"])),
                         [0, 1, 0, 2, 1, 3])
        propagate_unsat = False
        scheduler = _sd.C_Scheduler(start, inc, limit, propagate_unsat, verbose)
        self.assertEqual(schedule(scheduler, list_exp([5, "UKN", 1, "UNSAT"])),
                         [0, 1, 0, 2, 1, 3, 0, 2, 1, 0])

class TestSchedulerConfig(TestCase):
    """ class containing all tests for scheduler config. """
    def test_build(self):
        """ tests for building a scheduler. """
        config = _sd.Scheduler_Config()
        self.assertEqual(config.single_scheduler(), False)
        config.A = 5
        self.assertEqual(config.single_scheduler(), True)
        config.B = 0.5
        with self.assertRaises(Exception) as context:
            config.single_scheduler()
        config.A = None
        self.assertEqual(config.single_scheduler(), True)
        config.C = 1
        with self.assertRaises(Exception) as context:
            config.single_scheduler()
        config.B = None
        self.assertEqual(config.single_scheduler(), True)
        config.A = 5
        with self.assertRaises(Exception) as context:
            config.single_scheduler()
        config.B = 0.5
        with self.assertRaises(Exception) as context:
            config.single_scheduler()

if __name__ == '__main__':
    unittest.main()
