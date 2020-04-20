import unittest
import sys
import clingo
import telingo
import telingo.transformers as transformers
import scheduler as _sd

class TestCase(unittest.TestCase):
    def assertRaisesRegex(self, *args, **kwargs):
        return (self.assertRaisesRegexp(*args, **kwargs)
            if sys.version_info[0] < 3
            else unittest.TestCase.assertRaisesRegex(self, *args, **kwargs))


def parse_model(m, s, dual):
    ret = []
    for sym in m.symbols(shown=True):
        if not sym.name.startswith("__"):
            ret.append(sym)
    if dual:
        flip = lambda sym: clingo.Function(sym.name, sym.arguments[:-1] + [s - sym.arguments[-1].number], sym.positive)
        ret = [flip(sym) for sym in ret]
    return list(map(str, sorted(ret)))

def setattrs(_self, **kwargs):
    for k, v in kwargs.items():
        setattr(_self, k, v)
    return _self

def solve(s, sconfig=_sd.Scheduler_Config(), imin=0, imax=20, dual=False, always=True, v=False, zero=True):
    r = []
    prg = clingo.Control(['0'], message_limit=0)
    scheduler = sconfig.single_scheduler()
    with prg.builder() as b:
        program = ("#program always. " if always else "") + s
        program = program + (" #program initial. :- &final. " if not zero else "")
        if scheduler:
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
            program = program + externals_program
            if getattr(sconfig, "forbid_actions", False): program = program + forbid_actions_program
            if getattr(sconfig, "force_actions", False): program = program + force_actions_program
        if v: sys.stdout.write("\nprogram: {}\n".format(program))
        future_sigs, reground_parts = transformers.transform([program], b.add)

    if scheduler:
        telingo.smain(prg, future_sigs, reground_parts, lambda m, s: r.append(parse_model(m, s, dual)), imax=imax, imin=imin, scheduler_options=sconfig)
    else:
        sys.stdout.write("missing scheduler\n")
        telingo.imain(prg, future_sigs, reground_parts, lambda m, s: r.append(parse_model(m, s, dual)), imax=imax, imin=imin)
    return sorted(r)


class TestScheduler(TestCase):
    """ class containing all tests for scheduled telingo."""
    def test_scheduler_inc_linear(self):
        """ tests for linear growth schedulers algorithm. """
        _configs = []
        # scheduler A, size = 1, inc = 3
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, A=1, inc=3))
        # scheduler B, gamma = 0.1, inc = 3
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, B=0.1, inc=3))

        for sconfig in _configs:
            self.assertEqual(solve("p.", sconfig, imin=3), [
                ['p(0)'],
                ['p(0)', 'p(1)', 'p(2)', 'p(3)'],
                ['p(0)', 'p(1)', 'p(2)', 'p(3)', 'p(4)', 'p(5)', 'p(6)']])
            self.assertEqual(solve("p. q:-'p.", sconfig, imin=2), [
                ['p(0)'],
                ['p(0)', 'p(1)', 'p(2)', 'p(3)', 'q(1)', 'q(2)', 'q(3)']])
            self.assertEqual(solve("p :- &initial. p :- not 'p. :- not p, &final.", sconfig, zero=False), [['p(0)', 'p(2)', 'p(4)', 'p(6)']])
            self.assertEqual(solve("p :- not 'p, not &initial. :- not p, &final.", sconfig, zero=False), [['p(1)', 'p(3)']])
            self.assertEqual(solve("#program final. p.", sconfig, zero=False), [['p(3)']])
            self.assertEqual(solve("p :- not &initial. :- p, &final.", sconfig), [[]])
            self.assertEqual(solve("1{p;q}1. q :- 'p. p :- 'q.", sconfig, zero=False), [
                ['p(0)', 'p(2)', 'q(1)', 'q(3)'], ['p(1)', 'p(3)', 'q(0)', 'q(2)']])

    def test_scheduler_inc_exp(self):
        """ tests for exponential growth schedulers algorithm. """
        sconfig = _sd.Scheduler_Config()
        setattrs(sconfig, conflicts_per_restart=0, C=2)
        self.assertEqual(solve("p.", sconfig, imin=4), [
            ['p(0)'],
            ['p(0)', 'p(1)'],
            ['p(0)', 'p(1)', 'p(2)'],
            ['p(0)', 'p(1)', 'p(2)', 'p(3)', 'p(4)']])
        self.assertEqual(solve("p:-&initial. p:-not 'p. :- not p, &final.", sconfig, imin=4, zero=False), [
            ['p(0)', 'p(2)'],
            ['p(0)', 'p(2)', 'p(4)']])
        self.assertEqual(solve("p :- not 'p, not &initial. :- not p, &final.", sconfig, imin=4, zero=False), [['p(1)']])
        self.assertEqual(solve("p :- not 'p, not &initial. :- p, &final.", sconfig, imin=4, zero=False), [['p(1)'], ['p(1)', 'p(3)']])
        self.assertEqual(solve("1{p;q}1. q :- 'p. p :- 'q.", sconfig, imin=3, zero=False), [
            ['p(0)', 'p(2)', 'q(1)'],
            ['p(0)', 'q(1)'],
            ['p(1)', 'q(0)'],
            ['p(1)', 'q(0)', 'q(2)']])

    def test_scheduler_start(self):
        """ tests for scheduler start parameter. """
        _configs = []
        # scheduler A, size = 1, inc = 1, start = 3
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, A=1, inc=1, start=3))
        # scheduler B, gamma = 0.1, inc = 1, start = 3
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, B=0.1, inc=1, start=3))
        # scheduler C, exponent = 1, start = 3
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, C=1, start=3))

        for sconfig in _configs:
            self.assertEqual(solve("p.", sconfig), [['p(0)', 'p(1)', 'p(2)', 'p(3)']])
            self.assertEqual(solve("p:-&initial. p:-not 'p. :- not p, &final.", sconfig), [['p(0)', 'p(2)', 'p(4)']])
            self.assertEqual(solve("p :- not 'p, not &initial. :- not p, &final.", sconfig), [['p(1)', 'p(3)']])

    def test_scheduler_limit(self):
        """ tests for limit parameter. """
        _configs = []
        # scheduler A, size = 1, inc = 1, limit = 3
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, A=1, inc=1, limit=3))
        # scheduler B, gamma = 0.1, inc = 1, limit = 3
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, B=0.1, inc=1, limit=3))
        # scheduler C, exponent = 1, limit = 3
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, C=1, limit=3))

        for sconfig in _configs:
            self.assertEqual(solve("p(0):-&initial. p(I+1):-'p(I). :- &final, p(I), I<5.", sconfig), [])

    def test_scheduler_force_action(self):
        """ tests for the force action parameter. """
        _configs = []
        # scheduler A, size = 1, inc = 1, force_actions = True
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, A=1, inc=1, force_actions=True))
        # scheduler B, gamma = 0.1, inc = 1, force_actions = True
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, B=0.1, inc=1, force_actions=True))
        # scheduler C, exponent = 1, force_actions = True
        _configs.append(setattrs(_sd.Scheduler_Config(), conflicts_per_restart=0, C=1, force_actions=True))

        for sconfig in _configs:
            s = '''
            #program dynamic.
            {occurs(a)}.
            p:-occurs(a).
            #show p/0.
            '''
            self.assertEqual(solve(s, sconfig, imin=4, zero=False), [
                ['p(1)'],
                ['p(1)', 'p(2)'],
                ['p(1)', 'p(2)', 'p(3)']])
            setattrs(sconfig, start=3)
            self.assertEqual(solve(s, sconfig), [['p(1)', 'p(2)', 'p(3)']])


if __name__ == '__main__':
    unittest.main()
