from time import time
from contextlib import contextmanager
from collections import defaultdict

INF = float("inf")

def pretty_time(seconds):
    """https://stackoverflow.com/a/18421524/1868332"""
    mus = seconds * 10**6
    intervals = [
        ("µs", 1),
        ("ms", 1000),
        ("s", 1000),
        ('min', 60),
        ('h', 60)
    ]

    number = mus
    unit = intervals[0][0]
    for new_unit, ratio in intervals[1:]:
        new_number = float(number) / ratio
        # If the new number is too small, don't go to the next unit.
        if new_number < 2:
            break
        unit, number = new_unit, new_number
    return f"{number:.1f} {unit}"
    #return '{} {}'.format(shown_num, unit)


class Proc:
    REGISTRY = {}

    @classmethod
    def get(cls, name):
        if name not in cls.REGISTRY:
            cls.REGISTRY[name] = Proc(name=name)
        return cls.REGISTRY[name]

    def __init__(self, name):
        self.name = name
        self.times = []
        self.n_fails = 0

    def add(self, time, count=1):
        for _ in range(count):
            self.times.append(float(time))

    @property
    def min(self):
        if not self.times:
            return INF
        return min(self.times)

    @property
    def max(self):
        if not self.times:
            return INF
        return max(self.times)

    @property
    def avg(self):
        if not self.times:
            return INF
        return sum(self.times) / len(self.times)

    @property
    def med(self):
        if not self.times:
            return INF
        self.times.sort()
        return self.times[len(self.times)//2]

    def report(self):
        print(
            f'{self.name:>35s}:  '
            f'{pretty_time(self.min):7s} - {pretty_time(self.max):7s}  '
            f'(avg: {pretty_time(self.avg):7s} med: {pretty_time(self.med):7s})  '
            f'{len(self.times)} runs, {self.n_fails} fails'
        )


@contextmanager
def Time(name, count=1):
    t0 = time()
    try:
        yield
    except:
        t = time() - t0
        Proc.get(name).n_fails += 1
        name = 'failed:' + name
        if count == 1:
            Proc.get(name).add(t / count, count)
        raise
    else:
        t = time() - t0
        Proc.get(name).add(t / count, count)


def TimeReport():
    print("\nTime report:")
    for name, proc in Proc.REGISTRY.items():
        proc.report()
    print()
