"""Reproduce the root and weight enclosures in PROOF.md using exact rationals."""

from fractions import Fraction
from itertools import product


def interval(value):
    if isinstance(value, tuple):
        return value
    return Fraction(value), Fraction(value)


def add(left, right):
    a, b = interval(left)
    c, d = interval(right)
    return a + c, b + d


def mul(left, right):
    corners = [a * b for a, b in product(interval(left), interval(right))]
    return min(corners), max(corners)


def sub(left, right):
    a, b = interval(right)
    return add(left, (-b, -a))


def div(left, right):
    a, b = interval(right)
    assert a * b > 0
    return mul(left, (1 / b, 1 / a))


def horner(coefficients, argument):
    result = interval(0)
    for coefficient in coefficients:
        result = add(mul(result, argument), coefficient)
    return result


def verify():
    q = [1, 0, -6, -1, 7, 1]
    h = [2, 4, -2, -6, -1]
    lower_micro = [-1938938, -1349121, -142428, 1207308, 2223177]
    boxes = [(Fraction(v, 10**6), Fraction(v + 1, 10**6)) for v in lower_micro]
    reported = [
        ("-0.20351", "-0.20349"), ("0.05923", "0.05925"),
        ("0.06632", "0.06635"), ("0.07387", "0.07390"),
        ("43.0038", "43.0043"),
    ]
    weights = []
    for i, (a, b) in enumerate(boxes):
        assert horner(q, a)[0] * horner(q, b)[0] < 0
        weight = horner(h, (a, b))
        for j, other in enumerate(boxes):
            if i != j:
                weight = mul(weight, div(sub(2, other), sub((a, b), other)))
        low, high = map(Fraction, reported[i])
        assert low < weight[0] <= weight[1] < high
        weights.append(weight)

    error = 2 * sum(max(abs(a), abs(b)) for a, b in weights[:4])
    assert error < Fraction(81, 100)
    assert 42 < weights[4][0] <= weights[4][1] < 44
    for i in range(4):
        assert -2 < boxes[i][0] < boxes[i][1] < 2
        assert boxes[i][1] < boxes[i + 1][0]
    lower_base = Fraction(159, 100)
    upper_base = Fraction(8, 5)
    assert lower_base + 1 / lower_base < boxes[4][0]
    assert boxes[4][1] < upper_base + 1 / upper_base
    assert 44 / lower_base**12 < Fraction(19, 100)
    assert 2 * horner(h, 2)[0] % 5 == 1
    assert horner(q, 2)[0] == -5
    print("Verified five root intervals, five weight intervals and the strict error bound.")


if __name__ == "__main__":
    verify()
