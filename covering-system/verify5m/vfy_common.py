#!/usr/bin/env python3
"""
Independent verification utilities (adversarial re-check seat).

Written from scratch for this audit. Does NOT import any of the executor's
modules (search / crt_capacity / crt2_capacity / crt3_capacity).

Contents:
  - primes_upto: Eratosthenes on a bytearray.
  - factorize(n, primes): trial division by the prime list.
  - divisors_of(fac): all divisors from a factorisation dict.
  - sigma_of(fac): multiplicative sigma from a factorisation dict.
  - pool(n): divisors of n that are > 1 (the modulus pool for lcm = n).
"""
from math import isqrt


def primes_upto(limit):
    """All primes <= limit, sieve of Eratosthenes (bytearray)."""
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0] = 0
    sieve[1] = 0
    for i in range(2, isqrt(limit) + 1):
        if sieve[i]:
            step = i
            start = i * i
            sieve[start::step] = b"\x00" * ((limit - start) // step + 1)
    return [i for i in range(2, limit + 1) if sieve[i]]


def factorize(n, primes):
    """Factor n by trial division with the given prime list. Returns dict p->e."""
    fac = {}
    m = n
    for p in primes:
        if p * p > m:
            break
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            fac[p] = e
    if m > 1:
        fac[m] = fac.get(m, 0) + 1
    return fac


def divisors_of(fac):
    """All positive divisors from factorisation dict {p: e}."""
    divs = [1]
    for p, e in fac.items():
        cur = []
        pw = 1
        for _ in range(e + 1):
            for d in divs:
                cur.append(d * pw)
            pw *= p
        divs = cur
    return sorted(divs)


def sigma_of(fac):
    """sigma(n) = prod (p^(e+1)-1)/(p-1), exact integer."""
    s = 1
    for p, e in fac.items():
        s *= (p ** (e + 1) - 1) // (p - 1)
    return s


def pool_of(fac):
    """Modulus pool for a hypothetical covering with lcm n: divisors > 1."""
    return [d for d in divisors_of(fac) if d > 1]
