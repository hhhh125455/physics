"""End-to-end reconstruction of the bouncing complex time from raw Lanczos b_n.

Conventions: beta = 2*pi, symmetric thermal two-point weight
W(w) = pi*w**2/(cosh(pi*w)-cos(pi*w)).

1. Integrate the exact weight to obtain moments (only input from holography).
2. Stieltjes orthogonalization -> *raw* Lanczos coefficients b_n.
3. Discard moment inputs; reconstruct even moments using only the Jacobi matrix.
4. Estimate the moment normalization from the largest Jacobi moment.
5. Prony extraction -> complex roots -> symmetrized complex time.
6. Apply the known half-KMS imaginary shift to compare to paper's retarded time.

This is a high-precision numerical test, NOT a Lean proof of the infinite-sum
asymptotics or of the geometric/WKB identification of the singularity.
"""

from __future__ import annotations

import argparse
import mpmath as mp


def raw_moments(degree: int) -> list[mp.mpf]:
    pi = mp.pi
    cuts = [0, 1, 4, 10, 30, 80, mp.inf]
    result = []
    for n in range(degree + 1):
        power = 2 * n + 2

        def integrand(x: mp.mpf) -> mp.mpf:
            if x == 0:
                return mp.mpf("0.25") if n == 0 else mp.mpf(0)
            e = mp.exp(-x)
            den = mp.expm1(-x) ** 2 + 4 * e * mp.sin(x / 2) ** 2
            return x**power * e / den

        value = mp.quad(integrand, cuts) / (2 * pi ** (2 * n))
        result.append(value)
    return result


def multiply_x(coeffs: list[mp.mpf]) -> list[mp.mpf]:
    return [mp.mpf(0)] + coeffs


def poly_norm2(coeffs: list[mp.mpf], moments: list[mp.mpf]) -> mp.mpf:
    total = mp.mpf(0)
    for i, a in enumerate(coeffs):
        if a == 0:
            continue
        for j, b in enumerate(coeffs):
            if b == 0 or (i + j) % 2:
                continue
            total += a * b * moments[(i + j) // 2]
    return total


def get_lanczos(moments: list[mp.mpf]) -> list[mp.mpf]:
    """Return [b_0=0,b_1,...,b_N] using monic OP recurrence."""
    N = len(moments) - 1
    h_prev = mp.mpf(0)
    P_prev: list[mp.mpf] = []
    P = [mp.mpf(1)]
    h = moments[0]
    b = [mp.mpf(0)]
    for n in range(1, N + 1):
        P_next = multiply_x(P)
        if n > 1:
            coefficient = h / h_prev
            for j, cj in enumerate(P_prev):
                P_next[j] -= coefficient * cj
        h_next = poly_norm2(P_next, moments)
        if h_next <= 0:
            raise ArithmeticError(f"lost positive norm at n={n}; raise precision")
        b.append(mp.sqrt(h_next / h))
        P_prev, P, h_prev, h = P, P_next, h, h_next
    return b


def moments_from_b(b: list[mp.mpf]) -> list[mp.mpf]:
    """Compute m_2n = ||J^n e0||^2 from b alone, m0=1."""
    N = len(b) - 1
    v = [mp.mpf(0) for _ in range(N + 1)]
    v[0] = mp.mpf(1)
    moments = [mp.mpf(1)]
    for _ in range(N):
        v = [(b[j] * v[j - 1] if j else 0)
             + (b[j + 1] * v[j + 1] if j < N else 0)
             for j in range(N + 1)]
        moments.append(mp.fsum(x * x for x in v))
    return moments


def scaled_q(moment: mp.mpf, n: int) -> mp.mpf:
    return 2 * mp.pi ** (2 * n) * moment / mp.factorial(2 * n + 2)


def extract_prony(E: list[mp.mpf], n: int):
    e0, e1, e2, e3 = E[n:n + 4]
    D = e0 * e2 - e1 * e1
    c = (e0 * e3 - e1 * e2) / D
    d = (e1 * e3 - e2 * e2) / D
    return c, d


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--degree", type=int, default=24)
    p.add_argument("--dps", type=int, default=125)
    args = p.parse_args()
    mp.mp.dps = args.dps
    N = args.degree
    print(f"precision={mp.mp.dps}, Lanczos degree={N}", flush=True)
    mu = raw_moments(N)
    b = get_lanczos(mu)
    print("b1,b2,b3 =", *(mp.nstr(v, 22) for v in b[1:4]), flush=True)
    recovered_m = moments_from_b(b)
    max_rel = max(abs(recovered_m[n] / (mu[n] / mu[0]) - 1)
                  for n in range(1, N + 1))
    print("max relative moment reconstruction error =", mp.nstr(max_rel, 10), flush=True)
    q = [scaled_q(m, n) for n, m in enumerate(recovered_m)]
    E = [v / q[-1] - 1 for v in q]
    print("n        c_hat                        d_hat", flush=True)
    for n in (3, 5, 8, 10, 12, 15):
        if n + 3 >= N:
            continue
        c, d = extract_prony(E, n)
        print(f"{n:2}   {mp.nstr(c, 26):<28} {mp.nstr(d, 26)}", flush=True)
    n = min(12, N - 5)
    c, d = extract_prony(E, n)
    root_plus = (c + mp.sqrt(c * c - 4 * d)) / 2
    if mp.im(root_plus) < 0:
        root_plus = (c - mp.sqrt(c * c - 4 * d)) / 2
    A = 1 / mp.sqrt(root_plus)
    if mp.im(A) > 0:
        A = -A
    z_sym = 1j * mp.pi * A
    t_ret = z_sym - 1j * mp.pi
    print("reconstructed r+ =", mp.nstr(root_plus, 28), flush=True)
    print("reconstructed A =", mp.nstr(A, 28), flush=True)
    print("reconstructed retarded t*/pi =", mp.nstr(t_ret / mp.pi, 28), flush=True)
    print("paper target t*/pi = 1 + 1j", flush=True)


if __name__ == "__main__":
    main()
