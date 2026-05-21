from __future__ import annotations
from decimal import Decimal, ROUND_HALF_EVEN, getcontext
from fractions import Fraction
from itertools import product
import json
from typing import Iterable
from pwn import context, remote


HOST = "127.0.0.1"
PORT = 1344
MAX_RADIUS = 3

context.log_level = "error"
getcontext().prec = 150


class Client:
    def __init__(self, host: str, port: int):
        self.io = remote(host, port)
        self.io.recvuntil(b"> ")

    def close(self) -> None:
        self.io.sendline(b"exit")
        self.io.close()

    def call(self, cmd: str, payload: dict | None = None) -> dict:
        if payload is None:
            line = cmd
        else:
            line = f"{cmd} {json.dumps(payload, separators=(',', ':'))}"
        self.io.sendline(line.encode())
        data = self.io.recvuntil(b"> ", drop=True).strip()
        line = data.splitlines()[-1]
        return json.loads(line.decode())


def is_square(x: int, p: int) -> bool:
    x %= p
    return x == 0 or pow(x, (p - 1) // 2, p) == 1


def sqrt_mod(x: int, p: int) -> int:
    x %= p
    if x == 0:
        return 0
    if not is_square(x, p):
        raise ValueError("not a square")
    if p % 4 == 3:
        return pow(x, (p + 1) // 4, p)

    q = p - 1
    s = 0
    while q % 2 == 0:
        s += 1
        q //= 2

    z = 2
    while is_square(z, p):
        z += 1

    m = s
    c = pow(z, q, p)
    t = pow(x, q, p)
    r = pow(x, (q + 1) // 2, p)

    while t != 1:
        i = 1
        t2 = (t * t) % p
        while t2 != 1:
            t2 = (t2 * t2) % p
            i += 1
            if i == m:
                raise ValueError("not a square")
        b = pow(c, 1 << (m - i - 1), p)
        m = i
        c = (b * b) % p
        t = (t * c) % p
        r = (r * b) % p

    if (r * r) % p != x:
        raise ValueError("not a square")
    return r


def cube_roots_of_unity(p: int) -> list[int]:
    sqrt_neg_3 = sqrt_mod(-3, p)
    inv2 = pow(2, -1, p)
    w = ((sqrt_neg_3 - 1) * inv2) % p
    roots = []
    for x in (w, (w * w) % p):
        if x != 1 and pow(x, 3, p) == 1 and x not in roots:
            roots.append(x)
    return roots


def pass_residue_filters(params: dict, m: int, r: int, k: int) -> bool:
    p = params["p"]
    for am, ar, ak, c in params["residue_filters"]:
        if not is_square((am * m + ar * r + ak * k + c) % p, p):
            return False
    return True


def round_fraction(x: Fraction) -> int:
    if x >= 0:
        return (2 * x.numerator + x.denominator) // (2 * x.denominator)
    return -((-2 * x.numerator + x.denominator) // (2 * x.denominator))


def lll_reduction(basis: list[list[int]], delta: Fraction = Fraction(99, 100)) -> list[list[int]]:
    basis = [row[:] for row in basis]
    n = len(basis)
    m = len(basis[0])

    def gram_schmidt():
        bstar: list[list[Fraction]] = []
        mu = [[Fraction(0) for _ in range(n)] for __ in range(n)]
        norm: list[Fraction] = []

        for i in range(n):
            v = [Fraction(x) for x in basis[i]]
            for j in range(i):
                if norm[j] != 0:
                    mu[i][j] = sum(Fraction(basis[i][k]) * bstar[j][k] for k in range(m)) / norm[j]
                    for k in range(m):
                        v[k] -= mu[i][j] * bstar[j][k]
            bstar.append(v)
            norm.append(sum(x * x for x in v))

        return mu, norm

    k = 1
    mu, norm = gram_schmidt()
    while k < n:
        for j in range(k - 1, -1, -1):
            q = round_fraction(mu[k][j])
            if q:
                basis[k] = [basis[k][i] - q * basis[j][i] for i in range(m)]
                mu, norm = gram_schmidt()

        if norm[k] >= (delta - mu[k][k - 1] ** 2) * norm[k - 1]:
            k += 1
        else:
            basis[k], basis[k - 1] = basis[k - 1], basis[k]
            mu, norm = gram_schmidt()
            k = max(k - 1, 1)

    return basis


def gso_decimal(basis: list[list[int]]):
    n = len(basis)
    m = len(basis[0])
    bdec = [[Decimal(x) for x in row] for row in basis]
    bstar: list[list[Decimal]] = []
    mu = [[Decimal(0) for _ in range(n)] for __ in range(n)]
    norm: list[Decimal] = []

    for i in range(n):
        v = bdec[i][:]
        for j in range(i):
            if norm[j] != 0:
                mu[i][j] = sum(bdec[i][k] * bstar[j][k] for k in range(m)) / norm[j]
                for k in range(m):
                    v[k] -= mu[i][j] * bstar[j][k]
        bstar.append(v)
        norm.append(sum(x * x for x in v))

    return bstar, mu, norm


def babai_coefficients(basis: list[list[int]], target: list[int]) -> list[int]:
    n = len(basis)
    m = len(basis[0])
    bstar, mu, norm = gso_decimal(basis)
    tdec = [Decimal(x) for x in target]
    center = [sum(tdec[k] * bstar[i][k] for k in range(m)) / norm[i] for i in range(n)]

    z = [0] * n
    for i in reversed(range(n)):
        c = center[i] - sum(Decimal(z[j]) * mu[j][i] for j in range(i + 1, n))
        z[i] = int(c.to_integral_value(rounding=ROUND_HALF_EVEN))
    return z


def lattice_vector(basis: list[list[int]], coeffs: list[int]) -> list[int]:
    return [sum(coeffs[i] * basis[i][j] for i in range(len(basis))) for j in range(len(basis[0]))]


def build_relation_lattice(params: dict, omega: int):
    p = params["p"]
    base = params["base"]
    step = params["step"]
    account_id = params["account_id"]
    item_limit = params["item_limit"]
    limb_bound = params["limb_bound"]

    centers = [item_limit // 2, limb_bound // 2, limb_bound // 2, limb_bound // 2, limb_bound // 2]
    bounds = [item_limit, limb_bound, limb_bound, limb_bound, limb_bound]

    coeffs = [
        (omega * base) % p,
        (omega * step) % p,
        omega % p,
        (-step) % p,
        (-1) % p,
    ]

    constant = (
        omega * (base * centers[0] + step * centers[1] + centers[2])
        - (base * account_id + step * centers[3] + centers[4])
    ) % p

    q = 1 << 96
    h = 1 << 72
    scales = [max(1, q // (b // 2)) for b in bounds]

    basis = []
    for i, coeff in enumerate(coeffs):
        row = [0] * 6
        row[i] = scales[i]
        row[5] = coeff * h
        basis.append(row)
    basis.append([0, 0, 0, 0, 0, p * h])

    reduced = lll_reduction(basis)
    target = [0, 0, 0, 0, 0, -constant * h]
    return reduced, target, centers, bounds, scales, coeffs, constant, h


def parse_relation_vector(
    vector: list[int],
    target: list[int],
    centers: list[int],
    bounds: list[int],
    scales: list[int],
    coeffs: list[int],
    constant: int,
    h: int,
    p: int,
) -> Iterable[tuple[int, int, int, int, int]]:
    diff = [vector[i] - target[i] for i in range(6)]
    for candidate in (diff, [-x for x in diff]):
        if candidate[5] % h != 0:
            continue

        shifts = []
        ok = True
        for i in range(5):
            if candidate[i] % scales[i] != 0:
                ok = False
                break
            shifts.append(candidate[i] // scales[i])
        if not ok:
            continue

        values = tuple(centers[i] + shifts[i] for i in range(5))
        if not all(0 <= values[i] < bounds[i] for i in range(5)):
            continue
        if (constant + sum(coeffs[i] * shifts[i] for i in range(5))) % p != 0:
            continue
        yield values


def enumerate_short_relations(params: dict, omega: int, max_radius: int):
    p = params["p"]
    lattice = build_relation_lattice(params, omega)
    basis, target, centers, bounds, scales, coeffs, constant, h = lattice
    z0 = babai_coefficients(basis, target)
    dimension = len(basis)

    seen: set[tuple[int, int, int, int, int]] = set()
    for radius in range(max_radius + 1):
        for offset in product(range(-radius, radius + 1), repeat=dimension):
            if max(map(abs, offset)) != radius:
                continue
            coeff = [z0[i] + offset[i] for i in range(dimension)]
            vector = lattice_vector(basis, coeff)
            for relation in parse_relation_vector(
                vector, target, centers, bounds, scales, coeffs, constant, h, p
            ):
                if relation in seen:
                    continue
                seen.add(relation)
                yield radius, relation


def usable_y_and_z(x: int, b: int, p: int) -> tuple[int, int] | None:
    rhs = (pow(x, 3, p) + b) % p
    if not is_square(rhs, p):
        return None
    y = sqrt_mod(rhs, p)
    if not is_square(y, p):
        y = (-y) % p
    if not is_square(y, p):
        return None
    z = sqrt_mod(y, p)
    return y, z


def main() -> None:
    client = Client(HOST, PORT)
    tested = 0
    try:
        params = client.call("params")
        assert params["ok"], params

        p = params["p"]
        b = params["b"]
        base = params["base"]
        step = params["step"]
        account_id = params["account_id"]

        for omega in cube_roots_of_unity(p):
            for radius, relation in enumerate_short_relations(params, omega, MAX_RADIUS):
                tested += 1
                m1, r1, k1, r0, k0 = relation
                if m1 == account_id:
                    continue
                if not pass_residue_filters(params, m1, r1, k1):
                    continue
                if not pass_residue_filters(params, account_id, r0, k0):
                    continue

                x1 = (base * m1 + step * r1 + k1) % p
                x0 = (base * account_id + step * r0 + k0) % p
                if (omega * x1 - x0) % p != 0:
                    continue

                yz = usable_y_and_z(x0, b, p)
                if yz is None:
                    continue
                y, z = yz

                sign_resp = client.call(
                    "sign",
                    {"m": m1, "x": x1, "y": y, "r": r1, "k": k1, "z": z},
                )
                if not sign_resp.get("ok"):
                    continue

                token = sign_resp["token"]
                sx = (omega * token["x"]) % p
                sy = token["y"]

                verify_resp = client.call(
                    "verify",
                    {"x": x0, "y": y, "r": r0, "k": k0, "z": z, "sx": sx, "sy": sy},
                )
                if verify_resp.get("ok"):
                    print(verify_resp["flag"])
                    return

        print(f"no relation found after testing {tested} candidates")
    finally:
        client.close()


if __name__ == "__main__":
    main()
