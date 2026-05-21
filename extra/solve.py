from itertools import product
import json
from pwn import remote, context
from fpylll import CVP, GSO, IntegerMatrix, LLL, FPLLL
from sage.all import GF


HOST = "127.0.0.1"
PORT = 1344

context.log_level = "error"

Q_BITS = 96
H_BITS = 72
RADIUS = 4

FPLLL.set_precision(300)


def call(io, cmd, payload=None):
    if payload is None:
        line = cmd
    else:
        line = cmd + " " + json.dumps(payload, separators=(",", ":"))
    io.sendline(line.encode())
    data = io.recvuntil(b"> ", drop=True).strip()
    return json.loads(data.splitlines()[-1].decode())


def roots_of_unity(F):
    w = (-1 + F(-3).sqrt()) / 2
    return [int(w), int(w**2)]


def is_square(F, x):
    return F(x).is_square()


def sqrt_or_none(F, x):
    x = F(x)
    if not x.is_square():
        return None
    return int(x.sqrt())


def pass_filters(F, filters, m, r, k):
    for am, ar, ak, c in filters:
        if not is_square(F, am * m + ar * r + ak * k + c):
            return False
    return True


def rowsum(B, coeff):
    return [
        sum(int(coeff[i]) * int(B[i, j]) for i in range(B.nrows))
        for j in range(B.ncols)
    ]


def shells(n, radius):
    for r in range(radius + 1):
        for v in product(range(-r, r + 1), repeat=n):
            if max(map(abs, v)) == r:
                yield v


def build_lattice(params, omega):
    p = params["p"]
    base = params["base"]
    step = params["step"]
    account_id = params["account_id"]
    item_limit = params["item_limit"]
    limb_bound = params["limb_bound"]

    centers = [
        item_limit // 2,
        limb_bound // 2,
        limb_bound // 2,
        limb_bound // 2,
        limb_bound // 2,
    ]

    bounds = [
        item_limit,
        limb_bound,
        limb_bound,
        limb_bound,
        limb_bound,
    ]

    coeffs = [
        omega * base % p,
        omega * step % p,
        omega % p,
        -step % p,
        -1 % p,
    ]

    constant = (
        omega * (base * centers[0] + step * centers[1] + centers[2])
        - (base * account_id + step * centers[3] + centers[4])
    ) % p

    q = 1 << Q_BITS
    h = 1 << H_BITS
    scales = [max(1, q // (b // 2)) for b in bounds]

    basis = []
    for i, c in enumerate(coeffs):
        row = [0] * 6
        row[i] = scales[i]
        row[5] = c * h
        basis.append(row)

    basis.append([0, 0, 0, 0, 0, p * h])

    B = IntegerMatrix.from_matrix(basis)
    LLL.reduction(B)

    target = [0, 0, 0, 0, 0, -constant * h]
    return B, target, centers, bounds, scales, coeffs, constant, h


def decode(v, target, centers, bounds, scales, coeffs, constant, h, p):
    diff = [int(v[i]) - target[i] for i in range(6)]

    for d in (diff, [-x for x in diff]):
        if d[5] % h != 0:
            continue

        shifts = []
        ok = True

        for i in range(5):
            if d[i] % scales[i] != 0:
                ok = False
            shifts.append(d[i] // scales[i])

        if not ok:
            continue
        if any(abs(shifts[i]) > bounds[i] // 2 for i in range(5)):
            continue
        if (constant + sum(coeffs[i] * shifts[i] for i in range(5))) % p != 0:
            continue

        values = tuple(centers[i] + shifts[i] for i in range(5))
        if all(0 <= values[i] < bounds[i] for i in range(5)):
            yield values


def relations(params, omega):
    p = params["p"]
    B, target, centers, bounds, scales, coeffs, constant, h = build_lattice(params, omega)

    seen = set()

    v = CVP.closest_vector(B, target)
    for rel in decode(v, target, centers, bounds, scales, coeffs, constant, h, p):
        seen.add(rel)
        yield rel

    G = GSO.Mat(B, float_type="mpfr")
    G.update_gso()
    z = list(G.babai(target))

    for off in shells(B.nrows, RADIUS):
        coeff = [z[i] + off[i] for i in range(B.nrows)]
        v = rowsum(B, coeff)

        for rel in decode(v, target, centers, bounds, scales, coeffs, constant, h, p):
            if rel not in seen:
                seen.add(rel)
                yield rel


def usable_yz(F, x, b):
    rhs = x**3 + b
    y = sqrt_or_none(F, rhs)
    if y is None:
        return None

    z = sqrt_or_none(F, y)
    if z is not None:
        return y, z

    z = sqrt_or_none(F, -y)
    if z is not None:
        return (-y) % int(F.characteristic()), z

    return None


def main():
    io = remote(HOST, PORT)
    io.recvuntil(b"> ")

    params = call(io, "params")

    p = params["p"]
    b = params["b"]
    base = params["base"]
    step = params["step"]
    account_id = params["account_id"]
    filters = params["residue_filters"]

    F = GF(p)

    for omega in roots_of_unity(F):
        for m1, r1, k1, r0, k0 in relations(params, omega):
            if m1 == account_id:
                continue
            if not pass_filters(F, filters, m1, r1, k1):
                continue
            if not pass_filters(F, filters, account_id, r0, k0):
                continue

            x1 = (base * m1 + step * r1 + k1) % p
            x0 = (base * account_id + step * r0 + k0) % p

            if (omega * x1 - x0) % p != 0:
                continue

            yz = usable_yz(F, x0, b)
            if yz is None:
                continue

            y, z = yz

            sig = call(io, "sign", {
                "m": m1,
                "x": x1,
                "y": y,
                "r": r1,
                "k": k1,
                "z": z,
            })

            if not sig.get("ok"):
                continue

            token = sig["token"]

            res = call(io, "verify", {
                "x": x0,
                "y": y,
                "r": r0,
                "k": k0,
                "z": z,
                "sx": omega * token["x"] % p,
                "sy": token["y"],
            })

            if res.get("ok"):
                print(res["flag"])
                io.sendline(b"exit")
                io.close()
                return

    print("not found")
    io.sendline(b"exit")
    io.close()


main()