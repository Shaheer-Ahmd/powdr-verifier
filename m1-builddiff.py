from pathlib import Path
from src.lens.loader import load, detect_format
from src.lens.diff import build_diff, DiffError

# Small synthetic test: the same equation in two representations.
machine = {"constraints": [["x@0", "-", 1]]}
constraints = {"constraints": [["x@0", "+", 2013265920]]}

assert detect_format(machine) == "machine"
assert detect_format(constraints) == "constraints"

try:
    build_diff(machine, constraints)
except DiffError:
    print("PASS: cross-format comparison remains blocked by default")
else:
    raise AssertionError("Default cross-format guard was lost")

result = build_diff(machine, constraints, allow_cross_format=True)
assert not result.removed and not result.added and not result.changed
assert result.fmt == "machine->constraints"
print("PASS: opt-in recognizes this cross-format canonical match")

root = Path("powdr-dumps/guest-keccak")

def dump(block, step):
    matches = [
        path for path in root.glob(
            f"apc_candidate_{block}_{step:03d}_*.json"
        )
        if ".powdr-opt-" not in path.name
    ]
    assert len(matches) == 1, matches
    return load(matches[0])

for block, before, after, expected_unmatched in [
    (2099512, 14, 15, 0),
    (2106332, 8, 9, 2),
]:
    result = build_diff(
        dump(block, before),
        dump(block, after),
        allow_cross_format=True,
    )

    # Each "changed" pair contains one unmatched After expression.
    unmatched_after = result.added + [
        after_expr for _, after_expr in result.changed
    ]
    print(
        f"removed={len(result.removed)}, "
        f"added={len(result.added)}, "
        f"changed={len(result.changed)}, "
        f"unmatched_after={len(unmatched_after)}"
    )
    assert len(unmatched_after) == expected_unmatched

print("PASS: both algebraic-diff acceptance counts match")
