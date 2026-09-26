from pathlib import Path

from src.lens.loader import load, machine_of
from src.verify.circuit_partition import partition_circuit

root = Path("powdr-dumps/guest-keccak")

for block, step in [
    (2099512, 14),
    (2099512, 15),
    (2106332, 8),
    (2106332, 9),
]:
    paths = [
        p for p in root.glob(f"apc_candidate_{block}_{step:03d}_*.json")
        if ".powdr-opt-" not in p.name
    ]
    assert len(paths) == 1, paths

    data = load(paths[0])
    machine = machine_of(data)
    partition = partition_circuit(data)

    assert partition.algebraic == tuple(machine["constraints"])
    assert partition.derived == tuple(machine.get("derived_columns", []))

    # Reassemble the original bus list by its retained indices.
    combined = sorted(
        partition.stateful + partition.stateless,
        key=lambda item: item.index,
    )
    original = machine.get("bus_interactions", [])

    assert [item.index for item in combined] == list(range(len(original)))
    assert [item.interaction for item in combined] == original
    assert all(
        item.interaction["id"] in {0, 1}
        for item in partition.stateful
    )
    assert all(
        item.interaction["id"] in {2, 3, 6, 7}
        for item in partition.stateless
    )

    print(
        f"{block}/{step:03d}: "
        f"algebraic={len(partition.algebraic)}, "
        f"stateless={len(partition.stateless)}, "
        f"stateful={len(partition.stateful)}, "
        f"derived={len(partition.derived)}"
    )

print("PASS: every constraint and bus interaction was preserved.")

# Equivalent equation in the two dump representations.
machine_dump = {
    "constraints": [["x@0", "-", 1]],
    "bus_interactions": [],
}
constraints_dump = {
    "constraints": [["x@0", "+", 2013265920]],
    "bus_interactions": [],
}

assert partition_circuit(machine_dump).format == "machine"
assert partition_circuit(constraints_dump).format == "constraints"

# Baseline dumps can wrap the circuit under "machine".
wrapped = {"block": {}, "machine": machine_dump}
assert partition_circuit(wrapped).algebraic == (
    ["x@0", "-", 1],
)

# Exercise every supported bus ID, including a repeated interaction.
bus_ids = [0, 1, 2, 3, 6, 7, 1]
sample = {
    "constraints": [0, 0],
    "bus_interactions": [
        {"id": bus_id, "mult": 1, "args": []}
        for bus_id in bus_ids
    ],
}
partition = partition_circuit(sample)

assert [item.index for item in partition.stateful] == [0, 1, 6]
assert [item.index for item in partition.stateless] == [2, 3, 4, 5]
assert partition.algebraic == (0, 0)  # Preserve duplicates and trivial rules.

# Unsupported input must fail explicitly, not disappear or be misclassified.
bad_inputs = [
    [],  # Substitution files are not circuits.
    {"constraints": "not a list"},
    {"constraints": [], "bus_interactions": "not a list"},
    {"constraints": [], "derived_columns": "not a list"},
    {"constraints": [], "bus_interactions": [
        {"id": 99, "mult": 1, "args": []}
    ]},
    {"constraints": [], "bus_interactions": [
        {"id": "symbolic_bus@0", "mult": 1, "args": []}
    ]},
    {"constraints": [], "bus_interactions": [
        {"id": True, "mult": 1, "args": []}
    ]},
]

for data in bad_inputs:
    try:
        partition_circuit(data)
    except ValueError:
        pass
    else:
        raise AssertionError(f"Unsupported input was accepted: {data!r}")

print("PASS: formats, wrapper, bus taxonomy, duplicates, and rejection tests.")