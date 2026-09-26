"""Structural partition of supported OpenVM circuit dumps.

No equivalence claim, simplification, or variable mapping is performed here.
"""

from dataclasses import dataclass
from typing import Any

# from ..lens.loader import detect_format, machine_of
from src.lens.loader import detect_format, machine_of

# OpenVM IDs from src/bus_interactions/__init__.py.
STATEFUL_BUS_IDS = frozenset({0, 1})
STATELESS_BUS_IDS = frozenset({2, 3, 6, 7})


@dataclass(frozen=True)
class IndexedBus:
    index: int
    interaction: dict[str, Any]


@dataclass(frozen=True)
class CircuitPartition:
    format: str
    algebraic: tuple[Any, ...]
    stateless: tuple[IndexedBus, ...]
    stateful: tuple[IndexedBus, ...]
    derived: tuple[Any, ...]


def partition_circuit(data: Any) -> CircuitPartition:
    if not isinstance(data, dict):
        raise ValueError("Expected a circuit object")

    machine = machine_of(data)
    if not isinstance(machine, dict):
        raise ValueError("Expected a machine object")

    constraints = machine.get("constraints")
    buses = machine.get("bus_interactions", [])
    derived = machine.get("derived_columns", [])

    if not isinstance(constraints, list):
        raise ValueError("Expected a constraints list")
    if not isinstance(buses, list):
        raise ValueError("Expected a bus_interactions list")
    if not isinstance(derived, list):
        raise ValueError("Expected a derived_columns list")

    # detect_format inspects bus records, so validate their shape first.
    for index, interaction in enumerate(buses):
        if not isinstance(interaction, dict):
            raise ValueError(f"Bus interaction {index} is not an object")
        if not isinstance(interaction.get("args", []), list):
            raise ValueError(
                f"Bus interaction {index} must have an args list"
            )

    fmt = detect_format(data)
    if fmt not in {"machine", "constraints"}:
        raise ValueError(f"Unsupported circuit format: {fmt}")


    stateless = []
    stateful = []

    for index, interaction in enumerate(buses):
        if not isinstance(interaction, dict):
            raise ValueError(f"Bus interaction {index} is not an object")

        bus_id = interaction.get("id")

        # Do not silently classify unknown or symbolic IDs as stateless.
        if type(bus_id) is not int:
            raise ValueError(
                f"Bus interaction {index} has unsupported ID: {bus_id!r}"
            )

        item = IndexedBus(index, interaction)
        if bus_id in STATEFUL_BUS_IDS:
            stateful.append(item)
        elif bus_id in STATELESS_BUS_IDS:
            stateless.append(item)
        else:
            raise ValueError(
                f"Bus interaction {index} has unknown OpenVM ID: {bus_id}"
            )

    return CircuitPartition(
        format=fmt,
        algebraic=tuple(constraints),
        stateless=tuple(stateless),
        stateful=tuple(stateful),
        derived=tuple(derived),
    )
