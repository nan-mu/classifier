"""The Heimdall architecture and lifter from the original task evidence."""

from .arch_ebpf import ArchExtendedBPF
from .lift_ebpf import LifterEbpf

REVISION = "90b4605e1c6ddae7ae5ead9738d5c1ff8e2843ad"

__all__ = ["ArchExtendedBPF", "LifterEbpf", "REVISION"]
