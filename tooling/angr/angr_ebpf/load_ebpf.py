import logging

from cle.backends import ELF, register_backend
from .arch_ebpf import ArchExtendedBPF

l = logging.getLogger(__name__)

class ExtendedBPF(ELF):
    """Mark extended BPF as loadable via ELF"""

    is_default = False

    def __init__(self, *args, **kwargs):
        kwargs.setdefault("arch", ArchExtendedBPF("Iend_LE"))
        super().__init__(*args, **kwargs)
        self.os = "UNIX - System V"

register_backend("UNIX - System V", ExtendedBPF)
