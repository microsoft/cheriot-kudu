"""Hardware build identities and naming for separate VCS coverage databases."""

from pathlib import Path


BUILDS = {
    "cheriot": {"simv": "simv", "vdb": "simv.vdb"},
    "rv32": {"simv": "simv32", "vdb": "simv32.vdb"},
}


def build_cov_dir(base, build):
    """Partition by CHERIoTEn, never by the runtime PMODE setting."""
    if build not in BUILDS:
        raise ValueError("hardware build must be cheriot or rv32")
    base = Path(base)
    name = base.name
    if name.endswith(".vdb"):
        name = name[:-4]
    return base.with_name("{}_{}.vdb".format(name, build))
