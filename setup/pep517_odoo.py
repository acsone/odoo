"""Specialized PEP 517 build backend for Odoo.

It is based on setuptools, and the only thing it does differently from
setuptools is to symlink all addons into odoo/addons before building,
so setuptools discovers them automatically.
"""
import contextlib
from pathlib import Path

from setuptools import build_meta
from setuptools.build_meta import *


@contextlib.contextmanager
def _symlink_addons():
    symlinks = []
    try:
        target_addons_path = Path("addons")
        addons_path = Path("odoo") / "addons"
        link_target = Path("..") / ".." / "addons"
        if target_addons_path.is_dir():
            for target_addon_path in target_addons_path.iterdir():
                if not target_addon_path.is_dir():
                    continue
                addon_path = addons_path / target_addon_path.name
                if not addon_path.is_symlink():
                    addon_path.symlink_to(
                        link_target / target_addon_path.name, target_is_directory=True
                    )
                symlinks.append(addon_path)
        yield
    finally:
        for symlink in symlinks:
            symlink.unlink()


def build_sdist(*args, **kwargs):
    with _symlink_addons():
        return build_meta.build_sdist(*args, **kwargs)


def build_wheel(*args, **kwargs):
    with _symlink_addons():
        return build_meta.build_wheel(*args, **kwargs)
