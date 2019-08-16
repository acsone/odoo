"""Specialized PEP 517 build backend for Odoo.

It is based on setuptools, and the only thing it does differently from
setuptools is to symlink all addons into odoo/addons before building,
so setuptools discovers them automatically.
"""

import os

from setuptools import build_meta


def _symlink_addons():
    for addon in os.listdir("addons"):
        os.symlink(
            os.path.join("..", "..", "addons", addon),
            os.path.join("odoo", "addons", addon),
        )


def _unsymlink_addons():
    for f in os.listdir(os.path.join("odoo", "addons")):
        f = os.path.join("odoo", "addons", f)
        if os.path.islink(f):
            os.remove(f)


prepare_metadata_for_build_wheel = build_meta.prepare_metadata_for_build_wheel


get_requires_for_build_sdist = build_meta.get_requires_for_build_sdist


def build_sdist(*args, **kwargs):
    try:
        _symlink_addons()
        return build_meta.build_sdist(*args, **kwargs)
    finally:
        _unsymlink_addons()


get_requires_for_build_wheel = build_meta.get_requires_for_build_wheel


def build_wheel(*args, **kwargs):
    try:
        _symlink_addons()
        return build_meta.build_wheel(*args, **kwargs)
    finally:
        _unsymlink_addons()
