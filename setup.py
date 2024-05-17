#!/usr/bin/env python3

from setuptools import setup, find_packages  # type: ignore
import pypmt


# setup.py
setup(
    name="pyPMT",
    version=pypmt.__version__,
    description="TODO",
    author="TODO",
    author_email="TODO@email.com",
    packages=find_packages(),
    install_requires=[ "z3-solver", "unified-planning", "up-pyperplan", "networkx", "pytest", "numpy"],
    include_package_data=True,
    py_modules=["pyPMT"],
    entry_points={
        "console_scripts": [
            "pypmtcli = pypmt.pypmtcli:main",
        ],
    },
)
