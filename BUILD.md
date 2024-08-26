# Building PolyHorn
This document is intended as a knowledge base for future additions requiring a new build. 

## Step 1: Install build tools
```bash
pip install --upgrade setuptools wheel build twine
```

## Step 2: Update version number
Update the version number in `pyproject.toml` to reflect the new version. This is important for PyPi to recognize the new version and for pip to update the package.

## Step 3: Build the package
```bash
python -m build
```

## Step 4: Upload the package
```bash
twine upload dist/*
```

## Useful resources:
- [Tutorial for creating a Python package](https://packaging.python.org/tutorials/packaging-projects/)
- [Setuptools specific guide](https://setuptools.pypa.io/en/latest/userguide/dependency_management.html)
