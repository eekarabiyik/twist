# A Classification of Modular Curves
CAUTION! A BUG WAS FOUND IN DECEMBER 2025. PLEASE UPDATE AND REDOWNLOAD THE DATA FILES (VERSION 3 ON ZENODO)!

This repository contains the classification of modular curves upto genus 12 in terms of families. 
Please let me know any if you have any comments or suggestions, or find any bugs: ek693@cornell.edu

All the data is on: https://zenodo.org/records/18159016
Associated preprint: https://eekarabiyik.github.io/files/paper.pdf

## Loading families

From the repository root, initialize the `Modular` submodule for a full installation.

```sh
git submodule update --init -- Modular
```

Extract the version 3 data under `Families/` in the repository root. Each index has its own file, such as `Families/Genus5/Index144.dat` or `Families/Genus0/Index24.dat`. Start Magma from the repository root and pass the `Families` folder to the loader.

```magma
AttachSpec("spec");
FAM := LoadFamiliesGenusIndex("./Families" : genus:=5, index:=144);
#FAM;
```

For a collection split into files by agreeable label, such as `Families/Genus5/Index144/<agreeable_label>`, use `LoadFamilies` with the same folder and arguments. Both loaders are defined in [FindingFamilies/FamilyData/LoadData.m](FindingFamilies/FamilyData/LoadData.m).

A worked example computes a model for a group of index 192 in [FindingFamilies/Example.m](FindingFamilies/Example.m).


The main function is `FindModel` in the file main.m in the folder `FindingFamilies/MainCode`.
It takes an arbitrary subgroup G of GL_2(Z/NZ) with full determinant, its SL2Intersection T and the list of families `FAM` as inputs. In turn, it computes a set of equations for the modular curve, computes its jmap. It also computes whether the curve has Q-gonality 2. Check the function description for mode details.


`ConstructingFamilies.m` contains the functions for computing all the families arising from a Cummins Pauli record, upto a fixed genus.

Some explanations:
- DrewMagma folder contains a non submodule version of Andrew Sutherland's magma functions for GL2. 
- FindingFamilies folder is the main folder for computing models and maps. 
- `FindingFamilies/CummingsPauli` contains the Cummins–Pauli classification of congruence subgroups up to genus 24.
- `FindingFamilies/FamilyData` contains the family record definitions, data loaders, and code for constructing families from the Cummins–Pauli database.
- FamilyFinder folder contains code for, given a group G, finding the family it lies in. This is done first by computing the agreeable closure of the group and then searching that agreeable subgroup in our data.
- MainCode folder contains the main.m. Where everything is put together.


This repo is optimized for computation of modular curves with respect to group theory data coming from LMFDB. This is not necessary, earlier versions was not optimized for this and did not use LMFDB labels nor canonical generators. We believe that modular curves and forms data being collected in LMFDB is a good thing.


- Our implementation is usually faster than other implementations for finding models for modular curves. This is certainly the case when the level of modular curves input gets bigger.
- Improvements will be made. This is a working version as of April 2026.

Eray Karabiyik