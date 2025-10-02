# A Classification of Modular Curves

This repository contains the classification of modular curves upto genus 12 in terms of families. 

All the data is on: https://zenodo.org/records/15832985
Download these files. Unpack. Put them all in a folder. Individual files in the folder should have paths similar to: `Families/Genus5/Index144` 
In the file `Main/FindingFamilies/FamilyData/LoadData.m`, the intrinsic `LoadFamiliesGenusIndex`is used for loading the families into a list. 

Example (assuming the data files are put into the folder `Main/Families`):

`FAM:=LoadFamiliesGenusIndex("Main/Families": genus:=5,index:=144);`
`#FAM`
`>2247`

All the families of genus 5 and index 144 are loaded. There are 2247 of them.


- `Example.m` demonstrates an example.


The main function is `FindModel` in the file main.m in the folder `FindingFamilies/MainCode`.
It takes an arbitrary subgroup G of GL_2(Z/NZ) with full determinant, its SL2Intersection T and the list of families `FAM` as inputs. In turn, it computes a set of equations for the modular curve, computes its jmap. It also computes whether the curve has Q-gonality 2. Check the function description for mode details.


`ConstructingFamilies.m` contains the functions for computing all the families arising from a Cummins Pauli record, upto a fixed genus.

Some explanations:
- DrewMagma folder contains a non submodule version of Andrew Sutherland's magma functions for GL2. 
- FindingFamilies folder is the main folder for computing models and maps. 
- CumminsPauli folder contains Cummins-Pauli classification of congruence subgroups up to genus 24. 
- FamilyData folder contains the records for the families we use for our classification. Additionally, it includes a file that computes these families starting from the Cummins-Pauli database.
- FamilyFinder folder contains code for, given a group G, finding the family it lies in. This is done first by computing the agreeable closure of the group and then searching that agreeable subgroup in our data.
- MainCode folder contains the main.m. Where everything is put together.


This repo is optimized for computation of modular curves with respect to group theory data coming from LMFDB. This is not necessary, earlier versions was not optimized for this and did not use LMFDB labels nor canonical generators. We believe that modular curves and forms data being collected in LMFDB is a good thing.


- Our implementation is usually faster than other implementations for finding models for modular curves. This is certainly the case when the level of modular curves input gets bigger.

Eray Karabiyik