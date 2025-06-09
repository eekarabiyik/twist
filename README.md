# A Classification of Modular Curves
ATTENTION: THIS REPO IS RAPIDLY CHANGING. DO NOT BELIEVE ANYTHING IT SAYS! ONCE EVERYTHING IS IN PLACE THIS SENTENCE WILL BE REMOVED.
This repository contains the classification of modular curves upto genus 24 in terms of families. 

It also contains a set of codes for the computation of models of modular curves upto genus 24. 
The main function is `FindModel` in the file main.m in the folder `FindingFamilies/MainCode`.
It takes an arbitrary subgroup G of GL_2(Z/NZ) with full determinant, its SL2Intersection T and the list of families `FAM` as inputs. In turn it computes a set of equations for the modular curve, computes its jmap. It also camputes whether the curve has Q-gonality 2.

Some explanations:
- DrewMagma folder contains a non submodule version of Andrew Sutherland's magma functions for GL2. 
- FindingFamilies folder is the main folder for computing models and maps. 
- CumminsPauli folder contains Cummins-Pauli classification of congruence subgroups up to genus 24. 
- FamilyData folder contains the records for the families we use for our classification. Additionall it includes a file that computes these families starting from the Cummins-Pauli database.
- FamilyDataFiles contains the families as data files.
- FamilyFinder folder contains code for, given a group G, finding the family it lies in. This is done first by computing the agreeable closure of the group and then searching that agreeable subgroup in our data.
- MainCode folder contains the main.m. Where everything is put together.

- TwistingCode contains some important files: GroupToCocycle.m, H90.m, PolynomialTwister.m and TwistingCode.m They have enough comments in it to explain what they do. But also, ASK ME!

This repo is optimized for computation of modular curves with respect to group theory data coming from LMFDB. This is not necessary, earlier versions was not optimized for this and did not use LMFDB labels nor canonical generators. We believe that modular curves and forms data being collected in LMFDB is a good thing.


- Do not believe the output when your input is a genus 0 modular curve! There is a small bug but to fix it I need to recompute everything so it will some time to fix it. This is still the case but will be fixed.

- Our implementation is usually faster than other implementations for finding models for modular curves. This is certainly the case when the level of modular curves input gets bigger and bigger.

- `Trial/Trial.m` demonstrates over all genus 1 modular curves whose level us at most 70. Once other computations are done, this will be increased to genus up to 24.

Eray Karabiyik