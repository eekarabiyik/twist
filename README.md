# Genus6
This repository contains the classification of modular curves upto genus 6 in terms of families. 

It also contains a set of codes for the computation of models of modular curves upto genus 6. 
The main function is `FindModel` in the file main.m in the folder `FindingFamilies/MainCode`.
It takes an arbitrary subgroup G of GL_2(Z/NZ) with full determinant and its SL2Intersection T as inputs. In turn it computes a set of equations for the modular curve, computes its jmap. It also camputes whether the curve has Q-gonality 2.  Make sure that your directory is `FindingFamilies/MainCode`.

Some explanations:

- There is now the jmap functionality. Also the code will say whether the curve computed has QQ-gonality 2 or not. Soon a collection of plane models will be computed by the function and there will be functionality to compute universal elliptic curves.

- Ignore the trial folder.

- FamilyData folder contains, as data files, the families we have up to genus 6. 

- FamilyFinder folder contains code for, given a group G, finding the family it lies in. This is done first by computing the agreeable closure of the group and then searching that agreeable subgroup in our data.

- MainCode folder contains the main.m. Where everything is put together.

- TwistingCode contains three important files: Newco.m, H90.m, and TwistingCode.m They have enough comments in it to explain what they do. But also, ASK ME!

Constructing the families:
- There is now a function "FindAllFamilies" that computes the families up to a genus associated to a fixed congruence subgroup.
- With the recent updates, the code is now much faster. Some data for fine families and universal elliptic curves has been added. A final functionality of computing Universal Elliptic Curves will be added. 