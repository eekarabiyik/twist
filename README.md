# Genus6
ATTENTION: THIS REPO IS RAPIDLY CHANGING. DO NOT BELIEVE ANYTHING IT SAYS! ONCE EVERYTHING IS IN PLACE THIS SENTENCE WILL BE REMOVED.
This repository contains the classification of modular curves upto genus 6 in terms of families. 

It also contains a set of codes for the computation of models of modular curves upto genus 6. 
The main function is `FindModel` in the file main.m in the folder `FindingFamilies/MainCode`.
It takes an arbitrary subgroup G of GL_2(Z/NZ) with full determinant and its SL2Intersection T as inputs. In turn it computes a set of equations for the modular curve, computes its jmap. It also camputes whether the curve has Q-gonality 2.  Make sure that your directory is `Main`.

Some explanations:

- There is now the jmap functionality. Also the code will say whether the curve computed has QQ-gonality 2 or not. Soon a collection of plane models will be computed by the function and there will be functionality to compute universal elliptic curves.

- `FindingFamilies/Trial/newgenus6trial.m` has an example loop that runs of 200000 curves.

- FamilyData folder contains, as data files, the families we have up to genus 6. 

- FamilyFinder folder contains code for, given a group G, finding the family it lies in. This is done first by computing the agreeable closure of the group and then searching that agreeable subgroup in our data.

- MainCode folder contains the main.m. Where everything is put together.

- TwistingCode contains three important files: Newco.m, H90.m, and TwistingCode.m They have enough comments in it to explain what they do. But also, ASK ME!

Constructing the families:
- There is now a function "FindAllFamilies" that computes the families up to a genus associated to a fixed congruence subgroup.
- With the recent updates, the code is now much faster. Some data for fine families and universal elliptic curves has been added. A final functionality of computing Universal Elliptic Curves will be added. 

New Notes: We are adding so much more! There will be relative jmap functionalities, a skeleton of relative jmaps so that one can compose them to get the Absolute Jmap. LMFDB labels of families will be added. This is constantly changing! 

- It is posible that when you input certain groups, it will take much more than expected for the function to terminate. This is because for certain families the Absolute Jmaps are terribly large. When we replace the absolute ones with the relative Jmaps, this issue will be resolved. But for most of the curves, our function is already quite fast! 

- Do not believe the output when your input is a genus 0 modular curve! There is a small bug but to fix it I need to recompute everything so it will some time to fix it.