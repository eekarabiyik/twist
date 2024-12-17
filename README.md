# Genus6
This repository contains the classification of modular curves upto genus 6 in terms of families. 

It also contains a set of codes for the computation of models of modular curves upto genus 6. 
The main function is `FindModel` in the file main.m in the folder `FindingFamilies/MainCode`. Make sure that your directory is `FindingFamilies/MainCode`.

Some explanations:

- There is now the jmap functionality. Also the code will say whether the curve computed has QQ-gonality 2 or not.

- Ignore the trial folder.

- FamilyData folder contains, as data files, the families we have up to genus 6. 

- FamilyFinder folder contains code for, given a group G, finding the family it lies in. This is done first by computing the agreeable closure of the group and then searching that agreeable subgroup in our data.

- MainCode folder contains the main.m. Where everything is put together.

- TwistingCode contains three important files: Newco.m, H90.m, and TwistingCode.m They have enough comments in it to explain what they do. But also, ASK ME!

Constructing the families:
- If you would like to construct all the families from the beginning using the Cummins-Pauli database then go to the file FindingFamilies/FamilyData/ConstructingFamilies.m. This contains all the necessary steps. You need to edit the code to change the genus bound for calculation. 
