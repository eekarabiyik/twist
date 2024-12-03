# Genus6
This repository contains the classification of modular curves upto genus 6 in terms of families. 

It also contains a set of codes for the computation of models of modular curves upto genus 1. 
The main function is `FindModelNew` in the file main.m in the folder `FindingFamilies/MainCode`. Make sure that your directory is `FindingFamilies/MainCode`.

Some explanations:

- There is now the jmap functionality. Also the code will say whether the curve computed has gonality 2 or not.

- Ignore the folders which are to be ignored.

- FamilyData fodler contains, as data files, the families we have up to genus 1.  Families with models and representatives computed is not here! Because github did not allow!

- FamilyFinder folder contains code for, given a group G, finding the family it lies in. This is done first by computing the agreeable closure of the group and then searching that agreeable subgroup in our data.

- MainCode folder contains the main.m. Where everything is put together.

- RepresentativeFinder folder contains code -written by Zywina- that finds a representative group in a family. It actually can do more than that but that is irrelevant for our purposes.

- TwistingCode contains three important files: GroupToCocyle.m, H90.m, and TwistingCode.m They have enough comments in it to explain what they do. But also, ASK ME!
