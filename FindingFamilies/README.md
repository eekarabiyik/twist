# Genus1
This repository contains the classification of modular curves upto genus 1 in terms of families. 

It also contains a set of codes for the computation of models of modular curves upto genus 1. 
The main function is `FindModelNew` in the file main.m in the folder `FindingFamilies/MainCode`. Make sure that your directory is `FindingFamilies/MainCode`.

IMPORTANT!
Apparently the data file is too big so I could not upload it in the original upload. I will figure something out.

Some explanations:

- Ignore the two folders which is to be ignored.

- FindCanonicalModel function needs to be adjusted! I just had a talk with David Zywina and we figured out an issue regarding twisting and the polynomials that is output by FindCanonicalModel. This will be updated soon.

- Folder ConstructingFamilies has the necessary code for, well, constructing the families. I recently added some improvement code to get rid of certain redundant groups, so there are some commented/uncommented parts. ASK ME! 

- CummingsPauli: obvious

- FamilyData fodler contains, as data files, the families we have up to genus 1.  Families with models and representatives computed is not here! Because github did not allow!

- FamilyFinder folder contains code for, given a group G, finding the family it lies in. This is done first by computing the agreeable closure of the group and then searching that agreeable subgroup in our data.

- MainCode folder contains the main.m. Where everything is put together.

- OpenImage David Zywina's code adjusted/changed to a certain degree.

- RepresentativeFinder folder contains code -written by Zywina- that finds a representative group in a family. It actually can do more than that but that is irrelevant for our purposes.

- TwistingCode contains three important files: GroupToCocyle.m, H90.m, and TwistingCode.m They have enough comments in it to explain what they do. But also, ASK ME!
