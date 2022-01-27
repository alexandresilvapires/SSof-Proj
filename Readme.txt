---
Static Analysis Tool for vulnerability detection.

Made by:
João Fonseca nº92497
Alexandre Pires nº92414
Diogo Fouto nº93705 

---

Usage:

The tool can be used by executing bo-analyser.py using python3, and specifying path to the .json slice that you want to verify, 
followed by the path to the .json containing the patterns to be searched for.

Example usage:
python3 bo-analyser.py 5b-loops-unfolding.py.json 5b-patterns.json

---

Necessary modules:

Our tool needs the following python modules to be able to run:
'json', 'copy' and 'argparse' 

---

Tool organization:

The tool contains two utility modules containing methods used to aid the static analysis.
- ast_utils.py: contains methods that regard the manipulation of the json ast structure;
- utils.py: contains methods that regard the tracking of the tainted variables and sinks.