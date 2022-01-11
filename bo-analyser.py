import argparse
import ast
import json

import utils

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('program', help="Which program should be analyzed?")
    parser.add_argument('patterns', help="Which patterns should be searched for?")
    
    parsed = parser.parse_args()
    
    # Parse the program to an AST
    tree = json.loads(open(parsed.program).read())
    
    # Get a list of dictionaries with each vulnerability
    vulnerability = json.load(open(parsed.patterns))
    
    caughtVuns = []
    
    # For each vulnerability, mark each field of the AST based on if they are a sink, sanitizer or source
    # Then go through the AST to check what flows happen
    for v in vulnerability:
        print("Testing program for vulnerability",v['vulnerability'])
        
        print("Checking information flows")
        
        caught = utils.track_taint(tree, v["sources"], v["sanitizers"], v["sinks"])
        if len(caught) != 0:
            print(caught)
            for vuln in caught:
                source, sink, sanit = vuln
                
                if sanit:
                    caughtVuns.append({"vulnerability":v["vulnerability"], "source":source, "sink":sink, 
                                    "unsanitized flows": "no", "sanitized flows":[]})
                else:
                    caughtVuns.append({"vulnerability":v["vulnerability"], "source":source, "sink":sink, 
                                    "unsanitized flows": "yes", "sanitized flows":[]})
            
    print(caughtVuns)

if __name__ == '__main__':
    main()