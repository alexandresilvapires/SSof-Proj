import argparse
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
    vuln_counts = {}
    
    # For each vulnerability, mark each field of the AST based on if they are a sink, sanitizer or source
    # Then go through the AST to check what flows happen
    for v in vulnerability:
        vuln_name = v["vulnerability"]
        vuln_counts[vuln_name] = 0

        print("Testing program for vulnerability", vuln_name)
        print("Checking information flows")

        caught = utils.track_taint(tree, v["sources"], v["sanitizers"], v["sinks"], v["implicit"] == "yes")
            
        for vuln in caught:
            sources, sink, is_sanitized, s_flows = vuln

            for source in sources:    
                vuln_counts[vuln_name] += 1       
                if is_sanitized:
                    caughtVuns.append({"vulnerability":f'{vuln_name}_{vuln_counts[vuln_name]}', "source":source, "sink":sink, 
                                    "unsanitized flows": "no", "sanitized flows": s_flows})
                else:
                    caughtVuns.append({"vulnerability":f'{vuln_name}_{vuln_counts[vuln_name]}', "source":source, "sink":sink, 
                                    "unsanitized flows": "yes", "sanitized flows": s_flows})

    print("----- Final Results -----")
    print(caughtVuns)

if __name__ == '__main__':
    main()