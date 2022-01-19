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

        print("-- Testing program for vulnerability", vuln_name, "--")
        print("-- Checking information flows --\n")

        caught = utils.track_taint(tree, v["sources"], v["sanitizers"], v["sinks"], False)
            
        for sink_name in caught:
            sources = utils.get_source_from_vuln(caught[sink_name])

            for source in sources:    
                is_sanitized = utils.get_is_sanitized_from_vuln(caught[sink_name], source)
                s_flows = utils.get_sanitized_flows_from_vuln(caught[sink_name], source)

                vuln_counts[vuln_name] += 1       
                caughtVuns.append({ "vulnerability": f'{vuln_name}_{vuln_counts[vuln_name]}',
                                    "source":source,
                                    "sink": sink_name, 
                                    "unsanitized flows": "no" if is_sanitized else "yes",
                                    "sanitized flows": s_flows
                                    })

    print("----- Final Results -----")
    print(caughtVuns)

if __name__ == '__main__':
    main()