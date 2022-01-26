import argparse
import json
from ast_utils import getAllTrees, getLines
import copy
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
    
    allTrees = getAllTrees(tree)

    # For each vulnerability, mark each field of the AST based on if they are a sink, sanitizer or source
    # Then go through the AST to check what flows happen
    for v in vulnerability:
        vuln_name = v["vulnerability"]
        vuln_counts[vuln_name] = 0

        print("-- Testing program for vulnerability", vuln_name, "--")
        print("-- Checking information flows --\n")

        caught = {}
        for t in allTrees:
            caught_this_time = utils.track_taint(t, v["sources"], v["sanitizers"], v["sinks"], v["implicit"] == "yes")
            
            print("currently caught:", caught)
            print("caught this time:",caught_this_time)
            for sink in caught_this_time:
                print("checking sink",sink)
                if sink in caught:
                    for source in caught_this_time[sink]["source"]:
                        if source in caught[sink]["source"]:
                            if caught_this_time[sink]["source"][source] not in [caught[sink]["source"][source]] and caught_this_time[sink]["source"][source] != []:
                                caught[sink]["source"][source].extend(caught_this_time[sink]["source"][source])
                        else:
                            caught[sink]["source"][source] = copy.deepcopy(caught_this_time[sink]["source"][source])
                else:
                    caught.update({sink: copy.deepcopy(caught_this_time[sink])})

        for sink in caught:
            sources = caught[sink]["source"]
            is_sanitized = caught[sink]["is_sanitized"]

            for source in sources:
                s_flows = sources[source]
                vuln_counts[vuln_name] += 1
                
                #TODO: Fix, Nasty
                if(s_flows == [[]]):
                    s_flows = []
                elif(s_flows != []):
                    s_flows = [s_flows]

                if(is_sanitized and s_flows == []):
                    is_sanitized = False

                if is_sanitized:
                    caughtVuns.append({"vulnerability":f'{vuln_name}_{vuln_counts[vuln_name]}', "source":source, "sink":sink, 
                                    "unsanitized flows": "no", "sanitized flows": s_flows})
                else:
                    caughtVuns.append({"vulnerability":f'{vuln_name}_{vuln_counts[vuln_name]}', "source":source, "sink":sink, 
                                    "unsanitized flows": "yes", "sanitized flows": s_flows})

    print("----- Final Results -----")
    for vuln in caughtVuns:
        print(vuln)

if __name__ == '__main__':
    main()