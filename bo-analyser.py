import argparse
import ast
import json

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('program', help="Which program should be analyzed?")
    parser.add_argument('patterns', help="Which patterns should be searched for?")
    
    parsed = parser.parse_args()
    
    # Parse the program to an AST
    a = ast.literal_eval(open(parsed.program).read())
    print(a)
    tree = ast.parse(open(parsed.program).read())
    print(tree)
    #for node in ast.walk(tree):
    #    print(node)
    
    # Get a list of dictionaries with each vulnerability
    vulnerability = json.load(open(parsed.patterns))
    
    # For each vulnerability, mark each field of the AST based on if they are a sink, sanitizer or source
    # Then go through the AST to check what flows happen
    for v in vulnerability:
        print("Testing program for vulnerability",v['vulnerability'])
        print("Creating decorated program AST")
        
        #TODO: Make decorated AST with vuln info
        
        print("Checking information flows")
        
        #TODO cenas de ver os flows

if __name__ == '__main__':
    main()