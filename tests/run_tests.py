import os
import subprocess
import difflib

def make_cmd(fn):
    cmd = "cd .. && ocaml compiler.ml ./tests/inputs/{0}.scm > ./tests/bin/{0}.s && nasm -f elf64 -o ./tests/bin/{0}.o ./tests/bin/{0}.s && gcc -static -m64 -o ./tests/executables/{0} ./tests/bin/{0}.o".format(fn)
    return cmd

def run_compiler(filename):
	print(filename)
	fname = filename[:-4]
	os.system(make_cmd(fname))
	os.system('./executables/{0} > ./outputs/{0}'.format(fname))

def run_chez(filename):
	print(filename[:-4])
	os.system(f'chezscheme9.5 --quiet < ./inputs/{filename} > ./expected_outputs/{filename[:-4]}')

def compare(filename):
    output_name = filename[:-4]
    with open('./expected_outputs/{}'.format(output_name), 'r') as expected_output:
        with open('./outputs/{}'.format(output_name), 'r') as real_output:
            diff = difflib.unified_diff(
                real_output.readlines(),
                expected_output.readlines(),
                fromfile="real_output",
                tofile='expected_output'
            )
    return diff

if __name__ == "__main__":    
    input_files = os.listdir('./inputs')
    report = {}
    tests_total = 0
    tests_passed = 0
    for test in input_files:
        tests_total += 1
        run_compiler(test)
        run_chez(test)
        line_diff = []
        for line in compare(test):
            line_diff.append(line)
        if line_diff == []:
            report[test] = "passed"
            tests_passed += 1
        else:
            report[test] = "failed: \n" + " ".join(line_diff)
    if tests_passed != tests_total:
        print("passed {}/{} tests".format(tests_passed,tests_total))
        print(report)
    else:
        print("passed all tests!")
