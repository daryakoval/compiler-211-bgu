import os
import sys

def clean_bin():
    os.system('rm ./bin/*')

def clean_executables():
    os.system('rm ./executables/*')

def clean_outputs():
    os.system('rm ./outputs/*')

def clean_expected_outputs():
    os.system('rm ./expected_outputs/*')

if __name__ == "__main__":    
    args = sys.argv
    if '-a' in args or '-all' in args:
        clean_bin()
        clean_executables()
        clean_outputs()
        clean_expected_outputs()
    if '-b' in args or '-bin' in args:
        clean_bin()
    if '-o' in args or '-outputs' in args:
        clean_outputs()
    if '-eo' in args or '--expected-outputs' in args:
        clean_expected_outputs()
    if '-ex' in args or '-executables' in args:
        clean_executables()