#!/usr/bin/env python2

import argparse
import collections
import errno
import glob
import logging
import os
import re
import string
import subprocess
import shutil

def process(fn):
    shutil.copyfile(fn, fn+"~")
    src = open(fn+"~", "r")
    dst = open(fn, "w")
    in_proof = False
    for ln in src:
        if in_proof:
            if re.match("Qed.|Admitted.", ln):
                in_proof = False
                dst.write(ln+" *) ")
            else:
                dst.write(ln)
        else:
            if re.match("Proof.", ln):
                in_proof = True
                dst.write("Admitted. (* " + ln)
            else:
                dst.write(ln)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Comment out Coq proofs for faster compilation.')
    parser.add_argument("files", nargs='+')
    x = parser.parse_args()
    for fn in x.files:
        process(fn)

