#!/usr/bin/python
import sys
import os

#usage: python anfToanf2cnf boop.anf boopB.anf

inFilename = sys.argv[1]
outFilename = sys.argv[2]
inFile = open(inFilename, "r")
outFile = open(outFilename, "w")

varNum = 1
varDict = {}

for polynomial in inFile:
  monomials = polynomial.strip().split('+')
  line = ""
  for monomial in monomials:
    if not monomial == "1":
      variables = monomial.strip().split('*')
      for variable in variables:
        if not varDict.has_key(variable):
          varDict[variable] = str(varNum)
          varNum += 1
        line += varDict[variable] + ","
    line += "|"
  if line[0] == "|":
    line = line[1:] + "|"
  outFile.write(line + "\n")

inFile.close()
outFile.close()
