#!/usr/local/bin/python

from __future__ import print_function

import os
import csv

file1 = "generated_data/data.csv"

file2 = "generated_data/data_test.csv"

def findPair(ps, s):
	result = None
	for pair in ps:
		if (pair[0] == s):
			result = pair[1]
	return result

testPairs = []
origPairs = []

fields = None

with open(file2, 'r') as csvfile:
	csvreader = csv.reader(csvfile)
	fields = csvreader.next()
	
	for row in csvreader:
		testPairs.append(row)

with open(file1, 'r') as csvfile:
	csvreader = csv.reader(csvfile)
	fields = csvreader.next()
	
	for row in csvreader:
		origPairs.append(row)

count = 0
increase = 0
for pair in testPairs:
	number = findPair(origPairs, pair[0])
	print(pair[0], pair[1], number)
	increase = increase + (int(pair[1]) - int(number))
	count = count + 1

print("Average increase = " + str(increase/count))


	
		
