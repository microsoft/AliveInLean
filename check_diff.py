#!/usr/bin/python3
import sys

def matches(s1, s2):
	s1 = s1.strip()
	s2 = s2.strip()
	if s1 != "Correct" and s1 != "Incorrect":
		# Unknown output.
		return 0
	if (s1 == "Correct" and s2 == "Optimization is correct!") or \
	   (s1 == "Incorrect" and s2.startswith("ERROR:")):
		# Correct.
		return 1
	# Incorrect!
	return 2

if len(sys.argv) != 3:
	print("check_diff.py <AliveInLean output> <answer>")
	exit(1)

ls1 = open(sys.argv[1]).readlines()
ls2 = open(sys.argv[2]).readlines()
if len(ls1) != len(ls2):
	print("# of total lines of files differ..!")
	print("\t# of lines of " + sys.argv[1] + ": " + str(len(ls1)))
	print("\t# of lines of " + sys.argv[2] + ": " + str(len(ls2)))
	exit(1)

correct = 0
incorrect = 0
strange = 0
for i in range(0, len(ls1)):
	res = matches(ls1[i], ls2[i])
	if res == 0:
		print(str(i+1) + ": Unknown output:")
		print("\t" + ls1[i].strip())
		print("\t" + ls2[i].strip())
		strange = strange + 1
	elif res == 1:
		correct = correct + 1
	elif res == 2:
		print(str(i+1) + ": Incorrect!")
		print("\t" + ls1[i].strip())
		print("\t" + ls2[i].strip())
		incorrect = incorrect + 1

print("Total: " + str(correct) + " corrects, " + str(incorrect) +
	" incorrects, " + str(strange) + " strange outputs")
