for i in "inputs/alive/instcombine" "inputs/alive/unit"; do
	echo "Running ${i}/*.opt .."
	find ${i} -name "opt*" -print0 | sort -z | xargs --null cat > ${i}/all.opt
	lean -q --run src/main.lean -verifyopt ${i}/all.opt > output.txt
	python3 check_diff.py output.txt ${i}/answ.txt
	rm ${i}/all.opt
	echo
done
echo "NOTE: running inputs/alive/unit/all.opt should have two incorrect results because Alive does type checking on input which will fail but AliveInLean does not do type checking so it will say it's okay."
