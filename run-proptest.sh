if [ "$#" -eq 0 ]; then
	lean --run src/proptest_run.lean arith all 30
	lean --run src/proptest_run.lean bv_equiv all 30
	lean --run src/proptest_run.lean b_equiv all 30
	lean --run src/proptest_run.lean overflow_chk all 30
else
	lean --run src/proptest_run.lean $@
fi
