while read -d '%' input; do
echo "$input" > ./smtwork$$.smt2
z3 ./smtwork$$.smt2
done
rm ./smtwork$$.smt2
