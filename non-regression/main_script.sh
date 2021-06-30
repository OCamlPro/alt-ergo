rm -f main_script.log

## Given parameters
################################################################################################

pr=`pwd`/alt-ergo.opt

if [ "$pr" = "" ] ; then
    echo "`basename $0`: No prover is given!"
    exit 1
else if [ ! -f $pr ] ; then
    echo "`basename $0`: Given prover \"$pr\" not found!"
    exit 1
else if [ ! -x "$pr" ] ; then
    echo "$`basename $0`: Given prover \"$pr\" not executable!"
    exit 1
fi
fi
fi

opt=$1
echo "COMMAND: $pr $opt <file>"

## PP options
################################################################################################

cpt=0
COLS=$(tput cols)
limit=""
while [ $cpt -lt $COLS ]; do
    cpt=`expr $cpt + 1`
    limit=`echo -n $limit-`
done

echo -n "$limit"

main_script_out=$(mktemp)
main_script_err=$(mktemp)
trap "rm $main_script_out $main_script_err" EXIT

## Finding files
################################################################################################

files_pat=("-name" "*.ae" "-or" "-name" "*.smt2" "-or" "-name" "*.zip")

## Challenges
################################################################################################

score=0
total=0

big_total=`find challenges "${files_pat[@]}" | wc -l`
for kind in `ls challenges/`
do
    echo ""
    echo -n "challenges/$kind"
    for ae in `find challenges/$kind/ "${files_pat[@]}"`
    do
        tput hpa 25
        total=`expr $total + 1`
        echo -n "$total / $big_total"
        timeout 2 $pr -o native $ae $opt 1> $main_script_out 2> $main_script_err
        if grep -q -w Valid $main_script_out ; then
	    score=`expr $score + 1`
            echo -e "\e[32m    > [OK] ../non-regression/$ae\e[39m"
        else
            echo ../non-regression/$ae >> main_script.log
            cat $main_script_out >> main_script.log
            cat $main_script_err >> main_script.log
            echo "" >> main_script.log
            echo "    > [KO] ../non-regression/$ae"
        fi
    done
done

percent=`expr 100 \* $score / $total`
diff=`expr $total - $score`
echo ""
echo "$limit"
echo " Score Challenges: $score/$total : $percent% (-$diff) "
echo "$limit"


## Valid
################################################################################################

score=0
total=0

big_total=`find valid "${files_pat[@]}" | wc -l`
for kind in `ls valid/`
do
    echo ""
    echo -n "valid/$kind"
    for ae in `find valid/$kind/ "${files_pat[@]}"`
    do
        tput hpa 25
        total=`expr $total + 1`
        echo -n "$total / $big_total"
        timeout 2 $pr -o native $ae $opt 1> $main_script_out 2> $main_script_err
        if grep -q -w Valid $main_script_out ; then
	    score=`expr $score + 1`
        else
            echo ../non-regression/$ae >> main_script.log
            cat $main_script_out >> main_script.log
            cat $main_script_err >> main_script.log
            echo "" >> main_script.log
            echo "    > [KO] ../non-regression/$ae"
        fi
    done
done

percent=`expr 100 \* $score / $total`
diff=`expr $total - $score`
echo ""
echo "$limit"
echo " Score Valid: $score/$total : $percent% (-$diff) "
echo "$limit"


## Invalid
################################################################################################

score=0
total=0

big_total=`find invalid "${files_pat[@]}" | wc -l`
for kind in `ls invalid/`
do
    echo ""
    echo -n "invalid/$kind"
    for ae in `find invalid/$kind/ "${files_pat[@]}"`
    do
        tput hpa 25
        total=`expr $total + 1`
        echo -n "$total / $big_total"
        timeout 2 $pr -o native $ae $opt 1> $main_script_out 2> $main_script_err
        if grep -q -w "I don't know" $main_script_out ; then
	    score=`expr $score + 1`
        else
            echo ../non-regression/$ae >> main_script.log
            cat $main_script_out >> main_script.log
            cat $main_script_err >> main_script.log
            echo "" >> main_script.log
            echo "    > [KO] ../non-regression/$ae"
        fi
    done
done

percent=`expr 100 \* $score / $total`
diff=`expr $total - $score`
echo ""
echo "$limit"
echo " Score Invalid: $score/$total : $percent% (-$diff)"
echo "$limit"


## Incorrect
################################################################################################

score=0
total=0

big_total=`find incorrect "${files_pat[@]}" | wc -l`
for kind in `ls incorrect/`
do
    echo ""
    echo -n "incorrect/$kind"
    for ae in `find incorrect/$kind "${files_pat[@]}"`
    do
        tput hpa 25
        total=`expr $total + 1`
        echo -n "$total / $big_total"
        timeout 2 $pr -o native $ae $opt 1> $main_script_out 2> $main_script_err
        if [ $? -eq 0 ] ; then
            echo ../non-regression/$ae >> main_script.log
            cat $main_script_out >> main_script.log
            cat $main_script_err >> main_script.log
            echo "" >> main_script.log
            echo "    > [KO] ../non-regression/$ae"
        else
            score=`expr $score + 1`
        fi
    done
done

percent=`expr 100 \* $score / $total`
diff=`expr $total - $score`
echo ""
echo "$limit"
echo " Score Incorrect: $score/$total : $percent% (-$diff)"
echo "$limit"
